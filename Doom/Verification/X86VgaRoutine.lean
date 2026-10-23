import Doom.Verification.X86WordFillRoutine
/-! Opt-in observational VGA bus. This is NOT a planar renderer. Every accepted
port/aperture transaction may change all device state and yield ANY byte. The
caller quantifies over Environment. Ordinary RAM is not part of Device. Admission
requires explicit I/O permission and a mapped A0000..AFFFF device window. Unknown
ports, unmapped aperture, RAM byte copies, and unsupported opcodes fail closed.
Old interpreters are unchanged; a prior flat prefix is a separate trust boundary.
-/
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace Doom.Verification.X86VgaRoutine
open X86 X86Memory X86Control X86Block
abbrev Byte := BitVec 8
abbrev Port := BitVec 16
structure Device where
  ports : Port → Byte
  planes : Fin 4 → BitVec 16 → Byte
  latches : Fin 4 → Byte
inductive Event where
  | input (port : Port)
  | output (port : Port) (value : Byte)
  | read (address : Word)
  | write (address : Word) (value : Byte)
  deriving DecidableEq
structure Observation where
  event : Event
  value : Byte
/-- An arbitrary total response strategy; no VGA value, write mode, or latch
content is assumed. Quantification over this parameter covers all such choices.
No timing, faults, concurrency, or DMA is asserted to be modeled. -/
abbrev Environment := List Observation → Device → Event → Device × Byte
structure State where
  cpu : X86Control.State
  device : Device
  trace : List Observation := []
  ioAllowed : Bool
  apertureMapped : Bool
inductive Op where
  | immediate (dst : Reg) (value : Word)
  | byteImmediate (dst : Reg) (value : Byte)
  | add (dst : Reg) (value : Word)
  | sub (dst src : Reg)
  | xor (dst src : Reg)
  | orByte (dst : Reg) (value : Byte)
  | andByte (dst : Reg) (value : Byte)
  | compare (dst : Reg) (value : Word)
  | less (offset : Int)
  | loadWord (dst : Reg) (address : Word)
  | loadByte (dst : Reg) (address : Address)
  | storeByte (address : Address) (src : Reg)
  | input
  | output
  | pop (dst : Reg)
  | ret
  deriving DecidableEq

def aperture (a : Word) : Bool := 0xa0000 ≤ a.toNat && a.toNat < 0xb0000
def ramWord (a : Word) : Bool := !(aperture a || aperture (a+1) || aperture (a+2) || aperture (a+3))
def knownPort (p : Port) : Bool := p==0x3c4 || p==0x3c5 || p==0x3ce || p==0x3cf
def port (s : State) : Port := (s.cpu.core.regs 2).extractLsb' 0 16

def touch (env : Environment) (event : Event) (s : State) : State × Byte :=
  let response := env s.trace s.device event
  ({s with device:=response.1,trace:=⟨event,response.2⟩::s.trace},response.2)

def oldOp : Op → X86Routine.Op
  | .immediate r v => .immediate r v
  | .byteImmediate _ _ => .immediate 0 0 -- handled separately, never executed
  | .add r v => .addImmediate r v
  | .sub r t => .subRegistersWithFlags r t
  | .xor r t => .xorRegister r t
  | .orByte r v => .orByteImmediate r v
  | .andByte r v => .andByteImmediate r v
  | .compare r v => .compareRegister r v
  | .less d => .jumpSigned 3 d
  | .loadWord r a => .control (.block (.load r ⟨none,none,0,a⟩))
  | .pop r => .pop r
  | .ret => .ret
  | _ => .immediate 0 0 -- all device operations handled separately

def guard (op : Op) (s : State) : Bool := match op with
  | .input | .output => s.ioAllowed && knownPort (port s)
  | .loadByte _ a | .storeByte a _ => s.apertureMapped && aperture (a.eval s.cpu.core.regs)
  | .loadWord _ a => ramWord a
  | .pop _ | .ret => ramWord (s.cpu.core.regs 4)
  | _ => true

def execute (env : Environment) (op : Op) (s : State) : Option State :=
  if guard op s then match op with
    | .byteImmediate r v => some {s with cpu:={s.cpu with core:=putByte s.cpu.core r v}}
    | .input =>
        let response := touch env (.input (port s)) s
        some {response.1 with cpu:={s.cpu with core:=putByte s.cpu.core 0 response.2}}
    | .output => some (touch env (.output (port s) (readByte s.cpu.core.regs 0)) s).1
    | .loadByte r a =>
        let response := touch env (.read (a.eval s.cpu.core.regs)) s
        some {response.1 with cpu:={s.cpu with core:=putByte s.cpu.core r response.2}}
    | .storeByte a r => some (touch env (.write (a.eval s.cpu.core.regs) (readByte s.cpu.core.regs r)) s).1
    | _ => (X86Routine.execute (oldOp op) s.cpu).map fun cpu => {s with cpu}
  else none

def convert : X86Routine.Op → Option Op
  | .immediate r v => some (.immediate r v)
  | .addImmediate r v => some (.add r v)
  | .subRegistersWithFlags r t => some (.sub r t)
  | .control (.block (.arithmetic (.sub r t))) => some (.sub r t)
  | .xorRegister r t => some (.xor r t)
  | .orByteImmediate r v => some (.orByte r v)
  | .andByteImmediate r v => some (.andByte r v)
  | .compareRegister r v => some (.compare r v)
  | .jumpSigned 3 d => some (.less d)
  | .control (.loadByte r a) => some (.loadByte r a)
  | .storeByte a r => some (.storeByte a r)
  | .pop r => some (.pop r)
  | .ret => some .ret
  | _ => none

def decode (bytes : List UInt8) : Option (Op × List UInt8) := match bytes with
  | 0xee::tail => some (.output,tail)
  | 0xec::tail => some (.input,tail)
  | 0x0c::v::tail => some (.orByte 0 v.toBitVec,tail)
  | 0xa1::tail => do
      let (a,rest) ← X86Block.word tail
      pure (.loadWord 0 a,rest)
  | b::v::tail =>
      if 0xb0≤b.toNat ∧ b.toNat<0xb8 then some (.byteImmediate (Fin.ofNat 8 (b.toNat-0xb0)) v.toBitVec,tail)
      else do
        let (op,rest) ← X86Routine.decode bytes
        let op ← convert op
        pure (op,rest)
  | _ => do
      let (op,rest) ← X86Routine.decode bytes
      let op ← convert op
      pure (op,rest)
def decodeAt (bytes : List UInt8) (pc : Nat) : Option (Op × Nat) :=
  (decode (bytes.drop pc)).map fun (op,rest)=>(op,(bytes.drop pc).length-rest.length)
abbrev Program := Nat → Option (Op × Nat)
inductive Prefix (env : Environment) (program : Program) : Nat → State → State → Prop
  | nil (s) : Prefix env program 0 s s
  | step {n s middle last op length}
      (decoded : program s.cpu.pc=some (op,length))
      (executed : execute env op {s with cpu:={s.cpu with pc:=s.cpu.pc+length}}=some middle)
      (rest : Prefix env program n middle last) : Prefix env program (n+1) s last

theorem Prefix.trans {env p n m s t u} (a : Prefix env p n s t)
    (b : Prefix env p m t u) : Prefix env p (n+m) s u := by
  induction a with
  | nil => simpa using b
  | step decoded executed rest ih =>
    simpa [Nat.succ_add] using Prefix.step decoded executed (ih b)
theorem Prefix.transfer {env p n s t} (path : Prefix env p n s t)
    (q : Program) (agree : ∀ pc, p pc≠none → q pc=p pc) : Prefix env q n s t := by
  induction path with
  | nil => exact .nil _
  | @step n s middle last op len hd hx rest ih =>
    exact .step ((agree s.cpu.pc (by simp [hd])).trans hd) hx ih

theorem execute_memory (env : Environment) (op : Op) (s t : State)
    (h : execute env op s=some t) : t.cpu.core.memory=s.cpu.core.memory := by
  have frame : (execute env op s).map (fun t => t.cpu.core.memory) =
      (execute env op s).map (fun _ => s.cpu.core.memory) := by
    cases op <;> unfold execute <;> split <;> try rfl
    case less.isTrue d hg =>
      dsimp only
      rw [Option.map_map,Option.map_map]
      change Option.map (fun c : X86Control.State => c.core.memory)
        (do
          let f ← s.cpu.flags
          if f.sign != f.overflow then
            if (s.cpu.pc : Int)+d < 0 ∨ (s.cpu.pc : Int)+d ≥ 4294967296 then none
            else some {s.cpu with pc:=((s.cpu.pc : Int)+d).toNat}
          else some s.cpu) =
        Option.map (fun _ : X86Control.State => s.cpu.core.memory)
        (do
          let f ← s.cpu.flags
          if f.sign != f.overflow then
            if (s.cpu.pc : Int)+d < 0 ∨ (s.cpu.pc : Int)+d ≥ 4294967296 then none
            else some {s.cpu with pc:=((s.cpu.pc : Int)+d).toNat}
          else some s.cpu)
      cases hf : s.cpu.flags with
      | none => rfl
      | some flags =>
        simp only [bind,Bind.bind,Option.bind]
        split
        · split <;> rfl
        · rfl
  simpa [h] using frame

theorem Prefix.memory {env p n s t} (path : Prefix env p n s t) :
    t.cpu.core.memory=s.cpu.core.memory := by
  induction path with
  | nil => rfl
  | step decoded executed rest ih =>
    have kept := execute_memory _ _ _ _ executed
    exact ih.trans kept
end Doom.Verification.X86VgaRoutine
