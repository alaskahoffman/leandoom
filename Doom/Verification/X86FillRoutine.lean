import Doom.Verification.X86StartupRoutine
/-! Opt-in instructions for the first nested memset calls. This is deliberately
not a complete fill interpreter: DEC/ROR and partially-known shift flags remain
unsupported. The old interpreters and their flag contracts are unchanged. -/
namespace Doom.Verification.X86FillRoutine
open X86 X86Memory X86Control
inductive Op where
  | base (op : X86StartupRoutine.Op)
  | orRegisters (dst src : Reg)
  | compareMemoryByte (address : X86Block.Address) (src : Reg)
  deriving DecidableEq

def execute (op : Op) (s : X86Control.State) : Option X86Control.State :=
  match op with
  | .base op => X86StartupRoutine.execute op s
  | .orRegisters dst src =>
      let v := s.core.regs dst ||| s.core.regs src
      some {s with core:=put s.core dst v,flags:=some (logical32 v)}
  | .compareMemoryByte a src =>
      some {s with flags:=some (X86ByteRoutine.compare8
        (s.core.memory (a.eval s.core.regs)) (readByte s.core.regs src))}

def decode (bytes : List UInt8) : Option (Op × List UInt8) :=
  match bytes with
  | 0x8a :: m :: tail =>
      if m.toNat/64=3 then some (.base (.base (.base (.moveByte (reg m) (rm m)))),tail)
      else (X86StartupRoutine.decode bytes).map fun (op,rest)=>(.base op,rest)
  | 0x8b :: m :: tail =>
      if m.toNat/64=3 then some (.base (.base (.base (.control (.block (.legacy (.mov (reg m) (rm m))))))),tail)
      else (X86StartupRoutine.decode bytes).map fun (op,rest)=>(.base op,rest)
  | 0x0b :: m :: tail =>
      if m.toNat/64=3 then some (.orRegisters (reg m) (rm m),tail) else none
  | 0x38 :: m :: tail =>
      if m.toNat/64≠3 then do
        let (a,rest) ← X86Block.operand m tail
        pure (.compareMemoryByte a (reg m),rest)
      else (X86StartupRoutine.decode bytes).map fun (op,rest)=>(.base op,rest)
  | 0xa8 :: v :: tail => some (.base (.base (.base (.testByteImmediate 0 v.toBitVec))),tail)
  | _ => (X86StartupRoutine.decode bytes).map fun (op,rest)=>(.base op,rest)
def decodeAt (bytes : List UInt8) (pc : Nat) : Option (Op × Nat) :=
  (decode (bytes.drop pc)).map fun (op,tail)=>(op,(bytes.drop pc).length-tail.length)
abbrev Program := Nat → Option (Op × Nat)
def liftProgram (p : X86StartupRoutine.Program) : Program := fun pc =>
  (p pc).map fun (op,len)=>(.base op,len)
inductive Prefix (program : Program) (exits : List Nat) : Nat → X86Control.State → X86Control.State → Prop
  | nil (s) : Prefix program exits 0 s s
  | step {n s middle last op length}
      (active : s.pc ∉ exits)
      (decoded : program s.pc=some (op,length))
      (executed : execute op {s with pc:=s.pc+length}=some middle)
      (rest : Prefix program exits n middle last) : Prefix program exits (n+1) s last

theorem Prefix.trans {p exits n m s t u} (a : Prefix p exits n s t)
    (b : Prefix p exits m t u) : Prefix p exits (n+m) s u := by
  induction a with
  | nil => simpa using b
  | step active decoded executed rest ih =>
    simpa [Nat.succ_add] using Prefix.step active decoded executed (ih b)
theorem Prefix.transfer {p exits n s t} (path : Prefix p exits n s t)
    (q : Program) (outer : List Nat)
    (agree : ∀ pc, p pc≠none → q pc=p pc)
    (active : ∀ pc, p pc≠none → pc∉outer) : Prefix q outer n s t := by
  induction path with
  | nil => exact .nil _
  | @step n s middle last op len ha hd hx rest ih =>
    have valid : p s.pc≠none := by simp [hd]
    exact .step (active s.pc valid) ((agree s.pc valid).trans hd) hx ih

theorem lift_prefix {p exits n s t} (path : X86StartupRoutine.Prefix p exits n s t) :
    Prefix (liftProgram p) exits n s t := by
  induction path with
  | nil => exact .nil _
  | @step n s middle last op len active decoded executed rest ih =>
    exact .step (op:=.base op) (length:=len) active (by simp [liftProgram,decoded]) executed ih
end Doom.Verification.X86FillRoutine
