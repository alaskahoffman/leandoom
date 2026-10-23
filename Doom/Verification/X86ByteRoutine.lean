import Doom.Verification.X86Routine

/-! Opt-in byte-register arithmetic for the original bounded name comparator.
The old decoder/semantics remain unchanged. State and memory are shared with
X86Routine; only ZF/SF/OF/CF are modeled, as in the surrounding proofs. -/
namespace Doom.Verification.X86ByteRoutine
open X86 X86Memory X86Control
inductive Op where
  | base (op : X86Routine.Op)
  | compareImmediate (dst : Reg) (value : BitVec 8)
  | addImmediate (dst : Reg) (value : BitVec 8)
  | compareBytes (lhs rhs : Reg)
  deriving DecidableEq

def compare8 (a b : BitVec 8) : Flags :=
  {X86Routine.compare8 a b with carry:=some (a.ult b)}
def add8 (a b : BitVec 8) : Flags :=
  let v := a+b
  ⟨v==0,v.msb,(a.msb==b.msb) && (v.msb != a.msb),some (v.ult a)⟩

def execute (op : Op) (s : X86Control.State) : Option X86Control.State :=
  match op with
  | .base op => X86Routine.execute op s
  | .compareImmediate r v => some {s with flags:=some (compare8 (readByte s.core.regs r) v)}
  | .addImmediate r v => some ⟨putByte s.core r (readByte s.core.regs r + v),
      some (add8 (readByte s.core.regs r) v), s.pc⟩
  | .compareBytes a b => some {s with flags:=some (compare8 (readByte s.core.regs a) (readByte s.core.regs b))}

/-- Recognition depends only on bytes and ModR/M fields, never code addresses.
Unsupported memory forms are delegated to the unchanged original decoder. -/
def decode (bytes : List UInt8) : Option (Op × List UInt8) :=
  match bytes with
  | 0x80 :: m :: v :: tail =>
      if m.toNat / 64=3 ∧ m.toNat / 8 % 8=7 then some (.compareImmediate (X86Memory.rm m) v.toBitVec,tail)
      else if m.toNat / 64=3 ∧ m.toNat / 8 % 8=0 then some (.addImmediate (X86Memory.rm m) v.toBitVec,tail)
      else (X86Routine.decode bytes).map fun (op,rest) => (.base op,rest)
  | 0x77 :: d :: tail => some (.base (.jumpAbove d.toBitVec.toInt),tail)
  | 0x38 :: m :: tail =>
      if m.toNat / 64=3 then some (.compareBytes (X86Memory.rm m) (X86Memory.reg m),tail)
      else (X86Routine.decode bytes).map fun (op,rest) => (.base op,rest)
  | _ => (X86Routine.decode bytes).map fun (op,rest) => (.base op,rest)

def decodeAt (bytes : List UInt8) (pc : Nat) : Option (Op × Nat) :=
  (decode (bytes.drop pc)).map fun (op,tail) => (op,(bytes.drop pc).length-tail.length)
abbrev Program := Nat → Option (Op × Nat)
def liftProgram (p : X86Routine.Program) : Program := fun pc =>
  (p pc).map fun (op,len) => (.base op,len)
def run (p : Program) (exits : List Nat) : Nat → X86Control.State → Option X86Control.State
  | fuel,s => if s.pc∈exits then some s else match fuel with
    | 0 => none
    | n+1 => do
      let (op,len) ← p s.pc
      let next ← execute op {s with pc:=s.pc+len}
      run p exits n next

theorem execute_base (op : X86Routine.Op) (s : X86Control.State) :
    execute (.base op) s=X86Routine.execute op s := by rfl

/-- Existing complete executions embed without changing any state or result. -/
theorem run_lift (p : X86Routine.Program) (exits : List Nat) (fuel : Nat) (s : X86Control.State) :
    run (liftProgram p) exits fuel s=X86Routine.run p exits fuel s := by
  induction fuel generalizing s with
  | zero => simp [run,X86Routine.run]
  | succ n ih =>
    rw [run,X86Routine.run]
    split
    · rfl
    · cases hp : p s.pc with
      | none => simp [liftProgram,hp]
      | some pair =>
        rcases pair with ⟨op,len⟩
        simp only [liftProgram,hp,Option.map_some,Option.bind_some,execute_base]
        cases he : X86Routine.execute op {s with pc:=s.pc+len} <;> simp [execute,he,ih]

theorem run_sound (actual listed : Program)
    (sound : ∀ pc, listed pc≠none → actual pc=listed pc)
    (exits : List Nat) (fuel : Nat) (s : X86Control.State)
    (valid : run listed exits fuel s≠none) : run actual exits fuel s=run listed exits fuel s := by
  induction fuel generalizing s with
  | zero => simp [run]
  | succ n ih =>
    unfold run
    split
    · rfl
    · cases hp : listed s.pc with
      | none => simp [run,hp, *] at valid
      | some pair =>
        rw [sound s.pc (by simp [hp]),hp]
        rcases pair with ⟨op,len⟩
        dsimp only
        cases he : execute op {s with pc:=s.pc+len} with
        | none => simp [he]
        | some next =>
          have hn : run listed exits n next≠none := by simpa [run,hp,he, *] using valid
          simpa [he] using ih next hn

theorem byte_memory (s : X86Control.State) (r t : Reg) (v : BitVec 8) :
    (execute (.compareImmediate r v) s).map (fun z => z.core.memory)=some s.core.memory ∧
    (execute (.addImmediate r v) s).map (fun z => z.core.memory)=some s.core.memory ∧
    (execute (.compareBytes r t) s).map (fun z => z.core.memory)=some s.core.memory := by
  constructor; rfl
  constructor <;> rfl
end Doom.Verification.X86ByteRoutine
