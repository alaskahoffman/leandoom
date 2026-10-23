import Doom.Verification.X86BytePrefix
/-! Opt-in unsigned register DIV for startup. Existing decoders are unchanged.
Divide-by-zero and quotient overflow fail closed. DIV flags are undefined and
forgotten. No memory DIV, interrupts, fetch, segmentation or hardware refinement. -/
namespace Doom.Verification.X86StartupRoutine
open X86 X86Memory X86Control
inductive Op where
  | base (op : X86ByteRoutine.Op)
  | unsignedDivide (src : Reg)
  deriving DecidableEq

def execute (op : Op) (s : X86Control.State) : Option X86Control.State :=
  match op with
  | .base op => X86ByteRoutine.execute op s
  | .unsignedDivide src =>
      let dividend := (s.core.regs 2 ++ s.core.regs 0).toNat
      let divisor := (s.core.regs src).toNat
      let quotient := dividend / divisor
      if divisor=0 ∨ 4294967296≤quotient then none
      else some {s with core := (put (put s.core 0 (BitVec.ofNat 32 quotient)) 2
        (BitVec.ofNat 32 (dividend % divisor))), flags := none}
def decode (bytes : List UInt8) : Option (Op × List UInt8) :=
  match bytes with
  | 0xf7 :: m :: tail =>
      if m.toNat / 64=3 ∧ m.toNat / 8 % 8=6 then
        some (.unsignedDivide (X86Memory.rm m),tail)
      else (X86ByteRoutine.decode bytes).map fun (op,rest) => (.base op,rest)
  | _ => (X86ByteRoutine.decode bytes).map fun (op,rest) => (.base op,rest)
def decodeAt (bytes : List UInt8) (pc : Nat) : Option (Op × Nat) :=
  (decode (bytes.drop pc)).map fun (op,tail) => (op,(bytes.drop pc).length-tail.length)
abbrev Program := Nat → Option (Op × Nat)
def liftProgram (p : X86ByteRoutine.Program) : Program := fun pc =>
  (p pc).map fun (op,len) => (.base op,len)
inductive Prefix (program : Program) (exits : List Nat) : Nat → X86Control.State → X86Control.State → Prop
  | nil (s) : Prefix program exits 0 s s
  | step {n s middle last op length}
      (active : s.pc ∉ exits)
      (decoded : program s.pc = some (op,length))
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

theorem lift_prefix {p exits n s t} (path : X86ByteRoutine.Prefix p exits n s t) :
    Prefix (liftProgram p) exits n s t := by
  induction path with
  | nil => exact .nil _
  | @step n s middle last op len active decoded executed rest ih =>
    exact .step (op:=.base op) (length:=len) active (by simp [liftProgram,decoded]) executed ih

theorem lift_routine_prefix {p exits n s t} (path : X86Routine.Prefix p exits n s t) :
    Prefix (liftProgram (X86ByteRoutine.liftProgram p)) exits n s t := by
  induction path with
  | nil => exact .nil _
  | @step n s middle last op len active decoded executed rest ih =>
    exact .step (op:=.base (.base op)) (length:=len) active (by simp [liftProgram,X86ByteRoutine.liftProgram,decoded]) executed ih
end Doom.Verification.X86StartupRoutine
