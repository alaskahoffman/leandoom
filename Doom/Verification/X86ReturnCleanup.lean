import Doom.Verification.X86CodeMemory

/-! Opt-in 32-bit near RET imm16 support. Existing decoded operations retain
exactly their existing code-memory semantics. Like that model, this models flat
32-bit addresses and successful memory reads, not segment or access faults. -/
namespace Doom.Verification.X86ReturnCleanup
open X86 X86Memory X86Control

inductive Op where
  | prior (op : X86Routine.Op)
  | retCleanup (bytes : BitVec 16)
  deriving DecidableEq
abbrev Program := Nat → Option (Op × Nat)

def decodeAt (code : List UInt8) (pc : Nat) : Option (Op × Nat) :=
  match code.drop pc with
  | 0xc2 :: lo :: hi :: _ => some (.retCleanup (hi.toBitVec ++ lo.toBitVec),3)
  | 0xc2 :: _ => none
  | _ => (X86Routine.decodeAt code pc).map fun (op,len) => (.prior op,len)

def returned (bytes : BitVec 16) (s : X86Control.State) : X86Control.State :=
  ⟨put s.core 4 (s.core.regs 4+4+bytes.zeroExtend 32),s.flags,
    (load32 s.core.memory (s.core.regs 4)).toNat⟩
def execute (cm : Memory) (op : Op) (s : X86Control.State) : Option X86Control.State :=
  match op with
  | .prior op => X86CodeMemory.execute cm op s
  | .retCleanup bytes => some (returned bytes s)
def embed (p : X86Routine.Program) : Program := fun pc =>
  (p pc).map fun (op,len) => (.prior op,len)

theorem prior_execution (cm : Memory) (op : X86Routine.Op) (s : X86Control.State) :
    execute cm (.prior op) s=X86CodeMemory.execute cm op s := rfl

theorem zero_cleanup (cm : Memory) (s : X86Control.State) :
    execute cm (.retCleanup 0) s=X86CodeMemory.execute cm .ret s := by
  simp [execute,returned,X86CodeMemory.execute,X86Routine.execute]

/-- The immediate is unsigned; only ESP changes, after the original stack word
has supplied the destination. Memory and flags are unchanged. -/
theorem layout (bytes : BitVec 16) (s : X86Control.State) :
    (returned bytes s).pc=(load32 s.core.memory (s.core.regs 4)).toNat ∧
    (returned bytes s).core.regs 4=s.core.regs 4+4+bytes.zeroExtend 32 ∧
    (returned bytes s).core.memory=s.core.memory ∧
    (returned bytes s).flags=s.flags ∧
    (∀ r, r≠4 → (returned bytes s).core.regs r=s.core.regs r) := by
  simp [returned,put,X86.write]; intro r h; simp [h]

inductive Prefix (cm : Memory) (p : Program) (exits : List Nat) :
    Nat → X86Control.State → X86Control.State → Prop
  | nil (s) : Prefix cm p exits 0 s s
  | step {n s middle last op length}
      (active : s.pc∉exits)
      (decoded : p s.pc=some (op,length))
      (executed : execute cm op {s with pc := s.pc+length}=some middle)
      (rest : Prefix cm p exits n middle last) : Prefix cm p exits (n+1) s last

/-- Lift old proofs without changing any of their states, steps or semantics. -/
theorem lift {cm p exits n s t} (path : X86CodeMemory.Prefix cm p exits n s t) :
    Prefix cm (embed p) exits n s t := by
  induction path with
  | nil => exact .nil _
  | @step n s middle last op len active decoded executed rest ih =>
    exact .step (op := .prior op) (length := len) active (by simp [embed,decoded]) executed ih

theorem Prefix.transfer {cm p exits n s t} (path : Prefix cm p exits n s t)
    (q : Program) (agree : ∀ pc, p pc≠none → q pc=p pc) : Prefix cm q exits n s t := by
  induction path with
  | nil => exact .nil _
  | @step n s middle last op len active decoded executed rest ih =>
    exact .step active ((agree s.pc (by simp [decoded])).trans decoded) executed ih

theorem Prefix.trans {cm p exits n m s t u}
    (first : Prefix cm p exits n s t) (second : Prefix cm p exits m t u) :
    Prefix cm p exits (n+m) s u := by
  induction first with
  | nil => simpa using second
  | step active decoded executed rest ih =>
    simpa only [Nat.succ_add] using Prefix.step active decoded executed (ih second)
end Doom.Verification.X86ReturnCleanup
