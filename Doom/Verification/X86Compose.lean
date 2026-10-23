import Doom.Verification.X86Control

namespace Doom.Verification.X86Control

/-- Execute an exact prefix without treating any intermediate state as a halt.
This relation also records that the enclosing program has not exited early. -/
inductive Prefix (program : Program) (exits : List Nat) : Nat → State → State → Prop
  | nil (s) : Prefix program exits 0 s s
  | step {n s middle last op length}
      (active : s.pc ∉ exits)
      (decoded : program s.pc = some (op, length))
      (executed : execute op {s with pc := s.pc + length} = some middle)
      (rest : Prefix program exits n middle last) :
      Prefix program exits (n+1) s last

/-- A proved prefix can be plugged into the rest of an execution, retaining the
same memory, registers, flags, PC, program and outer exit set at the seam. -/
theorem Prefix.run {program exits n s middle}
    (path : Prefix program exits n s middle) (fuel : Nat) :
    runProgram program exits (n + fuel) s = runProgram program exits fuel middle := by
  induction path with
  | nil => simp
  | @step n s middle last op length active decoded executed rest ih =>
    rw [Nat.succ_add]
    simpa only [runProgram, active, ↓reduceIte, decoded, Bind.bind, Option.bind, executed] using ih

/-- PC relocation of a local block; memory and registers are untouched. -/
def shiftState (base : Nat) (s : State) : State := {s with pc := base + s.pc}
def shiftProgram (base : Nat) (program : Program) : Program := fun pc =>
  if base ≤ pc then program (pc - base) else none

/-- Forward relative branches need no assumption about address underflow. -/
def ForwardOp : Op → Prop
  | .jumpZero _ offset => 0 ≤ offset
  | _ => True

theorem execute_shift (base : Nat) (op : Op) (s : State) (hf : ForwardOp op) :
    execute op (shiftState base s) = (execute op s).map (shiftState base) := by
  cases op <;> try rfl
  case setle dst =>
    cases hf : s.flags <;> simp [execute, shiftState, hf]
  case jumpZero whenZero offset =>
    cases hflags : s.flags with
    | none => simp [execute, shiftState, hflags]
    | some flags =>
      have ho : 0 ≤ offset := hf
      have hs : ¬ (s.pc : Int) + offset < 0 := by omega
      by_cases hz : flags.zero = whenZero
      · simp [execute, shiftState, hflags, hs, hz]
        congr 1
        omega
      · simp [execute, shiftState, hflags, hs, hz]


theorem runProgram_shift (program : Program)
    (forward : ∀ pc op len, program pc = some (op, len) → ForwardOp op)
    (base : Nat) (exits : List Nat) (fuel : Nat) (s : State) :
    runProgram (shiftProgram base program) (exits.map (base + ·)) fuel (shiftState base s) =
      (runProgram program exits fuel s).map (shiftState base) := by
  induction fuel generalizing s with
  | zero => simp [runProgram, shiftState]
  | succ n ih =>
    have hm : (shiftState base s).pc ∈ exits.map (base + ·) ↔ s.pc ∈ exits := by
      simp [shiftState]
    simp only [runProgram, hm]
    split
    · rfl
    · simp only [shiftProgram, shiftState, Nat.le_add_right, ↓reduceIte, Nat.add_sub_cancel_left]
      cases hp : program s.pc with
      | none => rfl
      | some pair =>
        rcases pair with ⟨op, len⟩
        dsimp only [Bind.bind, Option.bind]
        have he := execute_shift base op {s with pc := s.pc + len} (forward s.pc op len hp)
        simp only [shiftState] at he
        simp only [Nat.add_assoc]
        rw [he]
        cases hx : execute op {s with pc := s.pc + len} with
        | none => rfl
        | some next => simpa using ih next

/-- Embed a verified partial program into a larger program without changing
any successful execution of the partial program. -/
theorem runProgram_extend (larger program : Program)
    (sound : ∀ pc, program pc ≠ none → larger pc = program pc)
    (exits : List Nat) (fuel : Nat) (s : State)
    (valid : runProgram program exits fuel s ≠ none) :
    runProgram larger exits fuel s = runProgram program exits fuel s := by
  induction fuel generalizing s with
  | zero => simp [runProgram]
  | succ n ih =>
    unfold runProgram
    split
    · rfl
    · cases hp : program s.pc with
      | none => simp [runProgram, *] at valid
      | some pair =>
        have hd := sound s.pc (by simp [hp])
        rw [hd, hp]
        rcases pair with ⟨op, length⟩
        dsimp only
        cases he : execute op { s with pc := s.pc + length } with
        | none => simp [he]
        | some next =>
          have hn : runProgram program exits n next ≠ none := by
            simpa [runProgram, hp, he, *] using valid
          simpa [he] using ih next hn


end Doom.Verification.X86Control
