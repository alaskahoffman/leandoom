import Doom.Verification.X86Routine

/-! Separate immutable code-segment memory for CS-relative table jumps.
Data memory is not used for code-table reads. All other instructions use the
existing semantics; no loader, segment faults or arbitrary indirect calls are modeled. -/
namespace Doom.Verification.X86CodeMemory
open X86 X86Memory X86Control

def execute (codeMemory : Memory) (op : X86Routine.Op) (s : X86Control.State) : Option X86Control.State :=
  match op with
  | .jumpCode a => some {s with pc := (load32 codeMemory (a.eval s.core.regs)).toNat}
  | _ => X86Routine.execute op s

def run (codeMemory : Memory) (p : X86Routine.Program) (exits : List Nat) : Nat → X86Control.State → Option X86Control.State
  | fuel,s => if s.pc ∈ exits then some s else match fuel with
    | 0 => none
    | n+1 => do
      let (op,len) ← p s.pc
      let next ← execute codeMemory op {s with pc := s.pc+len}
      X86CodeMemory.run codeMemory p exits n next

/-- A checked listing still has to agree with the original byte decoder. -/
theorem run_sound (cm : Memory) (actual listed : X86Routine.Program)
    (sound : ∀ pc, listed pc ≠ none → actual pc = listed pc)
    (exits : List Nat) (fuel : Nat) (s : X86Control.State)
    (valid : X86CodeMemory.run cm listed exits fuel s ≠ none) : X86CodeMemory.run cm actual exits fuel s = X86CodeMemory.run cm listed exits fuel s := by
  induction fuel generalizing s with
  | zero => simp [X86CodeMemory.run]
  | succ n ih =>
    unfold X86CodeMemory.run
    split
    · rfl
    · cases hp : listed s.pc with
      | none => simp [X86CodeMemory.run,hp, *] at valid
      | some pair =>
        rw [sound s.pc (by simp [hp]),hp]
        rcases pair with ⟨op,len⟩
        dsimp only
        cases he : execute cm op {s with pc := s.pc+len} with
        | none => simp [he]
        | some next =>
          have hn : X86CodeMemory.run cm listed exits n next ≠ none := by simpa [X86CodeMemory.run,hp,he, *] using valid
          simpa [he] using ih next hn

inductive Prefix (cm : Memory) (program : X86Routine.Program) (exits : List Nat) : Nat → X86Control.State → X86Control.State → Prop
  | nil (s) : Prefix cm program exits 0 s s
  | step {n s middle last op length}
      (active : s.pc ∉ exits)
      (decoded : program s.pc = some (op, length))
      (executed : execute cm op {s with pc := s.pc + length} = some middle)
      (rest : Prefix cm program exits n middle last) :
      Prefix cm program exits (n+1) s last

/-- A proved prefix can be plugged into the rest of an execution, retaining the
same memory, registers, flags, PC, program and outer exit set at the seam. -/
theorem Prefix.run {cm program exits n s middle}
    (path : Prefix cm program exits n s middle) (fuel : Nat) :
    X86CodeMemory.run cm program exits (n + fuel) s = X86CodeMemory.run cm program exits fuel middle := by
  induction path with
  | nil => simp
  | @step n s middle last op length active decoded executed rest ih =>
    rw [Nat.succ_add]
    simpa only [X86CodeMemory.run, active, ↓reduceIte, decoded, Bind.bind, Option.bind, executed] using ih


theorem run_mono {cm p exits n s t} (h : X86CodeMemory.run cm p exits n s = some t) (extra : Nat) :
    X86CodeMemory.run cm p exits (n + extra) s = some t := by
  induction n generalizing s with
  | zero =>
    by_cases he : s.pc ∈ exits
    · have ht : s = t := by simpa [X86CodeMemory.run,he] using h
      subst t
      unfold X86CodeMemory.run
      simp [he]
    · simp [X86CodeMemory.run, he] at h
  | succ n ih =>
    by_cases he : s.pc ∈ exits
    · have ht : s = t := by simpa [X86CodeMemory.run,he] using h
      subst t
      unfold X86CodeMemory.run
      simp [he]
    · simp only [X86CodeMemory.run, he, ↓reduceIte] at h
      cases hd : p s.pc with
      | none => simp [hd] at h
      | some pair =>
        rcases pair with ⟨op,len⟩
        cases hx : execute cm op {s with pc := s.pc + len} with
        | none => simp [hd,hx] at h
        | some next =>
          have hn : X86CodeMemory.run cm p exits n next = some t := by simpa [hd,hx] using h
          simpa [X86CodeMemory.run,he,hd,hx,Nat.succ_add] using ih hn

theorem run_path {cm p exits n s t} (h : X86CodeMemory.run cm p exits n s = some t) :
    ∃ k, k ≤ n ∧ Prefix cm p exits k s t ∧ t.pc ∈ exits := by
  induction n generalizing s with
  | zero =>
    by_cases he : s.pc ∈ exits
    · have ht : s = t := by simpa [X86CodeMemory.run,he] using h
      subst t
      exact ⟨0,Nat.le_refl _,Prefix.nil s,he⟩
    · simp [X86CodeMemory.run,he] at h
  | succ n ih =>
    by_cases he : s.pc ∈ exits
    · have ht : s = t := by simpa [X86CodeMemory.run,he] using h
      subst t
      exact ⟨0,Nat.zero_le _,Prefix.nil s,he⟩
    · cases hd : p s.pc with
      | none => simp [X86CodeMemory.run,he,hd] at h
      | some pair =>
        rcases pair with ⟨op,len⟩
        cases hx : execute cm op {s with pc := s.pc + len} with
        | none => simp [X86CodeMemory.run,he,hd,hx] at h
        | some next =>
          have hn : X86CodeMemory.run cm p exits n next = some t := by simpa [X86CodeMemory.run,he,hd,hx] using h
          obtain ⟨k,hk,path,done⟩ := ih hn
          exact ⟨k+1,by omega,Prefix.step he hd hx path,done⟩

/-- Transfer a path into an enclosing program with a different exit set. Every
executed source instruction must agree and be outside the enclosing exits. -/
theorem Prefix.transfer {cm p exits n s t} (path : Prefix cm p exits n s t)
    (q : X86Routine.Program) (outer : List Nat)
    (agree : ∀ pc, p pc ≠ none → q pc = p pc)
    (active : ∀ pc, p pc ≠ none → pc ∉ outer) : Prefix cm q outer n s t := by
  induction path with
  | nil => exact Prefix.nil _
  | @step n s middle last op len ha hd hx rest ih =>
    have valid : p s.pc ≠ none := by simp [hd]
    exact Prefix.step (active s.pc valid) ((agree s.pc valid).trans hd) hx ih

/-- Compose successful segments with a bound, even when a branch exits the
first segment early. No register, memory or flag reset occurs at the seam. -/
theorem Prefix.finish {cm p exits n s middle t} (path : Prefix cm p exits n s middle)
    {fuel : Nat} (tail : X86CodeMemory.run cm p exits fuel middle = some t) (budget : Nat)
    (enough : n + fuel ≤ budget) : X86CodeMemory.run cm p exits budget s = some t := by
  have joined : X86CodeMemory.run cm p exits (n+fuel) s = some t := by rw [path.run fuel, tail]
  have lifted := run_mono joined (budget - (n+fuel))
  simpa only [Nat.add_sub_of_le enough] using lifted

end Doom.Verification.X86CodeMemory
