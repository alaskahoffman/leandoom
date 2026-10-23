import Doom.Verification.X86ByteRoutine
namespace Doom.Verification.X86ByteRoutine
open X86 X86Memory X86Control
inductive Prefix (program : Program) (exits : List Nat) : Nat → X86Control.State → X86Control.State → Prop
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
    X86ByteRoutine.run program exits (n + fuel) s = X86ByteRoutine.run program exits fuel middle := by
  induction path with
  | nil => simp
  | @step n s middle last op length active decoded executed rest ih =>
    rw [Nat.succ_add]
    simpa only [X86ByteRoutine.run, active, ↓reduceIte, decoded, Bind.bind, Option.bind, executed] using ih


theorem run_mono {p exits n s t} (h : X86ByteRoutine.run p exits n s = some t) (extra : Nat) :
    X86ByteRoutine.run p exits (n + extra) s = some t := by
  induction n generalizing s with
  | zero =>
    by_cases he : s.pc ∈ exits
    · have ht : s = t := by simpa [X86ByteRoutine.run,he] using h
      subst t
      unfold X86ByteRoutine.run
      simp [he]
    · simp [X86ByteRoutine.run, he] at h
  | succ n ih =>
    by_cases he : s.pc ∈ exits
    · have ht : s = t := by simpa [X86ByteRoutine.run,he] using h
      subst t
      unfold X86ByteRoutine.run
      simp [he]
    · simp only [X86ByteRoutine.run, he, ↓reduceIte] at h
      cases hd : p s.pc with
      | none => simp [hd] at h
      | some pair =>
        rcases pair with ⟨op,len⟩
        cases hx : execute op {s with pc := s.pc + len} with
        | none => simp [hd,hx] at h
        | some next =>
          have hn : X86ByteRoutine.run p exits n next = some t := by simpa [hd,hx] using h
          simpa [X86ByteRoutine.run,he,hd,hx,Nat.succ_add] using ih hn

theorem run_path {p exits n s t} (h : X86ByteRoutine.run p exits n s = some t) :
    ∃ k, k ≤ n ∧ Prefix p exits k s t ∧ t.pc ∈ exits := by
  induction n generalizing s with
  | zero =>
    by_cases he : s.pc ∈ exits
    · have ht : s = t := by simpa [X86ByteRoutine.run,he] using h
      subst t
      exact ⟨0,Nat.le_refl _,Prefix.nil s,he⟩
    · simp [X86ByteRoutine.run,he] at h
  | succ n ih =>
    by_cases he : s.pc ∈ exits
    · have ht : s = t := by simpa [X86ByteRoutine.run,he] using h
      subst t
      exact ⟨0,Nat.zero_le _,Prefix.nil s,he⟩
    · cases hd : p s.pc with
      | none => simp [X86ByteRoutine.run,he,hd] at h
      | some pair =>
        rcases pair with ⟨op,len⟩
        cases hx : execute op {s with pc := s.pc + len} with
        | none => simp [X86ByteRoutine.run,he,hd,hx] at h
        | some next =>
          have hn : X86ByteRoutine.run p exits n next = some t := by simpa [X86ByteRoutine.run,he,hd,hx] using h
          obtain ⟨k,hk,path,done⟩ := ih hn
          exact ⟨k+1,by omega,Prefix.step he hd hx path,done⟩

/-- Transfer a path into an enclosing program with a different exit set. Every
executed source instruction must agree and be outside the enclosing exits. -/
theorem Prefix.transfer {p exits n s t} (path : Prefix p exits n s t)
    (q : Program) (outer : List Nat)
    (agree : ∀ pc, p pc ≠ none → q pc = p pc)
    (active : ∀ pc, p pc ≠ none → pc ∉ outer) : Prefix q outer n s t := by
  induction path with
  | nil => exact Prefix.nil _
  | @step n s middle last op len ha hd hx rest ih =>
    have valid : p s.pc ≠ none := by simp [hd]
    exact Prefix.step (active s.pc valid) ((agree s.pc valid).trans hd) hx ih

/-- Compose successful segments with a bound, even when a branch exits the
first segment early. No register, memory or flag reset occurs at the seam. -/
theorem Prefix.finish {p exits n s middle t} (path : Prefix p exits n s middle)
    {fuel : Nat} (tail : X86ByteRoutine.run p exits fuel middle = some t) (budget : Nat)
    (enough : n + fuel ≤ budget) : X86ByteRoutine.run p exits budget s = some t := by
  have joined : X86ByteRoutine.run p exits (n+fuel) s = some t := by rw [path.run fuel, tail]
  have lifted := run_mono joined (budget - (n+fuel))
  simpa only [Nat.add_sub_of_le enough] using lifted

/-- Concatenation preserves every machine component at the seam. -/
theorem Prefix.trans {p exits n m s t u} (a : Prefix p exits n s t)
    (b : Prefix p exits m t u) : Prefix p exits (n+m) s u := by
  induction a with
  | nil => simpa using b
  | step active decoded executed rest ih =>
    simpa [Nat.succ_add] using Prefix.step active decoded executed (ih b)

end Doom.Verification.X86ByteRoutine
