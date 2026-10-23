import Doom.Verification.X86Compose

namespace Doom.Verification.X86Control

theorem runProgram_mono {p exits n s t} (h : runProgram p exits n s = some t) (extra : Nat) :
    runProgram p exits (n + extra) s = some t := by
  induction n generalizing s with
  | zero =>
    by_cases he : s.pc ∈ exits
    · have ht : s = t := by simpa [runProgram,he] using h
      subst t
      unfold runProgram
      simp [he]
    · simp [runProgram, he] at h
  | succ n ih =>
    by_cases he : s.pc ∈ exits
    · have ht : s = t := by simpa [runProgram,he] using h
      subst t
      unfold runProgram
      simp [he]
    · simp only [runProgram, he, ↓reduceIte] at h
      cases hd : p s.pc with
      | none => simp [hd] at h
      | some pair =>
        rcases pair with ⟨op,len⟩
        cases hx : execute op {s with pc := s.pc + len} with
        | none => simp [hd,hx] at h
        | some next =>
          have hn : runProgram p exits n next = some t := by simpa [hd,hx] using h
          simpa [runProgram,he,hd,hx,Nat.succ_add] using ih hn

theorem runProgram_path {p exits n s t} (h : runProgram p exits n s = some t) :
    ∃ k, k ≤ n ∧ Prefix p exits k s t ∧ t.pc ∈ exits := by
  induction n generalizing s with
  | zero =>
    by_cases he : s.pc ∈ exits
    · have ht : s = t := by simpa [runProgram,he] using h
      subst t
      exact ⟨0,Nat.le_refl _,Prefix.nil s,he⟩
    · simp [runProgram,he] at h
  | succ n ih =>
    by_cases he : s.pc ∈ exits
    · have ht : s = t := by simpa [runProgram,he] using h
      subst t
      exact ⟨0,Nat.zero_le _,Prefix.nil s,he⟩
    · cases hd : p s.pc with
      | none => simp [runProgram,he,hd] at h
      | some pair =>
        rcases pair with ⟨op,len⟩
        cases hx : execute op {s with pc := s.pc + len} with
        | none => simp [runProgram,he,hd,hx] at h
        | some next =>
          have hn : runProgram p exits n next = some t := by simpa [runProgram,he,hd,hx] using h
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
    {fuel : Nat} (tail : runProgram p exits fuel middle = some t) (budget : Nat)
    (enough : n + fuel ≤ budget) : runProgram p exits budget s = some t := by
  have joined : runProgram p exits (n+fuel) s = some t := by rw [path.run fuel, tail]
  have lifted := runProgram_mono joined (budget - (n+fuel))
  simpa only [Nat.add_sub_of_le enough] using lifted


theorem runProgram_map_mono {α : Type} {p exits n s} {f : State → α} {value : α}
    (h : (runProgram p exits n s).map f = some value) (extra : Nat) :
    (runProgram p exits (n+extra) s).map f = some value := by
  cases hr : runProgram p exits n s with
  | none => simp [hr] at h
  | some t => rw [runProgram_mono hr extra]; simpa [hr] using h

theorem Prefix.finish_map {α : Type} {p exits n s middle} (path : Prefix p exits n s middle)
    {fuel : Nat} {f : State → α} {value : α}
    (tail : (runProgram p exits fuel middle).map f = some value) (budget : Nat)
    (enough : n + fuel ≤ budget) : (runProgram p exits budget s).map f = some value := by
  cases hr : runProgram p exits fuel middle with
  | none => simp [hr] at tail
  | some t => rw [path.finish hr budget enough]; simpa [hr] using tail

def forwardAt (code : List UInt8) (pc : Nat) : Bool :=
  match decodeAt code pc with
  | some (.jumpZero _ offset, _) => decide (0 ≤ offset)
  | _ => true

theorem decoded_forward (code : List UInt8) (checked : ∀ pc : Fin code.length, forwardAt code pc = true)
    (pc : Nat) (op : Op) (len : Nat) (h : decodeAt code pc = some (op,len)) : ForwardOp op := by
  by_cases hp : pc < code.length
  · have hc := checked ⟨pc,hp⟩
    simp only [forwardAt,h] at hc
    cases op <;> simp_all [ForwardOp]
  · have hz : code.drop pc = [] := List.drop_eq_nil_of_le (by omega)
    simp [decodeAt,hz,decode,X86Block.decode,X86Memory.decode,X86.decode] at h

theorem decodeAt_append (head tail : List UInt8) (pc : Nat) :
    decodeAt (head ++ tail) (head.length + pc) = decodeAt tail pc := by
  simp [decodeAt]

end Doom.Verification.X86Control
