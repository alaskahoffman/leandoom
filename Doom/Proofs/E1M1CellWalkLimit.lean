import Doom.Proofs.E1M1CellWalk
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1CellWalkLimit
open Verification X86
open E1M1CellWalkInvariant (Cell)
open E1M1CellWalk (Follows stopPc)
open E1M1PathAdvance (step nextPc ended axis)

/-- A continued iteration increments a legal counter; signed/wrapping states
outside 0..63 are not silently treated as legal loop indices. -/
theorem continuation (g : E1M1PathAdvance.Cell) (n : Nat) (legal : n<64)
    (counter : g.count=BitVec.ofNat 32 n) (go : nextPc g=0x2ca7f) :
    ended g=false ∧ n+1<64 ∧ (step g).count=BitVec.ofNat 32 (n+1) := by
  have notEnd : ended g=false := by
    cases h : ended g <;> simp_all [nextPc]
  have test : (g.count+(1#32)).toInt<64 := by
    unfold nextPc at go
    change (if ended g then 0x2cafd else if (g.count+(1#32)).toInt<64 then 0x2ca7f else 0x2cafd)=0x2ca7f at go
    rw [notEnd] at go
    split at go <;> simp_all
  have nextLegal := (E1M1PathAdvance.counter_limit n legal).mp (by simpa only [counter] using test)
  refine ⟨notEnd,nextLegal,?_⟩
  simp only [step,notEnd,Bool.false_eq_true,ite_false]
  rw [counter,BitVec.ofNat_add]
  rfl

/-- The itinerary condition itself rules out more than the remaining 64 cells,
including stalls; this length is derived, not an extra traversal premise. -/
theorem length_bound (g : E1M1PathAdvance.Cell) (n : Nat) (cells : List Cell)
    (legal : n<64) (counter : g.count=BitVec.ofNat 32 n) (follows : Follows g cells) :
    cells.length≤64-n := by
  induction cells generalizing g n with
  | nil => simp
  | cons c rest ih =>
    cases rest with
    | nil => simp; omega
    | cons d tail =>
      have cont := continuation g n legal counter (follows.2.2.1 (by simp))
      have remaining := ih (step g) (n+1) cont.2.1 cont.2.2 follows.2.2.2
      simp only [List.length_cons] at remaining ⊢
      omega

/-- Exhausting the legal iteration budget reaches the original exit PC even
if the numeric path stalls. Endpoint exits may happen sooner. -/
theorem exhausted (pc : Nat) (g : E1M1PathAdvance.Cell) (n : Nat) (cells : List Cell)
    (legal : n<64) (counter : g.count=BitVec.ofNat 32 n) (follows : Follows g cells)
    (full : cells.length=64-n) : stopPc pc g cells=0x2cafd := by
  induction cells generalizing pc g n with
  | nil => simp only [List.length_nil] at full; omega
  | cons c rest ih =>
    cases rest with
    | nil =>
      have last : n=63 := by simp only [List.length_cons,List.length_nil] at full; omega
      have stop : ¬(g.count+(1#32)).toInt<64 := by
        rw [counter,E1M1PathAdvance.counter_limit n legal]
        omega
      change (if ended g then 0x2cafd else if (g.count+(1#32)).toInt<64 then 0x2ca7f else 0x2cafd)=0x2cafd
      rw [if_neg stop]
      split <;> rfl
    | cons d tail =>
      have cont := continuation g n legal counter (follows.2.2.1 (by simp))
      exact ih (nextPc g) (step g) (n+1) cont.2.1 cont.2.2 follows.2.2.2 (by
        simp only [List.length_cons] at full ⊢; omega)
end Doom.Proofs.E1M1CellWalkLimit
