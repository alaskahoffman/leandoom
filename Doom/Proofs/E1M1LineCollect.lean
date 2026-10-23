import Doom.Proofs.E1M1MixedCellWalk
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1LineCollect
open Verification X86 X86Memory X86Control BlockSummary
open OriginalLineMixedInvariant (Candidate Initial Stable)
open OriginalLineVisits (Represents markPrefix)
attribute [local irreducible] load32

/-- Aiming's line body, using the production intersection and bounded append.
The scene lookup and signed-ID guard are supplied by the surrounding loop. -/
def visit (c : Candidate) (seen : Array Bool) (r : Collision.PathResult) :
    Except String (Array Bool × Collision.PathResult) := do
  if seen[c.id]! then return (seen,r)
  let seen := seen.set! c.id true
  if let some frac ← Collision.lineIntercept c.trace c.line then
    return (seen, ← Collision.appendIntercept r ⟨frac,true,c.id⟩)
  return (seen,r)

def collect : List Candidate → Array Bool → Collision.PathResult → Except String (Array Bool × Collision.PathResult)
  | [],seen,r => .ok (seen,r)
  | c::rest,seen,r => do
      let (seen,r) ← visit c seen r
      collect rest seen r

/-- The live stamp test selects the same duplicate branch as the Boolean array.
The initial scan contract supplies the geometry, fraction and bounded capacity. -/
theorem visit_step (initial : X86Memory.State) (n : Nat) (base lines : Word)
    (resolve : Collision.Intercept → Word) (h : Initial initial n base resolve)
    (count : Nat) (layout : OriginalLineVisits.Layout initial h lines count)
    (i : Nat) (s : X86Control.State) (r : Collision.PathResult) (inv : Stable initial h i s r)
    (hi : i<n) (flags : (h.candidates i).flags=3)
    (epoch : Word) (seen : Array Bool) (size : seen.size=count)
    (represented : Represents s.core.memory lines epoch seen) :
    visit (h.candidates i) seen r=.ok (seen.set! (h.candidates i).id true,
      (OriginalLineMixedInvariant.step (h.candidates i) s.core r).2) := by
  have duplicate := OriginalLineVisits.duplicate_iff initial n base resolve h lines count layout i s r inv hi epoch seen size represented
  have bound : (h.candidates i).id<seen.size := by rw [size]; exact layout.ids i hi
  have room : r.collected.size<128 := by have := inv.collection.room; omega
  have early : (h.candidates i).early=false := by simp [Candidate.early,flags]
  by_cases yes : seen[(h.candidates i).id]! =true
  · rw [OriginalLineVisits.set_already seen _ bound yes]
    simp only [visit,yes,ite_true,OriginalLineMixedInvariant.step,if_pos (duplicate.mpr yes)]
    rfl
  · have no : ¬OriginalLineCell.already (OriginalLineCell.header s.core).core := fun d => yes (duplicate.mp d)
    by_cases cross : (h.candidates i).crosses=true
    · have ready := h.crossing i hi cross
      have hit := OriginalLineFinish.line_intercept_live _ _ _ ready.geometry.crosses ready.computed
      simp only [visit,if_neg yes,OriginalLineMixedInvariant.step,if_neg no,if_pos cross,hit,Bind.bind,Except.bind]
      by_cases neg : (h.candidates i).frac.raw<0
      · simp [neg]; rfl
      · simp [neg,early,Collision.appendIntercept,show ¬r.collected.size≥128 by omega,Candidate.hit]; rfl
    · have same := h.rejection i hi (by cases e : (h.candidates i).crosses <;> simp_all)
      have hit := OriginalLineSecondPoint.same_side_none _ _ same.same
      simp [visit,yes,OriginalLineMixedInvariant.step,no,cross,hit,Bind.bind,Except.bind]; rfl

/-- A whole mixed machine scan equals an ordinary seen-array collector. Every
intermediate representation, record budget and branch fact comes from the
initial invariant; nothing is assumed at a reached callback. -/
theorem collect_run (initial : X86Memory.State) (n : Nat) (base lines : Word)
    (resolve : Collision.Intercept → Word) (h : Initial initial n base resolve)
    (count : Nat) (layout : OriginalLineVisits.Layout initial h lines count)
    (i : Nat) (s : X86Control.State) (r : Collision.PathResult) (inv : Stable initial h i s r)
    (k : Nat) (bound : i+k≤n) (flags : ∀ j, i≤j → j<i+k → (h.candidates j).flags=3)
    (epoch : Word) (seen : Array Bool) (size : seen.size=count)
    (represented : Represents s.core.memory lines epoch seen) :
    collect ((List.range' i k).map h.candidates) seen r=.ok
      (markPrefix h.candidates k i seen,(OriginalLineMixedInvariant.run h.candidates k i s r).2) := by
  induction k generalizing i s r seen with
  | zero => rfl
  | succ k ih =>
    have flag := flags i (by omega) (by omega)
    have first := visit_step initial n base lines resolve h count layout i s r inv (by omega) flag epoch seen size represented
    have continues : (h.candidates i).Continues := by right; simp [Candidate.early,flag]
    have nextInv := (OriginalLineMixedInvariant.advance initial n base resolve h i s r inv (by omega) (fun _ _ => continues)).1
    have nextSeen := OriginalLineVisits.step_represents initial n base resolve h lines count layout i s r inv (by omega) epoch seen size represented
    have tail := ih (i+1) _ _ nextInv (by omega) (fun j lo hi => flags j (by omega) (by omega))
      (seen.set! (h.candidates i).id true) (by simpa using size) nextSeen
    simpa only [List.range'_succ,List.map_cons,collect,first,Bind.bind,Except.bind,markPrefix,OriginalLineMixedInvariant.run] using tail
end Doom.Proofs.E1M1LineCollect
