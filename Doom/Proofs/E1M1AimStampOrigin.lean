import Doom.Proofs.E1M1AimStampQuery
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimStampOrigin
open Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1CellWalkInvariant (Context Cell)
open E1M1MixedCellWalk (history visits)
attribute [local irreducible] load32 store32

/-- An origin can move backward across a prefix that preserves all stamp words.
The current memory and actual marked history are unchanged. -/
theorem rebase (before origin current : Memory) (lines epoch : Word) (seen : Array Bool)
    (image : E1M1AimStampImage.Image origin current lines epoch seen)
    (kept : ∀ j<seen.size, load32 origin (OriginalLineVisits.stamp lines j)=
      load32 before (OriginalLineVisits.stamp lines j)) :
    E1M1AimStampImage.Image before current lines epoch seen := by
  refine ⟨image.counter,?_⟩
  intro j hj
  rw [image.stamps j hj,kept j hj]

/-- Mixed traversal marks existing entries; it never changes the history size. -/
theorem history_size (q : Context) (seen : Array Bool) (cells : List Cell) :
    (history q seen cells).size=seen.size := by
  induction cells generalizing seen with
  | nil => rfl
  | cons c rest ih =>
    rw [history,ih]
    unfold visits
    split
    · exact OriginalLineVisitedRun.mark_size _ _ _ _
    · rfl

/-- Pre-ray setup leaves stamp words intact, so the completed query's image
can refer to memory before the real P_AimLineAttack prologue. -/
theorem preray (q : Context) (s : X86Memory.State) (thing : SolidThing)
    (angle : Angle) (distance : Fixed) (h : E1M1AimSetupEntry.Inputs q s thing angle distance)
    (out : X86Control.State) (seen : Array Bool) (size : seen.size=475)
    (image : E1M1AimStampImage.Image (E1M1PathMapQuery.traversal s).core.memory
      out.core.memory q.lines q.epoch seen) :
    E1M1AimStampImage.Image s.memory out.core.memory q.lines q.epoch seen := by
  apply rebase s.memory _ out.core.memory q.lines q.epoch seen image
  intro j hj
  exact E1M1PathMapQuery.traversal_frame s _ (h.stampSafe j (by rw [h.lineCount]; omega))
end Doom.Proofs.E1M1AimStampOrigin
