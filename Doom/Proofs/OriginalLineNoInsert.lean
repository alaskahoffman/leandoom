import Doom.Proofs.OriginalLineCollection
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.OriginalLineNoInsert
open Verification X86 X86Memory X86Control BlockSummary
open OriginalLineCollection

/-- Both no-insertion outcomes: a negative fraction continues, whereas an
eligible early-out returns false. Neither writes an intercept record. -/
def NoInsert (frac : Fixed) (flags : Nat) (line : Collision.Line) : Prop :=
  frac.raw<0 ∨ OriginalLineStop.Stops frac flags line

variable (s : X86Memory.State) (trace : Collision.Divline) (line : Collision.Line)
  (frac : Fixed) (flags : Nat) (p v w : Word)
  (h : OriginalLineDispatch.Ready s trace line frac flags p v w)
  (no : NoInsert frac flags line)
include h no

theorem disabled : ¬OriginalLineFinish.inserts (OriginalLineTail.fraction (OriginalLineStop.tested s).core).core := by
  have inputs := OriginalLineTail.inputs (OriginalLineStop.tested s).core trace line frac flags p v
    (OriginalLineCrossing.ready (OriginalLineDispatch.entry s).core trace line p v w
      (OriginalLineDispatch.crossing_inputs s trace line p v w h.geometry h.geometrySafe) frac flags
      (OriginalLineDispatch.tail_inputs s trace line frac flags p v h.fresh h.tail))
  intro enabled
  rcases no with neg|stop
  · apply enabled.1
    simpa [inputs.fraction,Int32.toInt_toBitVec,Int32.lt_iff_toInt_lt] using neg
  · exact enabled.2 ((OriginalLineFinish.early_live _ frac line flags p inputs).mpr stop.2)

/-- Unlike the general frame theorem, no separation from the next record is
needed: the negative/stop branch never writes that record or its cursor. -/
theorem frame (a : Word) (dispatch : OriginalLineDispatch.Safe s a)
    (side : OriginalLineCrossing.SideSafe (OriginalLineDispatch.view s) a)
    (scratch : OriginalLineCrossing.ScratchSafe (OriginalLineDispatch.view s) a) :
    load32 (OriginalLineDispatch.result s).core.memory a=load32 s.memory a := by
  change load32 (OriginalLineResume.result (OriginalLineStop.finished s).core).core.memory a=_
  rw [OriginalLineResume.memory]
  change load32 (OriginalLineFinish.result (OriginalLineTail.fraction (OriginalLineStop.tested s).core).core).core.memory a=_
  rw [OriginalLineFinish.result_memory,if_neg (disabled s trace line frac flags p v w h no)]
  have geometry := OriginalLineDispatch.crossing_inputs s trace line p v w h.geometry h.geometrySafe
  have stack := (OriginalLineCrossing.tested_regs (OriginalLineDispatch.entry s).core trace line p v w geometry).2.1
  have scratch' : OriginalLineTail.StackSafe (OriginalLineStop.tested s).core a := by
    intro off ho
    rw [stack]
    exact scratch off ho
  exact (OriginalLineTail.fraction_frame _ a scratch').trans
    ((OriginalLineCrossing.tested_frame (OriginalLineDispatch.entry s).core trace line p v w geometry a side).trans
      (OriginalLineDispatch.entry_frame s a dispatch))

theorem collection (base : Word) (resolve : Collision.Intercept → Word)
    (hits : Array Collision.Intercept) (reserve : Nat)
    (tracked : Tracks s base resolve hits (reserve+1)) (layout : Layout s base) :
    Tracks (OriginalLineDispatch.result s).core base resolve hits reserve := by
  apply OriginalLineCollection.preserve s _ base resolve hits reserve tracked
  · exact frame s trace line frac flags p v w h no _
      (h.tail.dispatchSafe _ (by simp)) h.tail.cursor.1 h.tail.cursor.2
  · intro i hi off ho
    have cap := tracked.room
    exact frame s trace line frac flags p v w h no _
      (layout.dispatch i (by omega) off ho) (layout.side i (by omega) off ho) (layout.scratch i (by omega) off ho)

omit no in
/-- The production geometric filter rejects a negative intersection fraction. -/
theorem negative_live (neg : frac.raw<0) : Collision.lineIntercept trace line=.ok none := by
  have live := OriginalLineFinish.line_intercept_live trace line frac h.geometry.crosses h.tail.computed
  simpa only [if_pos neg] using live

end Doom.Proofs.OriginalLineNoInsert
