import Doom.Proofs.OriginalLineMixedInvariant
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.OriginalLineInterceptRegister
open Verification X86 X86Memory X86Control BlockSummary

/-- The running X intercept lives in EBP across line callbacks. -/
def register : Fin 8 := 5
def savedOffset : Word := 20
def popOffset : Word := 16

theorem slot_address (sp : Word) :
    sp-(36#32)+popOffset=sp-savedOffset := by
  simp [popOffset,savedOffset,BitVec.sub_eq_add_neg,BitVec.add_assoc]

theorem saved_prologue (s : X86Memory.State) :
    load32 (OriginalLineInterceptEntry.saved s) (s.regs 4-savedOffset)=s.regs register := by
  change load32 (store32 _ (s.regs 4-(20#32)) (s.regs 5)) (s.regs 4-(20#32))=s.regs 5
  exact load_store _ _ _

theorem helper_apart (sp : Word) (off : Word)
    (ho : off∈[(40#32),44,48,52,56]) : Apart (sp-savedOffset) (sp-off) := by
  apply OriginalLineSide.slots_apart
  simp only [savedOffset]
  all_goals
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
    rcases ho with rfl|rfl|rfl|rfl|rfl <;> unfold Apart <;> decide

/-- Neither point-side helper overwrites the saved intercept, on either
side-test outcome. This is a prologue-derived value, not a post-call premise. -/
theorem tested_saved (s : X86Memory.State) (trace : Collision.Divline) (line : Collision.Line)
    (p v : Word) (entry : OriginalLineInterceptEntry.Inputs s trace line p v) :
    load32 (OriginalLineCrossing.tested s).core.memory (s.regs 4-savedOffset)=s.regs register := by
  have sp := (OriginalLineInterceptEntry.gate_preserves (OriginalLineInterceptEntry.prepared s)).2.2.trans
    (OriginalLineInterceptEntry.prepared_regs s).2.1
  have callKeep : load32 (OriginalLineInterceptEntry.first s).core.memory (s.regs 4-savedOffset)=s.regs register := by
    unfold OriginalLineInterceptEntry.first
    rw [OriginalLineInterceptEntry.call_frame]
    · rw [(OriginalLineInterceptEntry.gate_preserves (OriginalLineInterceptEntry.prepared s)).1,
        OriginalLineInterceptEntry.prepared_memory]
      exact saved_prologue s
    · rw [sp]
      simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using helper_apart (s.regs 4) 40 (by simp)
  have helperSafe : ∀ off∈[(4#32),8,12,16],
      Apart (s.regs 4-savedOffset) ((OriginalLineInterceptEntry.first s).core.regs 4-off) := by
    rw [(OriginalLineInterceptEntry.live s trace line p v entry).stack]
    intro off ho
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
    rcases ho with rfl|rfl|rfl|rfl
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using helper_apart (s.regs 4) 44 (by simp)
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using helper_apart (s.regs 4) 48 (by simp)
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using helper_apart (s.regs 4) 52 (by simp)
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using helper_apart (s.regs 4) 56 (by simp)
  have firstKeep : load32 (E1M1LineSecondPoint.firstReturn s).core.memory (s.regs 4-savedOffset)=s.regs register := by
    rw [E1M1LineSecondPoint.first_return_form s trace line p v entry]
    split
    · exact (OriginalDivlineSide.frame _ _ helperSafe).trans callKeep
    · exact (OriginalLineSide.frame _ _ helperSafe).trans callKeep
  rw [OriginalLineCrossing.tested,E1M1LineSecondPoint.at_return _ _
    (E1M1LineSecondPoint.first_return_regs s trace line p v entry).2.2]
  apply (OriginalLineSecondPoint.frame _ _ _ ?_).trans firstKeep
  rw [(E1M1LineSecondPoint.first_return_regs s trace line p v entry).1]
  intro off ho
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
  rcases ho with rfl|rfl|rfl|rfl|rfl
  · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using helper_apart (s.regs 4) 40 (by simp)
  · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using helper_apart (s.regs 4) 44 (by simp)
  · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using helper_apart (s.regs 4) 48 (by simp)
  · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using helper_apart (s.regs 4) 52 (by simp)
  · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using helper_apart (s.regs 4) 56 (by simp)

theorem unwind_intercept (s : X86Memory.State) :
    (OriginalLineSecondPoint.unwind s).core.regs register=load32 s.memory (s.regs 4+popOffset) := by
  simp [register,popOffset,OriginalLineSecondPoint.unwind,OriginalLineSecondPoint.unwind5,
    OriginalLineSecondPoint.unwind4,OriginalLineSecondPoint.unwind3,OriginalLineSecondPoint.unwind2,
    OriginalLineSecondPoint.unwind1,OriginalLineSecondPoint.unwind0,put,write]

theorem resume_intercept (s : X86Memory.State) :
    (OriginalLineResume.result s).core.regs register=s.regs register := by
  unfold OriginalLineResume.result
  split <;> simp [register,OriginalLineResume.exited,
    OriginalLineResume.exit1,OriginalLineResume.exit2,OriginalLineCell.advance,put,write]

theorem finish_intercept (s : X86Memory.State) :
    (OriginalLineFinish.result s).core.regs register=
      load32 (OriginalLineFinish.result s).core.memory (s.regs 4+popOffset) := by
  simp only [OriginalLineFinish.result,OriginalLineFinish.selected]
  split <;> (try split) <;>
    simp [OriginalLineFinish.rejected,OriginalLineFinish.stopped,OriginalLineFinish.accepted,
      OriginalLineFinish.unwind,unwind_intercept,OriginalLineFinish.unwind_memory,
      OriginalLineFinish.inserted_regs,OriginalLineFinish.start,put,write]


theorem scratch_safe (s : X86Memory.State) :
    OriginalLineCrossing.ScratchSafe s (s.regs 4-savedOffset) := by
  intro off ho
  have base : Apart (-(savedOffset)) (-(36#32)+off) := by
    simp only [savedOffset]
    all_goals
      simp only [OriginalLineTail.stackOffsets,List.mem_cons,List.not_mem_nil,or_false] at ho
      rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> unfold Apart <;> decide
  simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using
    OriginalPathXStep.apart_translate (s.regs 4) _ _ base

/-- Both crossing outcomes (discarding or inserting an intercept) restore the
intercept, provided the record writes cannot alias its saved word. -/
theorem crossing_intercept (s : X86Memory.State) (trace : Collision.Divline) (line : Collision.Line)
    (p v w : Word) (h : OriginalLineCrossing.Inputs s trace line p v w)
    (cursor : OriginalLineCrossing.SideSafe s (0x2c028#32) ∧ OriginalLineCrossing.ScratchSafe s (0x2c028#32))
    (savedSafe : OriginalLineTail.RecordSafe s (s.regs 4-savedOffset)) :
    (OriginalLineCrossing.result s).core.regs register=s.regs register := by
  have sp := (OriginalLineCrossing.tested_regs s trace line p v w h).2.1
  have addr : (OriginalLineCrossing.tested s).core.regs 4+popOffset=s.regs 4-savedOffset := by
    rw [sp,slot_address]
  have protect : OriginalLineTail.Protected (OriginalLineCrossing.tested s).core (s.regs 4-savedOffset) := by
    constructor
    · intro off ho; rw [sp]; exact scratch_safe s off ho
    · have eq := OriginalLineCrossing.tested_frame s trace line p v w h _ cursor.1
      simpa only [OriginalLineTail.RecordSafe,OriginalLineFinish.cursor,eq] using savedSafe
  have cursorSafe : OriginalLineTail.StackSafe (OriginalLineCrossing.tested s).core (0x2c028#32) := by
    intro off ho; rw [sp]; exact cursor.2 off ho
  rw [OriginalLineCrossing.result,OriginalLineTail.result,resume_intercept,OriginalLineTail.finished,finish_intercept,
    (OriginalLineFraction.returned _).2.1,addr]
  exact (OriginalLineTail.finished_frame _ _ cursorSafe protect).trans
    (tested_saved s trace line p v h.entry)

/-- The same-side early rejection restores the intercept from the same saved
word; no intercept-array separation is needed on this branch. -/
theorem rejected_intercept (s : X86Memory.State) (trace : Collision.Divline) (line : Collision.Line)
    (p v w : Word) (h : OriginalLineReject.Inputs s trace line p v w) :
    (OriginalLineReject.resumed s).core.regs register=s.regs register := by
  rw [OriginalLineReject.resumed,resume_intercept]
  have restore : (OriginalLineReject.tested s).core.regs register=
      load32 (OriginalLineReject.tested s).core.memory (s.regs 4-savedOffset) := by
    rw [OriginalLineReject.tested_form s trace line p v w h]
    simp only [OriginalLineSecondPoint.rejected,unwind_intercept,put,write,show (4 : Fin 8)≠0 by decide,if_false]
    rw [(OriginalLineSecondPoint.second_saved _ _).1,
      (E1M1LineSecondPoint.first_return_regs s trace line p v h.entry).1,slot_address]
    rfl
  exact restore.trans (tested_saved s trace line p v h.entry)


theorem entry_intercept (s : X86Memory.State) :
    (OriginalLineDispatch.entry s).core.regs register=s.regs register := by
  simp [register,OriginalLineDispatch.entry,OriginalLineDispatch.selected,
    OriginalLineCell.callback,OriginalLineCell.marked,X86Routine.pushWord,OriginalLineCell.duplicate,
    OriginalLineCell.d4,OriginalLineCell.d3,OriginalLineCell.d2,OriginalLineCell.d1,
    OriginalLineCell.header,OriginalLineCell.h1,put,write]

theorem visit_intercept (s : X86Memory.State) :
    (OriginalLineCell.visit s).core.regs register=s.regs register := by
  simp only [OriginalLineCell.visit]
  split <;> (try split) <;>
    simp [register,OriginalLineCell.callback,OriginalLineCell.marked,X86Routine.pushWord,
      OriginalLineCell.advance,OriginalLineCell.duplicate,OriginalLineCell.d4,OriginalLineCell.d3,
      OriginalLineCell.d2,OriginalLineCell.d1,OriginalLineCell.header,OriginalLineCell.h1,put,write]

theorem dispatch_intercept (s : X86Memory.State) (trace : Collision.Divline) (line : Collision.Line)
    (frac : Fixed) (flags : Nat) (p v w : Word)
    (h : OriginalLineDispatch.Ready s trace line frac flags p v w)
    (safe : OriginalLineTail.RecordSafe (OriginalLineDispatch.view s)
      ((OriginalLineDispatch.view s).regs 4-savedOffset)) :
    (OriginalLineDispatch.result s).core.regs register=s.regs register := by
  exact (crossing_intercept (OriginalLineDispatch.entry s).core trace line p v w
    (OriginalLineDispatch.crossing_inputs s trace line p v w h.geometry h.geometrySafe)
    (OriginalLineDispatch.tail_inputs s trace line frac flags p v h.fresh h.tail).cursor
    (OriginalLineDispatch.record_safe s _ (h.tail.dispatchSafe _ (by simp)) safe)).trans
    (entry_intercept s)

theorem reject_intercept (s : X86Memory.State) (trace : Collision.Divline) (line : Collision.Line)
    (p v w : Word) (h : OriginalLineReject.Ready s trace line p v w) :
    (OriginalLineReject.result s).core.regs register=s.regs register :=
  (rejected_intercept (OriginalLineDispatch.entry s).core trace line p v w
    (OriginalLineReject.entry_inputs s trace line p v w h.geometry h.geometrySafe)).trans (entry_intercept s)

open OriginalLineMixedInvariant
section Scan
variable (initial : X86Memory.State) (n : Nat) (base : Word) (resolve : Collision.Intercept → Word)
    (h : Initial initial n base resolve) (i : Nat) (s : X86Control.State) (r : Collision.PathResult)
    (inv : Stable initial h i s r)
include inv

/-- Existing storage and cursor separation already protect the intercept
slot. No new heap-layout premise is needed for the scan. -/
theorem saved_safe (hi : i<n) :
    OriginalLineTail.RecordSafe (OriginalLineDispatch.view s.core)
      ((OriginalLineDispatch.view s.core).regs 4-savedOffset) := by
  apply record_safe initial n base resolve h i s r inv hi
  have layout := storage initial n base resolve h i s r inv hi
  have cursor := (metadata initial n base resolve h i s r inv hi).2.1
  have mem : savedOffset∈[(4#32),8,12,16,20,40,44,48,52,56] := by decide
  exact ⟨fun k hk off ho => FloorCaller.apart_symm (layout.side k hk off ho _ mem),
    FloorCaller.apart_symm (cursor _ mem)⟩

theorem step_intercept (hi : i<n) :
    (step (h.candidates i) s.core r).1.core.regs register=s.core.regs register := by
  by_cases seen : OriginalLineCell.already (OriginalLineCell.header s.core).core
  · simp only [step,if_pos seen]; exact visit_intercept s.core
  · by_cases app : (h.candidates i).crosses=true
    · simp only [step,if_neg seen,if_pos app]
      exact dispatch_intercept _ _ _ _ _ _ _ _ (crossing_ready initial n base resolve h i s r inv hi seen app)
         (saved_safe initial n base resolve h i s r inv hi)
    · have reject : (h.candidates i).crosses=false := by cases eq : (h.candidates i).crosses <;> simp_all
      simp only [step,if_neg seen,if_neg app]
      exact reject_intercept _ _ _ _ _ _ (reject_ready initial n base resolve h i s r inv hi seen reject)

theorem run_intercept (k : Nat) (hi : i+k≤n)
    (keep : ∀ j, i≤j → j<i+k → (h.candidates j).crosses=true → (h.candidates j).Continues) :
    (run h.candidates k i s r).1.core.regs register=s.core.regs register := by
  induction k generalizing i s r with
  | zero => rfl
  | succ k ih =>
    have next := (advance initial n base resolve h i s r inv (by omega)
      (fun _ app => keep i (by omega) (by omega) app)).1
    exact (ih (i+1) (step (h.candidates i) s.core r).1 (step (h.candidates i) s.core r).2 next
      (by omega) (fun j lo hi => keep j (by omega) (by omega))).trans
      (step_intercept initial n base resolve h i s r inv (by omega))
end Scan

/-- The intercept survives the entire mixed scan and sentinel epilogue. -/
theorem finished_intercept (initial : X86Memory.State) (n : Nat) (base : Word)
    (resolve : Collision.Intercept → Word) (h : Initial initial n base resolve)
    (r : Collision.PathResult) (f : Option Flags)
    (collected : OriginalLineCollection.Tracks initial base resolve r.collected n)
    (keep : ∀ j<n, (h.candidates j).crosses=true → (h.candidates j).Continues) :
    (finished initial n base resolve h f r).1.core.regs register=initial.regs register := by
  have retained := run_intercept initial n base resolve h 0 ⟨initial,f,0x2c57f⟩ r
    (start initial n base resolve h r f collected) n (by omega) (fun j _ hj => keep j (by omega))
  simpa [finished,OriginalLineBounds.returned,OriginalLineBounds.r3,OriginalLineBounds.r2,
    OriginalLineBounds.r1,OriginalLineCell.header,OriginalLineCell.h1,register,put,write] using retained

end Doom.Proofs.OriginalLineInterceptRegister
