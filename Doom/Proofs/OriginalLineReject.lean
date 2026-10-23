import Doom.Proofs.OriginalLineMixed
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.OriginalLineReject
open Verification X86 X86Memory X86Control BlockSummary
abbrev program := OriginalLineDispatch.program
abbrev first := E1M1LineSecondPoint.firstReturn
abbrev tested := OriginalLineCrossing.tested
def resumed (s : X86Memory.State) := OriginalLineResume.result (tested s).core

def result (s : X86Memory.State) := resumed (OriginalLineDispatch.entry s).core

structure Inputs (s : X86Memory.State) (trace : Collision.Divline) (line : Collision.Line)
    (p v w : Word) : Prop where
  entry : OriginalLineInterceptEntry.Inputs s trace line p v
  data : E1M1LineSecondPoint.LineData s line p v w
  same : OriginalLineSecondPoint.firstSide trace line=OriginalLineSecondPoint.lastSide trace line

variable (s : X86Memory.State) (trace : Collision.Divline) (line : Collision.Line)
  (p v w : Word) (h : Inputs s trace line p v w)
include h

theorem tested_form : tested s=OriginalLineSecondPoint.rejected
    (OriginalLineSecondPoint.second trace.usesDivlineTest (first s).core).core := by
  rw [tested,OriginalLineCrossing.tested,E1M1LineSecondPoint.at_return _ _
    (E1M1LineSecondPoint.first_return_regs s trace line p v h.entry).2.2,
    OriginalLineSecondPoint.live _ trace line p v w
      (E1M1LineSecondPoint.entry_inputs s trace line p v w h.entry h.data),if_pos h.same]

theorem saved_cursor : load32 (tested s).core.memory (s.regs 4-(12#32))=s.regs 2 := by
  have apart (x y : Word) (hy : Apart (-x) (-y)) := OriginalLineSide.slots_apart (s.regs 4) x y hy
  have sp := (OriginalLineInterceptEntry.gate_preserves (OriginalLineInterceptEntry.prepared s)).2.2.trans
    (OriginalLineInterceptEntry.prepared_regs s).2.1
  have callKeep : load32 (OriginalLineInterceptEntry.first s).core.memory (s.regs 4-(12#32))=s.regs 2 := by
    unfold OriginalLineInterceptEntry.first
    rw [OriginalLineInterceptEntry.call_frame]
    · rw [(OriginalLineInterceptEntry.gate_preserves (OriginalLineInterceptEntry.prepared s)).1,
        OriginalLineInterceptEntry.prepared_memory]
      unfold OriginalLineInterceptEntry.saved
      change load32 (store32 (store32 (store32 _ (s.regs 4-(12#32)) (s.regs 2))
        (s.regs 4-(16#32)) _) (s.regs 4-(20#32)) _) (s.regs 4-(12#32))=s.regs 2
      rw [load_store_apart _ _ _ _ (apart (12#32) (20#32) (by unfold Apart; decide)),
        load_store_apart _ _ _ _ (apart (12#32) (16#32) (by unfold Apart; decide)),load_store]
    · rw [sp]
      simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using apart 12 40 (by unfold Apart; decide)
  have helperSafe : ∀ off∈[(4#32),8,12,16],
      Apart (s.regs 4-(12#32)) ((OriginalLineInterceptEntry.first s).core.regs 4-off) := by
    rw [(OriginalLineInterceptEntry.live s trace line p v h.entry).stack]
    intro off ho
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
    rcases ho with rfl|rfl|rfl|rfl
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using apart 12 44 (by unfold Apart; decide)
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using apart 12 48 (by unfold Apart; decide)
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using apart 12 52 (by unfold Apart; decide)
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using apart 12 56 (by unfold Apart; decide)
  have firstKeep : load32 (first s).core.memory (s.regs 4-(12#32))=s.regs 2 := by
    rw [first,E1M1LineSecondPoint.first_return_form s trace line p v h.entry]
    split
    · exact (OriginalDivlineSide.frame _ _ helperSafe).trans callKeep
    · exact (OriginalLineSide.frame _ _ helperSafe).trans callKeep
  rw [tested_form s trace line p v w h,OriginalLineSecondPoint.rejected_frame]
  apply (OriginalLineSecondPoint.second_frame _ _ _ ?_).trans firstKeep
  rw [(E1M1LineSecondPoint.first_return_regs s trace line p v h.entry).1]
  intro off ho
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
  rcases ho with rfl|rfl|rfl|rfl|rfl
  · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using apart 12 40 (by unfold Apart; decide)
  · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using apart 12 44 (by unfold Apart; decide)
  · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using apart 12 48 (by unfold Apart; decide)
  · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using apart 12 52 (by unfold Apart; decide)
  · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using apart 12 56 (by unfold Apart; decide)

theorem tested_frame (a : Word) (safe : OriginalLineCrossing.SideSafe s a) :
    load32 (tested s).core.memory a=load32 s.memory a := by
  rw [tested,OriginalLineCrossing.tested,E1M1LineSecondPoint.at_return _ _
    (E1M1LineSecondPoint.first_return_regs s trace line p v h.entry).2.2]
  have inner : ∀ off∈[(4#32),8,12,16,20], Apart a ((first s).core.regs 4-off) := by
    rw [(E1M1LineSecondPoint.first_return_regs s trace line p v h.entry).1]
    intro off ho
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
    rcases ho with rfl|rfl|rfl|rfl|rfl
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe 40 (by simp)
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe 44 (by simp)
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe 48 (by simp)
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe 52 (by simp)
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe 56 (by simp)
  exact (OriginalLineSecondPoint.frame _ _ a inner).trans
    (E1M1LineSecondPoint.first_return_frame s trace line p v h.entry a safe)

theorem tested_observe :
    (tested s).core.regs 0=(1#32) ∧ (tested s).core.regs 2=s.regs 2 ∧
    (tested s).core.regs 4=s.regs 4+(4#32) ∧
    (tested s).pc=(load32 s.memory (s.regs 4)).toNat ∧
    Collision.lineIntercept trace line=.ok none := by
  have live := E1M1LineSecondPoint.callback_rejection s trace line p v w h.entry h.data h.same
  have r := OriginalLineSecondPoint.second_saved trace.usesDivlineTest (first s).core
  have f := E1M1LineSecondPoint.first_return_regs s trace line p v h.entry
  have cursor : (tested s).core.regs 2=load32 (tested s).core.memory (s.regs 4-(12#32)) := by
    rw [tested_form s trace line p v w h]
    simp only [OriginalLineSecondPoint.rejected,OriginalLineSecondPoint.unwind,
      OriginalLineSecondPoint.unwind5,OriginalLineSecondPoint.unwind4,OriginalLineSecondPoint.unwind3,
      OriginalLineSecondPoint.unwind2,OriginalLineSecondPoint.unwind1,OriginalLineSecondPoint.unwind0,put,write]
    simp only [show (2 : Fin 8)≠4 by decide,if_false,ite_true]
    rw [r.1,f.1]
    exact congrArg (load32 (OriginalLineSecondPoint.second trace.usesDivlineTest (first s).core).core.memory)
      (show s.regs 4-(36#32)+(24#32)=s.regs 4-(12#32) by bv_decide)
  refine ⟨live.1,cursor.trans (saved_cursor s trace line p v w h),?_,live.2.1,live.2.2⟩
  rw [tested_form s trace line p v w h]
  change (OriginalLineSecondPoint.second trace.usesDivlineTest (first s).core).core.regs 4+(40#32)=_
  rw [r.1,f.1]; bv_decide

theorem callback_execution (f : Option Flags) (ret : load32 s.memory (s.regs 4)=(0x2c578#32)) :
    ∃ n≤167, X86Routine.Prefix program [] n ⟨s,f,0x2c5f0⟩ (resumed s) := by
  obtain ⟨n,hn,a⟩ := OriginalLineCrossing.tests_execution s f
  obtain ⟨m,hm,b⟩ := OriginalLineResume.execution (tested s).core (tested s).flags
  have pc : (tested s).pc=0x2c578 := by rw [(tested_observe s trace line p v w h).2.2.2.1,ret]; rfl
  rw [OriginalPathXStep.at_pc _ _ pc] at b
  exact ⟨n+m,by omega,OriginalGroupBounds.prefix_join a (b.transfer program [] E1M1LineResume.contains_resume (by simp))⟩

theorem callback_continued : (resumed s).pc=0x2c57f ∧
    (resumed s).core.regs 2=s.regs 2+(2#32) ∧ (resumed s).core.regs 4=s.regs 4+(4#32) := by
  have r := tested_observe s trace line p v w h
  have k := OriginalLineResume.continued (tested s).core (by rw [r.1]; decide)
  exact ⟨k.1,by rw [resumed,k.2.1,r.2.1],k.2.2.trans r.2.2.1⟩

omit h
theorem entry_inputs (s : X86Memory.State) (trace : Collision.Divline) (line : Collision.Line)
    (p v w : Word) (h : Inputs (OriginalLineDispatch.view s) trace line p v w)
    (safe : ∀ a∈OriginalLineSecondPoint.reads p v w, OriginalLineDispatch.Safe s a) :
    Inputs (OriginalLineDispatch.entry s).core trace line p v w := by
  have keep (a : Word) (ha : a∈OriginalLineSecondPoint.reads p v w) := OriginalLineDispatch.entry_frame s a (safe a ha)
  refine ⟨?_,?_,h.same⟩
  · refine ⟨h.entry.lineArg,?_,?_,?_,?_,?_,?_,?_,h.entry.safeReads⟩
    · rw [keep _ (by simp [OriginalLineSecondPoint.reads])]; exact h.entry.traceX
    · rw [keep _ (by simp [OriginalLineSecondPoint.reads])]; exact h.entry.traceY
    · rw [keep _ (by simp [OriginalLineSecondPoint.reads])]; exact h.entry.traceDX
    · rw [keep _ (by simp [OriginalLineSecondPoint.reads])]; exact h.entry.traceDY
    · rw [keep _ (by simp [OriginalLineSecondPoint.reads])]; exact h.entry.vertex
    · rw [keep _ (by simp [OriginalLineSecondPoint.reads])]; exact h.entry.vertexX
    · rw [keep _ (by simp [OriginalLineSecondPoint.reads])]; exact h.entry.vertexY
  · refine ⟨?_,?_,?_,?_,?_,h.data.safe⟩
    · rw [keep _ (by simp [OriginalLineSecondPoint.reads])]; exact h.data.vertex2
    · rw [keep _ (by simp [OriginalLineSecondPoint.reads])]; exact h.data.x2
    · rw [keep _ (by simp [OriginalLineSecondPoint.reads])]; exact h.data.y2
    · rw [keep _ (by simp [OriginalLineSecondPoint.reads])]; exact h.data.dx
    · rw [keep _ (by simp [OriginalLineSecondPoint.reads])]; exact h.data.dy


structure Ready (s : X86Memory.State) (trace : Collision.Divline) (line : Collision.Line)
    (p v w : Word) : Prop where
  fresh : OriginalLineDispatch.Fresh s
  geometry : Inputs (OriginalLineDispatch.view s) trace line p v w
  geometrySafe : ∀ a∈OriginalLineSecondPoint.reads p v w, OriginalLineDispatch.Safe s a

variable (ready : Ready s trace line p v w)
include ready

theorem execution (f : Option Flags) :
    ∃ n≤178, X86Routine.Prefix program [] n ⟨s,f,0x2c57f⟩ (result s) := by
  obtain ⟨n,hn,a⟩ := OriginalLineDispatch.entry_execution s f ready.fresh
  obtain ⟨m,hm,b⟩ := callback_execution (OriginalLineDispatch.entry s).core trace line p v w
    (entry_inputs s trace line p v w ready.geometry ready.geometrySafe) (OriginalLineDispatch.entry s).flags
    (OriginalLineDispatch.entry_observe s ready.fresh).2.1
  rw [OriginalPathXStep.at_pc _ _ (OriginalLineDispatch.entry_observe s ready.fresh).1] at b
  exact ⟨n+m,by omega,OriginalGroupBounds.prefix_join a b⟩

theorem continued : (result s).pc=0x2c57f ∧ (result s).core.regs 2=s.regs 2+(2#32) ∧
    (result s).core.regs 4=s.regs 4 ∧ Collision.lineIntercept trace line=.ok none := by
  have inputs := entry_inputs s trace line p v w ready.geometry ready.geometrySafe
  have r := callback_continued (OriginalLineDispatch.entry s).core trace line p v w inputs
  refine ⟨r.1,?_,?_,(tested_observe _ trace line p v w inputs).2.2.2.2⟩
  · rw [result,r.2.1,(OriginalLineDispatch.entry_regs s).2.1]
  · rw [result,r.2.2,(OriginalLineDispatch.entry_regs s).2.2]; bv_decide

theorem frame (a : Word) (dispatch : OriginalLineDispatch.Safe s a)
    (safe : OriginalLineCrossing.SideSafe (OriginalLineDispatch.view s) a) :
    load32 (result s).core.memory a=load32 s.memory a := by
  rw [result,resumed,OriginalLineResume.memory]
  exact (tested_frame (OriginalLineDispatch.entry s).core trace line p v w
    (entry_inputs s trace line p v w ready.geometry ready.geometrySafe) a safe).trans
    (OriginalLineDispatch.entry_frame s a dispatch)

end Doom.Proofs.OriginalLineReject
