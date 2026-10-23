import Doom.Proofs.E1M1OutsideLine
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1OutsideCell
open Verification X86 X86Memory X86Control BlockSummary
open E1M1CellWalkInvariant
attribute [local irreducible] load32

/-- Bounds returns preserve existing records and stamps using fixed stack
separation. No candidate is appended, so no extra reserve is required. -/
theorem state_reads (q : Context) (s t : X86Control.State) (r : Collision.PathResult) (seen : Array Bool)
    (common : Common q) (state : E1M1CellWalkInvariant.State q s r seen)
    (stack : t.core.regs 4=q.sp-(112#32))
    (reads : ∀ a, CallerSafe q.sp a → load32 t.core.memory a=load32 s.core.memory a) :
    E1M1CellWalkInvariant.State q t r seen := by
  refine ⟨stack,E1M1CellMapInvariant.transport _ _ q.sp q.base q.lines q.words q.width q.height
    state.maps common.mapLayout (fun a safe => reads a safe.caller),⟨?_,?_,state.tracked.room⟩,
    ⟨(reads _ common.epochSafe.caller).trans state.represented.1,?_⟩,state.size⟩
  · intro i hi
    have old := state.tracked.encoded i hi
    have safe (off : Word) (ho : off∈[(0#32),4,8]) := common.records i (by have := state.tracked.room; omega) off ho
    unfold OriginalLineFinish.RecordAt at old ⊢
    exact ⟨(reads _ (by simpa only [OriginalLineCollection.slot,BitVec.add_zero] using safe (0#32) (by simp))).trans old.1,
      (reads _ (safe 4 (by simp))).trans old.2.1,(reads _ (safe 8 (by simp))).trans old.2.2⟩
  · exact (reads _ common.cursor).trans state.tracked.cursor
  · intro j hj
    rw [reads _ (common.stampSafe j (by simpa only [state.size] using hj)).caller]
    exact state.represented.2 j hj

/-- The enabled object iterator also rejects the out-of-map coordinate, before
reading any object-table entry or running a callback. -/
theorem objects (q : Context) (s : X86Control.State) (r : Collision.PathResult) (seen : Array Bool)
    (common : Common q) (state : E1M1CellWalkInvariant.State q s r seen)
    (pc : s.pc=0x2ca94) (success : s.core.regs 0=(1#32)) (x y : Int32)
    (mapX : s.core.regs 6=x.toBitVec) (mapY : s.core.regs 1=y.toBitVec)
    (outMap : Collision.pathCellInside x y q.width q.height=false) :
    let out := E1M1CellObjectSelection.result s
    (∃ n≤28, X86CodeMemory.Prefix FloorCaller.cm E1M1FiringAdvance.program [] n s out) ∧
    out.pc=0x2cab1 ∧ out.core.regs 0=(1#32) ∧
    E1M1CellWalkInvariant.State q out r seen ∧
    E1M1PathAdvance.observe out.core=E1M1PathAdvance.observe s.core ∧
    E1M1CellMapInvariant.Frame q.sp q.lines s.core.memory out.core.memory := by
  obtain ⟨⟨n,hn,enter⟩,callPC,callSP,cx,cy,_,returnWord,_,_⟩ :=
    E1M1FiringNextThings.enter s q.sp q.lines q.epoch q.objects r.collected seen pc success state.stack state.maps.options
      state.tracked state.represented (common.returns.array _ (by simp [E1M1ScanReturn.returnWords]))
      (common.epochSafe.caller 116 (by simp))
      (fun j hj => (common.stampSafe j (by simpa only [state.size] using hj)).caller 116 (by simp))
  let call := E1M1FiringNextThings.called s
  have address : call.core.regs 4-(4#32)=q.sp-(120#32) := by
    rw [callSP]; simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  have read (a : Word) (safe : E1M1FiringMapState.Safe q.sp q.lines a) :
      load32 call.core.memory a=load32 s.core.memory a := by
    apply OriginalPathCell.call_frame false s.core _ a
    rw [state.stack]
    simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe.caller 116 (by simp)
  have encoding : OriginalThingEntry.Inputs call.core x y q.width q.height := by
    refine ⟨cx.trans mapX,cy.trans mapY,
      (read _ (common.mapLayout.globals _ (by simp))).trans state.maps.width,
      (read _ (common.mapLayout.globals _ (by simp))).trans state.maps.height,
      state.maps.widthBound,state.maps.heightBound,?_⟩
    intro a ha
    rw [address]
    apply (common.mapLayout.globals a ?_).caller 120 (by simp)
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl <;> simp
  have outside : ¬OriginalThingEntry.Inside (OriginalThingEntry.entry call.core) := by
    rw [OriginalThingEntry.live_bounds _ _ _ _ _ encoding,outMap]; decide
  have ret := OriginalThingEntry.outside_return call.core outside
  rw [returnWord,callSP] at ret
  have outSP : (E1M1CellObjectSelection.result s).core.regs 4=q.sp-(112#32) := by
    simpa [E1M1CellObjectSelection.result,call,BitVec.sub_eq_add_neg,BitVec.add_assoc] using ret.2.1
  obtain ⟨m,hm,run⟩ := OriginalThingEntry.execution call.core call.flags
  rw [OriginalPathXStep.at_pc _ _ callPC] at run
  have numeric := E1M1CellObjectSelection.observe s q.sp state.stack
  have restored : E1M1ObjectBoundary.callerView (E1M1CellObjectSelection.result s) q.sp=
      (E1M1CellObjectSelection.result s).core := by
    unfold E1M1ObjectBoundary.callerView
    rw [←outSP]
    unfold put write
    congr; funext i; split <;> simp_all
  rw [restored] at numeric
  exact ⟨⟨n+m,by omega,E1M1PspriteStep.prefix_trans enter
    (X86CodeMemory.lift_success (run.transfer _ [] E1M1NextThingLookup.contains_entry (by simp)) FloorCaller.cm)⟩,
    ret.2.2,ret.1,state_reads q s _ r seen common state outSP
      (fun a safe => E1M1CellObjectSelection.read_word s q.sp state.stack a (safe 116 (by simp)) (safe 120 (by simp))),
    numeric,E1M1CellObjectSelection.frame s q.sp q.lines state.stack⟩

def result (s : X86Control.State) :=
  E1M1CellBoundaryAdvance.result (E1M1CellObjectSelection.result (E1M1OutsideLine.result s))

/-- Complete out-of-map cell: real line and object bounds returns, then the
original grid step. Collected hits and visited history are exactly unchanged. -/
theorem execution (q : Context) (s : X86Control.State) (r : Collision.PathResult) (seen : Array Bool)
    (common : Common q) (state : E1M1CellWalkInvariant.State q s r seen)
    (pc : s.pc=0x2ca7f) (x y : Int32)
    (mapX : s.core.regs 6=x.toBitVec) (mapY : s.core.regs 1=y.toBitVec)
    (outMap : Collision.pathCellInside x y q.width q.height=false) :
    let out := result s
    (∃ n≤71, X86CodeMemory.Prefix FloorCaller.cm E1M1FiringAdvance.program [] n s out) ∧
    E1M1CellWalkInvariant.State q out r seen ∧
    E1M1PathAdvance.observe out.core=E1M1PathAdvance.step (E1M1PathAdvance.observe s.core) ∧
    out.pc=E1M1PathAdvance.nextPc (E1M1PathAdvance.observe s.core) ∧
    E1M1CellMapInvariant.Frame q.sp q.lines s.core.memory out.core.memory := by
  obtain ⟨⟨n,hn,lineRun⟩,linePC,lineOk,lineSP,lineObs,lineFrame⟩ :=
    E1M1OutsideLine.execution q s x y common state.stack state.maps pc mapX mapY outMap
  have lineState := state_reads q s _ r seen common state lineSP (fun a safe => E1M1OutsideLine.read_word s q.sp a state.stack safe)
  obtain ⟨⟨m,hm,objectRun⟩,objectPC,objectOk,objectState,objectObs,objectFrame⟩ :=
    objects q _ r seen common lineState linePC lineOk x y
      ((congrArg E1M1PathAdvance.Cell.mapX lineObs).trans mapX)
      ((congrArg E1M1PathAdvance.Cell.mapY lineObs).trans mapY) outMap
  have obs := objectObs.trans lineObs
  obtain ⟨⟨k,hk,advance⟩,finalSP,finalObs,finalPC,hits,visits⟩ :=
    E1M1CellBoundaryAdvance.execution _ q.sp q.lines q.epoch q.objects (E1M1PathAdvance.observe s.core) r.collected seen
      ⟨objectPC,objectOk,objectState.stack,obs,objectState.tracked,objectState.represented⟩ common.locals
      common.epochSafe.advance (fun j hj => (common.stampSafe j (by simpa only [state.size] using hj)).advance)
  have frame : E1M1CellMapInvariant.Frame q.sp q.lines s.core.memory (result s).core.memory :=
    fun a safe => (E1M1CellBoundaryAdvance.frame _ q.sp objectState.stack a safe.advance).trans
      ((objectFrame a safe).trans (lineFrame a safe))
  exact ⟨⟨n+m+k,by omega,E1M1PspriteStep.prefix_trans (E1M1PspriteStep.prefix_trans lineRun objectRun) advance⟩,
    ⟨finalSP,E1M1CellMapInvariant.transport _ _ q.sp q.base q.lines q.words q.width q.height state.maps common.mapLayout frame,
      hits,visits,state.size⟩,finalObs,finalPC,frame⟩
end Doom.Proofs.E1M1OutsideCell
