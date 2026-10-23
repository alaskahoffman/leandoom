import Doom.Proofs.E1M1AimFirstSelection
import Doom.Proofs.E1M1QueryCallback
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1AimQuerySelection
open Verification X86 X86Memory X86Control BlockSummary
open E1M1CellWalkInvariant (Context Cell Common State)
open E1M1MixedCellWalk (inside Admitted Images budget bound history)
open E1M1GridRoute (sourceRoute)
open E1M1QueryCollection (path Entry)
open E1M1TraversalEntry (Protected)
open E1M1FirstIntercept (program)
open E1M1QueryCallback (CallbackSafe)
open E1M1AimFirstSelection (Outcome)
attribute [local irreducible] load32 store32

/-- Query initialization and the entire collection run continuously into the
first ordered selection. The aiming target comes from query-entry memory;
stack shape, counter, records, first return and word transport are derived. -/
theorem execution (q : Context) (pick : Int32 → Int32 → Cell)
    (s : X86Memory.State) (f : Option Flags) (sx sy ex ey : Fixed)
    (entry : Entry q s sx sy ex ey) (profile : E1M1QuerySource.supported q.world=true)
    (xout yout : Int32 × Fixed × Fixed)
    (okX : (path q sx sy ex ey).xStep=.ok xout)
    (okY : (path q sx sy ex ey).yStep=.ok yout)
    (common : Common q) (height : q.world.grid.height=q.height)
    (statics : ∀ c∈sourceRoute pick 64 (E1M1FiringGridState.initial (path q sx sy ex ey) xout yout), Admitted q c)
    (scenes : ∀ c∈sourceRoute pick 64 (E1M1FiringGridState.initial (path q sx sy ex ey) xout yout),
      inside q c=true → E1M1CellLineSource.SceneLines q c)
    (payloads : ∀ c∈sourceRoute pick 64 (E1M1FiringGridState.initial (path q sx sy ex ey) xout yout),
      inside q c=true → E1M1QueryImages.Payload s.memory q c ∧ E1M1QueryImages.Protected s q c)
    (separated : Protected q)
    (callbackSafe : CallbackSafe q s)
    (argument : load32 s.memory (s.regs 4+8)=0x2b760)
    (cursorCall : Apart 0x2c028 (q.sp-140))
    (room : budget q (sourceRoute pick 64 (E1M1FiringGridState.initial (path q sx sy ex ey) xout yout))≤128) :
    let g := E1M1FiringGridState.initial (path q sx sy ex ey) xout yout
    let cells := sourceRoute pick 64 g
    let seen := Array.replicate q.world.lines.size false
    ∃ (collected : X86Control.State) (after : Collision.PathResult) (out : X86Control.State),
      (∃ n≤207+bound q cells+7*after.collected.size,
        X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2c8a0⟩ out) ∧
      E1M1LiveWalk.source q.world q.trace 64 g seen {trace:=q.trace}=
        .ok (E1M1LoopReplay.pack (E1M1PathAdvance.observe collected.core) (history q seen cells) after) ∧
      (∀ visit, q.world.pathTraverse sx sy ex ey 3 visit=E1M1QuerySource.visitHits after visit) ∧
      State q collected after (history q seen cells) ∧
      Outcome after.collected (E1M1ThingFinish.resolve q.lines q.objects) (q.sp-136) out ∧
      E1M1AimStackShape.Shape (q.sp-136) out ∧
      load32 out.core.memory ((q.sp-136)+20)=0x2cb0b ∧
      (∀ a, E1M1PathMapSetup.Safe s a → E1M1FiringMapState.Safe q.sp q.lines a →
        E1M1AimEntryFrame.SafeWord (q.sp-112) a →
        load32 out.core.memory a=load32 s.memory a) := by
  obtain ⟨_,_,collected,after,⟨n,hn,run⟩,source,tail,state,_,_,pc,_,frame⟩ :=
    E1M1QueryCallback.collection q pick s f sx sy ex ey entry profile xout yout okX okY
      common height statics scenes payloads room
  have bounded : after.collected.size≤128 := by simpa using state.tracked.room
  have limit : load32 collected.core.memory 0x2c028=E1M1MinimumScan.address after.collected.size := by
    simpa [OriginalLineFinish.cursor,E1M1MinimumScan.address,BitVec.ofNat_add] using state.tracked.cursor
  have sp : collected.core.regs 4-24=q.sp-136 := by
    rw [state.stack]; simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  have pushed : collected.core.regs 4-28=q.sp-140 := by
    rw [state.stack]; simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  have target : OriginalInterceptSetup.callback collected.core=0x2b760 := by
    unfold OriginalInterceptSetup.callback
    rw [state.stack]
    have addr : q.sp-(112#32)+68=q.sp-44 := by simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rw [addr,frame _ callbackSafe.initial callbackSafe.walk]
    rw [entry.stack] at argument
    simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using argument
  have protect : E1M1AimFirstSelection.Protected (collected.core.regs 4) after.collected := by
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · rw [state.stack]; exact separated.cursor
    · intro i hi off ho
      rw [state.stack]; exact separated.records i (by omega) off ho
    · rw [state.stack]; exact FloorCaller.apart_symm (separated.cursor 24 (by simp))
    · rw [pushed]; exact cursorCall
    · intro i hi off ho
      rw [pushed]; exact callbackSafe.records i (by omega) off ho
    · rw [state.stack]; exact FloorCaller.apart_symm (separated.cursor 4 (by simp))
  obtain ⟨m,hm,out,dispatch,outcome,shape,saved,words⟩ :=
    E1M1AimFirstSelection.execution collected.core collected.flags after.collected
      (E1M1ThingFinish.resolve q.lines q.objects) bounded limit state.tracked.encoded protect target
  rw [OriginalPathXStep.at_pc _ _ pc] at dispatch
  rw [sp] at outcome shape saved
  have collectRun := (run.transfer E1M1TraversalEntry.program [] E1M1TraversalEntry.contains_collection (by simp)).transfer
    program [] E1M1FirstIntercept.contains_entry (by simp)
  refine ⟨collected,after,out,⟨n+m,by omega,E1M1PspriteStep.prefix_trans collectRun dispatch⟩,
    source,tail,state,outcome,shape,saved,?_⟩
  intro a initSafe loopSafe callSafe
  exact (words a (by rw [state.stack]; exact callSafe)).trans (frame a initSafe loopSafe)

end Doom.Proofs.E1M1AimQuerySelection
