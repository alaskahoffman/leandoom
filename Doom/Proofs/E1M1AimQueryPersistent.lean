import Doom.Proofs.E1M1AimEntryPersistent
import Doom.Proofs.E1M1QueryCallback
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1AimQueryPersistent
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

/-- The continuous query supplies its own live Persistent invariant. Initial
contracts are required only for the collection returned by the pure source run;
there is no premise about reached registers, memory, callback slot or invariant. -/
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
    (room : budget q (sourceRoute pick 64 (E1M1FiringGridState.initial (path q sx sy ex ey) xout yout))≤128)
    (portals : Nat → Option E1M1AimCatalog.Portal) (distance z : Fixed)
    (initial : ∀ grid stamps after,
      E1M1LiveWalk.source q.world q.trace 64
        (E1M1FiringGridState.initial (path q sx sy ex ey) xout yout)
        (Array.replicate q.world.lines.size false) {trace:=q.trace}=
        .ok (E1M1LoopReplay.pack grid stamps after) →
      E1M1AimEntryPersistent.Initial q s after.collected portals distance z) :
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
      load32 out.core.memory (q.sp-136)=0x2b760 ∧
      (out.pc=0x2b760 → E1M1AimTraversalInvariant.Persistent out.core after.collected after.collected
        (E1M1ThingFinish.resolve q.lines q.objects) portals distance z) ∧
      (∀ a, E1M1PathMapSetup.Safe s a → E1M1FiringMapState.Safe q.sp q.lines a →
        E1M1AimEntryFrame.SafeWord (q.sp-112) a →
        load32 out.core.memory a=load32 s.memory a) := by
  obtain ⟨collected,after,out,run,source,tail,state,outcome,shape,saved,slot,frame⟩ :=
    E1M1AimQuerySlot.execution q pick s f sx sy ex ey entry profile xout yout okX okY
      common height statics scenes payloads separated callbackSafe argument cursorCall room
  refine ⟨collected,after,out,run,source,tail,state,outcome,shape,saved,slot,?_,frame⟩
  intro live
  exact E1M1AimEntryPersistent.persistent q s out after.collected portals distance z
    (initial _ _ after source) (by simpa using state.tracked.room) separated outcome live frame slot
end Doom.Proofs.E1M1AimQueryPersistent
