import Doom.Proofs.E1M1FirstIntercept
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1QueryDispatch
open Verification X86 X86Memory X86Control BlockSummary
open E1M1CellWalkInvariant (Context Cell Common State)
open E1M1MixedCellWalk (inside Admitted budget bound history)
open E1M1GridRoute (sourceRoute)
open E1M1QueryCollection (path Entry)
open E1M1TraversalEntry (Protected)
open E1M1FirstIntercept (program Boundary)
attribute [local irreducible] load32 store32

/-- Continuous query initialization, collection, selector setup, first minimum
and distance cutoff through either the no-hit exit or the real callback entry.
No state, memory or callback result is supplied at the internal seams. -/
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
      State q collected after (history q seen cells) ∧ Boundary after.collected out := by
  obtain ⟨collected,after,⟨n,hn,setup⟩,collection,tail,state,records,limit,maximum,pc⟩ :=
    E1M1TraversalEntry.execution q pick s f sx sy ex ey entry profile xout yout okX okY
      common height statics scenes payloads separated room
  have bounded : after.collected.size≤128 := by simpa using state.tracked.room
  obtain ⟨m,hm,out,dispatch,boundary⟩ := E1M1FirstIntercept.dispatch
    (E1M1InterceptSetup.result collected.core after.collected.size) after.collected bounded limit
    (E1M1MinimumScan.fractions _ _ _ records) maximum pc
  exact ⟨collected,after,out,⟨n+m,by omega,E1M1PspriteStep.prefix_trans
    (setup.transfer program [] E1M1FirstIntercept.contains_entry (by simp)) dispatch⟩,
    collection,tail,state,boundary⟩
end Doom.Proofs.E1M1QueryDispatch
