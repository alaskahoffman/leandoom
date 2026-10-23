import Doom.Proofs.E1M1AimNextContext
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimNextCollection
open Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1CellWalkInvariant (Context Cell Common State)
open E1M1MixedCellWalk (inside Admitted Images budget bound history)
open E1M1QueryCollection (path)
open E1M1AimRetryGeometry (nextAngle)
open E1M1PathMapQuery (traversal)
open E1M1AimNextContext (context route)
attribute [local irreducible] load32 store32 SolidThing.shootHeight

/-- The next probe reconstructs its entry invariant and executes every cell of
its generated route. Data comes from prepared entry memory; route metadata and
capacity are explicit pure contracts, not assumptions about later machine states. -/
theorem execution (q : Context) (pick : Int32 → Int32 → Cell)
    (s : X86Memory.State) (next : X86Control.State)
    (thing : SolidThing) (angle : Angle) (distance : Fixed) (second : Bool)
    (h : E1M1AimSetupEntry.Inputs q s thing angle distance)
    (request : E1M1AimRetryRequest.Request second s next)
    (seen : Array Bool) (size : seen.size=475)
    (image : E1M1AimStampImage.Image s.memory next.core.memory q.lines q.epoch seen)
    (before : E1M1AimStampImage.Fresh s.memory q.lines (q.epoch+1) 475)
    (nextX nextY : Int32 × Fixed × Fixed)
    (okX : (path q thing.x thing.y (thing.attackEndpoint (nextAngle second angle) (Fixed.ofInt 1024)).1
      (thing.attackEndpoint (nextAngle second angle) (Fixed.ofInt 1024)).2).xStep=.ok nextX)
    (okY : (path q thing.x thing.y (thing.attackEndpoint (nextAngle second angle) (Fixed.ofInt 1024)).1
      (thing.attackEndpoint (nextAngle second angle) (Fixed.ofInt 1024)).2).yStep=.ok nextY)
    (data : E1M1AimRetryInputs.Prepared q next.core thing (nextAngle second angle)
      (route q pick thing angle second nextX nextY))
    (profile : E1M1QuerySource.supported q.world=true)
    (common : Common q) (height : q.world.grid.height=q.height)
    (statics : ∀ c∈route q pick thing angle second nextX nextY, Admitted (context q thing angle second) c)
    (scenes : ∀ c∈route q pick thing angle second nextX nextY,
      inside (context q thing angle second) c=true → E1M1CellLineSource.SceneLines (context q thing angle second) c)
    (room : budget (context q thing angle second) (route q pick thing angle second nextX nextY)≤128) :
    let cfg := context q thing angle second
    let cells := route q pick thing angle second nextX nextY
    let g := E1M1FiringGridState.initial (path q thing.x thing.y
      (thing.attackEndpoint (nextAngle second angle) (Fixed.ofInt 1024)).1
      (thing.attackEndpoint (nextAngle second angle) (Fixed.ofInt 1024)).2) nextX nextY
    let freshSeen := Array.replicate q.world.lines.size false
    E1M1AimSetupEntry.Inputs cfg next.core thing (nextAngle second angle) (Fixed.ofInt 1024) ∧
    cells≠[] ∧ cells.length≤64 ∧ ∃ out after,
      (∃ n≤211+bound cfg cells, X86ReturnCleanup.Prefix FloorCaller.cm E1M1AimProgramLink.program [] n next out) ∧
      E1M1LiveWalk.source q.world cfg.trace 64 g freshSeen {trace:=cfg.trace}=
        .ok (E1M1LoopReplay.pack (E1M1PathAdvance.observe out.core) (history cfg freshSeen cells) after) ∧
      (∀ visit, q.world.pathTraverse thing.x thing.y
        (thing.attackEndpoint (nextAngle second angle) (Fixed.ofInt 1024)).1
        (thing.attackEndpoint (nextAngle second angle) (Fixed.ofInt 1024)).2 3 visit=
          E1M1QuerySource.visitHits after visit) ∧
      State cfg out after (history cfg freshSeen cells) ∧ after.collected.size≤budget cfg cells ∧
      E1M1PathAdvance.observe out.core=E1M1CellWalk.grid g cells ∧ out.pc=0x2cafd ∧
      Images cfg cells out.core.memory ∧
      (∀ a, E1M1AimPreRayMemory.Read cfg next.core a → load32 out.core.memory a=load32 next.core.memory a) ∧
      E1M1AimStampImage.Image next.core.memory out.core.memory q.lines (q.epoch+1) (history cfg freshSeen cells) := by
  let cfg := context q thing angle second
  have inputs := E1M1AimNextContext.inputs q s next thing angle distance second _ h request data seen size image before
  have entry := E1M1AimSetupEntry.entry cfg next.core thing _ _ inputs
  have payloads : ∀ c∈route q pick thing angle second nextX nextY,
      inside cfg c=true → E1M1QueryImages.Payload (traversal next.core).core.memory cfg c ∧
        E1M1QueryImages.Protected (traversal next.core).core cfg c := by
    intro c member _
    have p := E1M1AimNextContext.payload q thing angle second next.core c
      (data.payloads c member).1 (data.payloads c member).2
    exact E1M1AimPreRayMemory.payload next.core cfg c p.1 p.2
  obtain ⟨nonempty,length,out,after,⟨n,hn,run⟩,source,tail,state,used,obs,pc,images,frame,stampImage⟩ :=
    E1M1AimStampCollection.collection cfg pick (traversal next.core).core (traversal next.core).flags
      thing.x thing.y (thing.attackEndpoint (nextAngle second angle) (Fixed.ofInt 1024)).1
      (thing.attackEndpoint (nextAngle second angle) (Fixed.ofInt 1024)).2
      entry profile nextX nextY okX okY (E1M1AimNextContext.common q thing angle second common)
      height statics scenes payloads room
  have atEntry : (traversal next.core).pc=0x2c8a0 := rfl
  rw [OriginalPathXStep.at_pc _ _ atEntry] at run
  have query := (run.transfer E1M1TraversalEntry.program [] E1M1TraversalEntry.contains_collection (by simp)).transfer
    E1M1FirstIntercept.program [] E1M1FirstIntercept.contains_entry (by simp)
  have linked := (X86ReturnCleanup.lift query).transfer E1M1AimProgramLink.program E1M1AimProgramLink.contains_query
  have setup := E1M1AimSetupLink.execution next.core next.flags
  rw [OriginalPathXStep.at_pc _ _ request.pc] at setup
  have originalImage := E1M1AimStampOrigin.preray cfg next.core thing _ _ inputs out _ state.size stampImage
  change n≤175+bound (context q thing angle second) (route q pick thing angle second nextX nextY) at hn
  refine ⟨inputs,nonempty,length,out,after,⟨36+n,by omega,setup.trans linked⟩,
    source,tail,state,used,obs,pc,images,?_,originalImage⟩
  intro a safe
  have later := E1M1AimPreRayMemory.later cfg next.core a safe.2
  exact (frame a later.1 later.2.1).trans (E1M1PathMapQuery.traversal_frame next.core a safe.1)
end Doom.Proofs.E1M1AimNextCollection
