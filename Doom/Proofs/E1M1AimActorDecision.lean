import Doom.Proofs.E1M1AimActorObservation
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimActorDecision
open Verification X86 X86Memory X86Control BlockSummary Collision
attribute [local irreducible] load32 store32

/-- The real target test and bullet-slope store retain actor provenance. -/
theorem decision_image (second : Bool) (initial : Array Intercept) (resolve : Intercept → Word)
    (out : X86Control.State) (answer : AimResult)
    (image : E1M1AimActorCaller.Image initial resolve out answer) :
    E1M1AimActorCaller.Image initial resolve (OriginalBulletSlope.decision second out.core) answer := by
  apply E1M1AimActorObservation.frame initial resolve out _ answer image
  all_goals exact load_store_apart _ _ _ _ (by unfold Apart; decide)

open E1M1CellWalkInvariant (Context Cell Common State)
open E1M1MixedCellWalk (inside Admitted Images budget bound history)
open E1M1GridRoute (sourceRoute)
open E1M1QueryCollection (path Entry)
open E1M1QueryCallback (CallbackSafe)
open E1M1AimCatalog (Portal)
open E1M1AimQueryCatalog (view Protected)
open E1M1ThingFinish (resolve)
attribute [local irreducible] SolidThing.shootHeight

open E1M1AimQueryCaller (Initial Source callerSlots restores)

/-- The complete continuous query supplies its own target-presence evidence and
returns to the controller address saved in initial memory. Append the actual
branch and stored bullet slope without an endpoint PC or target premise. This
covers one center/right probe decision, not all three autoaim queries. -/
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
    (separated : E1M1TraversalEntry.Protected q)
    (callbackSafe : CallbackSafe q s)
    (argument : load32 s.memory (s.regs 4+8)=0x2b760)
    (cursorCall : Apart 0x2c028 (q.sp-140))
    (room : budget q (sourceRoute pick 64 (E1M1FiringGridState.initial (path q sx sy ex ey) xout yout))≤128)
    (scene : Scene) (shooter : Nat) (thing : SolidThing) (distance : Fixed)
    (portals : Nat → Option Portal) (walls : Nat → Prop) (who : Word)
    (initial : ∀ grid stamps after,
      E1M1LiveWalk.source q.world q.trace 64
        (E1M1FiringGridState.initial (path q sx sy ex ey) xout yout)
        (Array.replicate q.world.lines.size false) {trace:=q.trace}=
        .ok (E1M1LoopReplay.pack grid stamps after) →
      Initial q s scene shooter thing after.collected distance portals walls who ∧
      ∃ path, Source q scene shooter thing after path distance portals walls)
    (second : Bool)
    (resume : (load32 s.memory ((q.sp-136)+112)).toNat=if second then 0x2d7f8 else 0x2d7d5) :
    let g := E1M1FiringGridState.initial (path q sx sy ex ey) xout yout
    let cells := sourceRoute pick 64 g
    ∃ (after path : PathResult) (out : X86Control.State) (answer : AimResult) (n : Nat),
      n≤232+bound q cells+7*after.collected.size+
        after.collected.size*(157+7*after.collected.size) ∧
      X86ReturnCleanup.Prefix FloorCaller.cm E1M1AimProgramLink.program [] n ⟨s,f,0x2c8a0⟩ out ∧
      q.world.pathTraverse sx sy ex ey 3 (fun _ _ => true)=.ok path ∧
      E1M1AimSource.afterPath scene shooter thing path distance=.ok answer ∧
      load32 out.core.memory 0x2c0c0=answer.slope.raw.toBitVec ∧
      out.pc=(if answer.target.isSome then 0x2d81e else (if second then 0x2d807 else 0x2d7e4)) ∧
      E1M1AimActorCaller.Image after.collected (resolve q.lines q.objects) out answer ∧
      (∀ id, answer.target=some id → load32 out.core.memory 0x2b9f8=q.objects id ∧
        load32 out.core.memory 0x2b9b4=answer.slope.raw.toBitVec) := by
  obtain ⟨after,path,returned,answer,n,hn,run,pathSource,aimSource,value,restored,image,related⟩ :=
    E1M1AimActorQuery.execution q pick s f sx sy ex ey entry profile xout yout okX okY
      common height statics scenes payloads separated callbackSafe argument cursorCall room
      scene shooter thing distance portals walls who initial
  have pc := restored.2.1.trans resume
  obtain ⟨tail,slope,branch⟩ := E1M1AimTargetDecision.decision second returned answer related pc
  have finalImage := decision_image second after.collected (resolve q.lines q.objects) returned answer image
  exact ⟨after,path,OriginalBulletSlope.decision second returned.core,answer,n+4,by omega,
    run.trans tail,pathSource,aimSource,slope,branch,finalImage,
    fun id chosen => E1M1AimActorCaller.object_pointer after.collected q.lines q.objects _ answer finalImage id chosen⟩
end Doom.Proofs.E1M1AimActorDecision
