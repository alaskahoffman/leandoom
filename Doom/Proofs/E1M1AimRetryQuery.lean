import Doom.Proofs.E1M1AimRetryRequest
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimRetryQuery
open Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1CellWalkInvariant (Context Cell Common State)
open E1M1MixedCellWalk (inside Admitted Images budget bound history)
open E1M1GridRoute (sourceRoute)
open E1M1QueryCollection (path)
open E1M1QueryCallback (CallbackSafe)
open E1M1AimCatalog (Portal)
open E1M1AimQueryCaller (Source)
open E1M1ThingFinish (resolve)
open E1M1PathMapQuery (traversal)
attribute [local irreducible] load32 store32 SolidThing.shootHeight

/-- Complete aim execution now restores the original caller registers and ESP,
not merely the saved memory values at traversal entry. -/
theorem execution (q : Context) (pick : Int32 → Int32 → Cell)
    (s : X86Memory.State) (f : Option Flags) (thing : SolidThing) (angle : Angle) (distance : Fixed)
    (h : E1M1AimSetupEntry.Inputs q s thing angle distance)
    (shooter : Nat) (shooterValue : q.world.things[shooter]?=some thing)
    (positive : ¬distance.raw≤0) (profile : E1M1QuerySource.supported q.world=true)
    (xout yout : Int32 × Fixed × Fixed)
    (okX : (path q thing.x thing.y (thing.attackEndpoint angle distance).1 (thing.attackEndpoint angle distance).2).xStep=.ok xout)
    (okY : (path q thing.x thing.y (thing.attackEndpoint angle distance).1 (thing.attackEndpoint angle distance).2).yStep=.ok yout)
    (common : Common q) (height : q.world.grid.height=q.height)
    (statics : ∀ c∈sourceRoute pick 64 (E1M1FiringGridState.initial (path q thing.x thing.y (thing.attackEndpoint angle distance).1 (thing.attackEndpoint angle distance).2) xout yout), Admitted q c)
    (scenes : ∀ c∈sourceRoute pick 64 (E1M1FiringGridState.initial (path q thing.x thing.y (thing.attackEndpoint angle distance).1 (thing.attackEndpoint angle distance).2) xout yout),
      inside q c=true → E1M1CellLineSource.SceneLines q c)
    (payloads : ∀ c∈sourceRoute pick 64 (E1M1FiringGridState.initial (path q thing.x thing.y (thing.attackEndpoint angle distance).1 (thing.attackEndpoint angle distance).2) xout yout),
      inside q c=true → E1M1QueryImages.Payload s.memory q c ∧ E1M1AimPreRayMemory.PayloadSafe s q c)
    (separated : E1M1TraversalEntry.Protected q)
    (callbackSafe : CallbackSafe q (E1M1AimPreRayMemory.layout s))
    (cursorCall : Apart 0x2c028 (q.sp-140))
    (room : budget q (sourceRoute pick 64 (E1M1FiringGridState.initial (path q thing.x thing.y (thing.attackEndpoint angle distance).1 (thing.attackEndpoint angle distance).2) xout yout))≤128)
    (portals : Nat → Option Portal) (walls : Nat → Prop) (who : Word)
    (initial : ∀ grid stamps after,
      E1M1LiveWalk.source q.world q.trace 64
        (E1M1FiringGridState.initial (path q thing.x thing.y (thing.attackEndpoint angle distance).1 (thing.attackEndpoint angle distance).2) xout yout)
        (Array.replicate q.world.lines.size false) {trace:=q.trace}=
        .ok (E1M1LoopReplay.pack grid stamps after) →
      E1M1AimPreRayCatalog.Initial q s q.world shooter after.collected portals walls who ∧
      ∃ path, Source q q.world shooter thing after path distance portals walls)
    (savedSafe : E1M1AimCallerRegisters.SavedSafe s)
    (returnSafe : E1M1PathMapQuery.Safe s (s.regs 4)) :
    let g := E1M1FiringGridState.initial (path q thing.x thing.y (thing.attackEndpoint angle distance).1 (thing.attackEndpoint angle distance).2) xout yout
    let cells := sourceRoute pick 64 g
    ∃ (after traced : PathResult) (out : X86Control.State) (answer : AimResult) (n : Nat),
      n≤264+bound q cells+7*after.collected.size+
        after.collected.size*(157+7*after.collected.size) ∧
      X86ReturnCleanup.Prefix FloorCaller.cm E1M1AimProgramLink.program [] n ⟨s,f,0x2bb80⟩ out ∧
      q.world.pathTraverse thing.x thing.y (thing.attackEndpoint angle distance).1 (thing.attackEndpoint angle distance).2 3 (fun _ _ => true)=.ok traced ∧
      q.world.aimLineAttack shooter angle distance=.ok answer ∧
      E1M1AimCallerRegisters.Restores s out ∧
      E1M1AimReturnedTarget.Image after.collected (resolve q.lines q.objects) out answer ∧
      E1M1BulletAim.ProbeResult out.core answer := by
  obtain ⟨after,traced,out,answer,n,hn,run,pathSource,aimSource,restored,image,related⟩ :=
    E1M1AimPreRayQuery.execution q pick s f thing angle distance h shooter shooterValue positive
      profile xout yout okX okY common height statics scenes payloads separated callbackSafe cursorCall room
      portals walls who initial
  exact ⟨after,traced,out,answer,n,hn,run,pathSource,aimSource,
    E1M1AimCallerRegisters.restores q s out h.stack savedSafe returnSafe restored,image,related⟩

/-- If this actual source query has no target, extend the same machine execution
through the next CALL with arguments derived from original caller registers.
This reaches the next query; its memory contracts and execution remain separate. -/
theorem retry (q : Context) (pick : Int32 → Int32 → Cell)
    (s : X86Memory.State) (f : Option Flags) (thing : SolidThing) (angle : Angle) (distance : Fixed)
    (h : E1M1AimSetupEntry.Inputs q s thing angle distance)
    (shooter : Nat) (shooterValue : q.world.things[shooter]?=some thing)
    (positive : ¬distance.raw≤0) (profile : E1M1QuerySource.supported q.world=true)
    (xout yout : Int32 × Fixed × Fixed)
    (okX : (path q thing.x thing.y (thing.attackEndpoint angle distance).1 (thing.attackEndpoint angle distance).2).xStep=.ok xout)
    (okY : (path q thing.x thing.y (thing.attackEndpoint angle distance).1 (thing.attackEndpoint angle distance).2).yStep=.ok yout)
    (common : Common q) (height : q.world.grid.height=q.height)
    (statics : ∀ c∈sourceRoute pick 64 (E1M1FiringGridState.initial (path q thing.x thing.y (thing.attackEndpoint angle distance).1 (thing.attackEndpoint angle distance).2) xout yout), Admitted q c)
    (scenes : ∀ c∈sourceRoute pick 64 (E1M1FiringGridState.initial (path q thing.x thing.y (thing.attackEndpoint angle distance).1 (thing.attackEndpoint angle distance).2) xout yout),
      inside q c=true → E1M1CellLineSource.SceneLines q c)
    (payloads : ∀ c∈sourceRoute pick 64 (E1M1FiringGridState.initial (path q thing.x thing.y (thing.attackEndpoint angle distance).1 (thing.attackEndpoint angle distance).2) xout yout),
      inside q c=true → E1M1QueryImages.Payload s.memory q c ∧ E1M1AimPreRayMemory.PayloadSafe s q c)
    (separated : E1M1TraversalEntry.Protected q)
    (callbackSafe : CallbackSafe q (E1M1AimPreRayMemory.layout s))
    (cursorCall : Apart 0x2c028 (q.sp-140))
    (room : budget q (sourceRoute pick 64 (E1M1FiringGridState.initial (path q thing.x thing.y (thing.attackEndpoint angle distance).1 (thing.attackEndpoint angle distance).2) xout yout))≤128)
    (portals : Nat → Option Portal) (walls : Nat → Prop) (who : Word)
    (initial : ∀ grid stamps after,
      E1M1LiveWalk.source q.world q.trace 64
        (E1M1FiringGridState.initial (path q thing.x thing.y (thing.attackEndpoint angle distance).1 (thing.attackEndpoint angle distance).2) xout yout)
        (Array.replicate q.world.lines.size false) {trace:=q.trace}=
        .ok (E1M1LoopReplay.pack grid stamps after) →
      E1M1AimPreRayCatalog.Initial q s q.world shooter after.collected portals walls who ∧
      ∃ path, Source q q.world shooter thing after path distance portals walls)
    (savedSafe : E1M1AimCallerRegisters.SavedSafe s)
    (returnSafe : E1M1PathMapQuery.Safe s (s.regs 4))
    (second : Bool)
    (controller : s.regs 6=s.regs 0 ∧ s.regs 1=angle.raw.toBitVec)
    (resume : (load32 s.memory (s.regs 4)).toNat=if second then 0x2d7f8 else 0x2d7d5) :
    let g := E1M1FiringGridState.initial (path q thing.x thing.y (thing.attackEndpoint angle distance).1 (thing.attackEndpoint angle distance).2) xout yout
    let cells := sourceRoute pick 64 g
    ∃ (after traced : PathResult) (out : X86Control.State) (answer : AimResult) (n : Nat),
      n≤264+bound q cells+7*after.collected.size+
        after.collected.size*(157+7*after.collected.size) ∧
      X86ReturnCleanup.Prefix FloorCaller.cm E1M1AimProgramLink.program [] n ⟨s,f,0x2bb80⟩ out ∧
      q.world.pathTraverse thing.x thing.y (thing.attackEndpoint angle distance).1 (thing.attackEndpoint angle distance).2 3 (fun _ _ => true)=.ok traced ∧
      q.world.aimLineAttack shooter angle distance=.ok answer ∧
      E1M1AimCallerRegisters.Restores s out ∧
      E1M1AimReturnedTarget.Image after.collected (resolve q.lines q.objects) out answer ∧
      E1M1BulletAim.ProbeResult out.core answer ∧
      (answer.target=none →
        X86ReturnCleanup.Prefix FloorCaller.cm E1M1AimProgramLink.program []
          (n+(4+(if second then 4 else 5))) ⟨s,f,0x2bb80⟩ (E1M1BulletAim.nextQuery second out.core) ∧
        E1M1AimRetryRequest.Request second s (E1M1BulletAim.nextQuery second out.core) ∧
        (E1M1BulletAim.nextQuery second out.core).core.regs 0=s.regs 0 ∧
        (E1M1BulletAim.nextQuery second out.core).core.regs 2=
          angle.raw.toBitVec+(if second then 0xf8000000 else 0x04000000)) := by
  obtain ⟨after,traced,out,answer,n,hn,run,pathSource,aimSource,restored,image,related⟩ :=
    execution q pick s f thing angle distance h shooter shooterValue positive profile xout yout okX okY
      common height statics scenes payloads separated callbackSafe cursorCall room portals walls who initial savedSafe returnSafe
  refine ⟨after,traced,out,answer,n,hn,run,pathSource,aimSource,restored,image,related,?_⟩
  intro miss
  have request := E1M1AimRetryRequest.request second s out restored
  exact ⟨run.trans (E1M1AimRetryRequest.execution second out answer related miss (restored.pc.trans resume)),
    request,request.actor.trans controller.1,by rw [request.angle,controller.2]⟩
end Doom.Proofs.E1M1AimRetryQuery
