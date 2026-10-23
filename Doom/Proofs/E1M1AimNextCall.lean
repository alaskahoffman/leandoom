import Doom.Proofs.E1M1AimRetryCatalog
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimNextCall
open Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1CellWalkInvariant (Context Cell Common State)
open E1M1MixedCellWalk (inside Admitted Images budget bound history)
open E1M1QueryCollection (path)
open E1M1AimRetryGeometry (nextAngle)
open E1M1PathMapQuery (traversal)
open E1M1AimNextContext (context route)
open E1M1AimCatalog (Portal)
open E1M1AimQueryCaller (Source)
open E1M1ThingFinish (resolve)
attribute [local irreducible] load32 store32 SolidThing.shootHeight

/-- The next complete aim call, including ordered line/actor processing and
return, derived from original-memory catalogs and the actual retry's read image.
No catalog or arithmetic result is assumed at a reached machine state. -/
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
    (room : budget (context q thing angle second) (route q pick thing angle second nextX nextY)≤128)
    (shooter : Nat) (shooterValue : q.world.things[shooter]?=some thing)
    (controller : s.regs 6=s.regs 0)
    (separated : E1M1TraversalEntry.Protected q)
    (callbackSafe : E1M1QueryCallback.CallbackSafe q (E1M1AimPreRayMemory.layout s))
    (cursorCall : Apart 0x2c028 (q.sp-140))
    (portals : Nat → Option Portal) (walls : Nat → Prop) (who : Word)
    (watched : List Word)
    (kept : ∀ a∈watched, load32 next.core.memory a=load32 s.memory a)
    (initial : ∀ grid stamps after,
      E1M1LiveWalk.source q.world (context q thing angle second).trace 64
        (E1M1FiringGridState.initial (path q thing.x thing.y
          (thing.attackEndpoint (nextAngle second angle) (Fixed.ofInt 1024)).1
          (thing.attackEndpoint (nextAngle second angle) (Fixed.ofInt 1024)).2) nextX nextY)
        (Array.replicate q.world.lines.size false) {trace:=(context q thing angle second).trace}=
        .ok (E1M1LoopReplay.pack grid stamps after) →
      E1M1AimPreRayCatalog.Initial (context q thing angle second) s q.world shooter after.collected portals walls who ∧
      (∃ traced, Source (context q thing angle second) q.world shooter thing after traced (Fixed.ofInt 1024) portals walls) ∧
      (∀ a∈E1M1AimRetryCatalog.reads after.collected (resolve q.lines q.objects) portals, a∈watched))
    (savedSafe : E1M1AimCallerRegisters.SavedSafe s)
    (returnSafe : E1M1PathMapQuery.Safe s (s.regs 4))
    (watchedRead : ∀ a∈watched, E1M1AimPreRayMemory.Read q s a)
    (watchedSafe : ∀ a∈watched, E1M1AimSavedWords.Protect (E1M1AimQueryCatalog.view q s) a)
    (stampSafe : ∀ a∈E1M1AimStampQuery.stampWords q.lines 475, E1M1AimEntryFrame.SafeWord (q.sp-112) a)
    (stampProtected : ∀ a∈E1M1AimStampQuery.stampWords q.lines 475,
      E1M1AimSavedWords.Protect (E1M1AimQueryCatalog.view q s) a) :
    let cfg := context q thing angle second
    let cells := route q pick thing angle second nextX nextY
    E1M1AimSetupEntry.Inputs cfg next.core thing (nextAngle second angle) (Fixed.ofInt 1024) ∧
    ∃ (after traced : PathResult) (out : X86Control.State) (answer : AimResult) (n : Nat),
      n≤264+bound cfg cells+7*after.collected.size+
        after.collected.size*(157+7*after.collected.size) ∧
      X86ReturnCleanup.Prefix FloorCaller.cm E1M1AimProgramLink.program [] n next out ∧
      q.world.pathTraverse thing.x thing.y
        (thing.attackEndpoint (nextAngle second angle) (Fixed.ofInt 1024)).1
        (thing.attackEndpoint (nextAngle second angle) (Fixed.ofInt 1024)).2 3 (fun _ _ => true)=.ok traced ∧
      q.world.aimLineAttack shooter (nextAngle second angle) (Fixed.ofInt 1024)=.ok answer ∧
      E1M1AimCallerRegisters.Restores next.core out ∧
      E1M1AimReturnedTarget.Image after.collected (resolve q.lines q.objects) out answer ∧
      E1M1BulletAim.ProbeResult out.core answer ∧
      (∀ a∈watched, load32 out.core.memory a=load32 s.memory a) ∧
      E1M1AimStampImage.Image next.core.memory out.core.memory q.lines (q.epoch+1)
        (history cfg (Array.replicate q.world.lines.size false) cells) ∧
      (E1M1AimStampImage.Fresh next.core.memory q.lines ((q.epoch+1)+1) 475 →
        E1M1AimStampImage.Fresh out.core.memory q.lines (load32 out.core.memory 0x13580+1) 475) := by
  let cfg := context q thing angle second
  have inputs := E1M1AimNextContext.inputs q s next thing angle distance second _ h request data seen size image before
  have actor := request.actor.trans controller
  have payloads : ∀ c∈route q pick thing angle second nextX nextY,
      inside cfg c=true → E1M1QueryImages.Payload next.core.memory cfg c ∧
        E1M1AimPreRayMemory.PayloadSafe next.core cfg c := by
    intro c member _
    exact E1M1AimNextContext.payload q thing angle second next.core c
      (data.payloads c member).1 (data.payloads c member).2
  have returnNext := E1M1AimRetryData.safe s next.core (s.regs 4) request.stack returnSafe
  rw [←request.stack] at returnNext
  obtain ⟨after,traced,out,answer,n,hn,run,pathSource,aimSource,restored,target,related,words,stampImage,futureFresh⟩ :=
    E1M1AimStampCall.execution cfg pick next.core next.flags thing (nextAngle second angle) (Fixed.ofInt 1024)
      inputs shooter shooterValue (by decide) profile nextX nextY okX okY
      (E1M1AimNextContext.common q thing angle second common) height statics scenes payloads ⟨separated.cursor,separated.records⟩
      (E1M1AimRetryCatalog.callback cfg s next.core request.stack
        ⟨callbackSafe.initial,callbackSafe.walk,callbackSafe.records⟩) cursorCall room portals walls who
      (by
        intro grid stamps after source
        obtain ⟨catalog,model,covered⟩ := initial grid stamps after source
        exact ⟨E1M1AimRetryCatalog.initial cfg s next.core q.world shooter after.collected portals walls who
          request.stack actor catalog (fun a ha => kept a (covered a ha)),model⟩)
      (E1M1AimRetryCatalog.saved s next.core request.stack savedSafe) returnNext
      watched (fun a ha => E1M1AimRetryCatalog.read q s next.core a request.stack (watchedRead a ha))
      (fun a ha => E1M1AimSavedWords.transport _ _ a rfl (watchedSafe a ha))
      stampSafe (fun a ha => E1M1AimSavedWords.transport _ _ a rfl (stampProtected a ha))
  rw [OriginalPathXStep.at_pc _ _ request.pc] at run
  exact ⟨inputs,after,traced,out,answer,n,hn,run,pathSource,aimSource,restored,target,related,
    fun a ha => (words a ha).trans (kept a ha),stampImage,futureFresh⟩
end Doom.Proofs.E1M1AimNextCall
