import Doom.Proofs.E1M1AimActorStampCall
import Doom.Proofs.E1M1AimThirdCall
import Doom.Proofs.E1M1AimPairController
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimActorThirdCall
open Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1CellWalkInvariant (Context Cell Common)
open E1M1MixedCellWalk (inside Admitted budget bound history)
open E1M1QueryCollection (path)
open E1M1AimRetryInputs (reads Prepared)
open E1M1AimCatalog (Portal)
open E1M1AimQueryCaller (Source)
open E1M1ThingFinish (resolve)
attribute [local irreducible] load32 store32 SolidThing.shootHeight

open E1M1AimThirdCall (angle context route Request prepared inputs)

/-- Execute the whole third query from data retained at the original center
entry. The remaining source arithmetic/catalog and allocation contracts are
explicit; no third callback state or answer is assumed. -/
theorem execution (q : Context) (pick : Int32 → Int32 → Cell)
    (s : X86Memory.State) (third : X86Control.State) (thing : SolidThing) (facing : Angle)
    (h : E1M1AimSetupEntry.Inputs q s thing facing (Fixed.ofInt 1024))
    (request : Request s third facing)
    (epoch : load32 third.core.memory 0x13580=q.epoch+1)
    (fresh : E1M1AimStampImage.Fresh third.core.memory q.lines ((q.epoch+1)+1) 475)
    (shooter : Nat) (shooterValue : q.world.things[shooter]?=some thing)
    (profile : E1M1QuerySource.supported q.world=true)
    (xout yout : Int32 × Fixed × Fixed)
    (okX : (path q thing.x thing.y (thing.attackEndpoint (angle facing) (Fixed.ofInt 1024)).1
      (thing.attackEndpoint (angle facing) (Fixed.ofInt 1024)).2).xStep=.ok xout)
    (okY : (path q thing.x thing.y (thing.attackEndpoint (angle facing) (Fixed.ofInt 1024)).1
      (thing.attackEndpoint (angle facing) (Fixed.ofInt 1024)).2).yStep=.ok yout)
    (common : Common q) (height : q.world.grid.height=q.height)
    (statics : ∀ c∈route q pick thing facing xout yout, Admitted (context q thing facing) c)
    (scenes : ∀ c∈route q pick thing facing xout yout,
      inside (context q thing facing) c=true → E1M1CellLineSource.SceneLines (context q thing facing) c)
    (tables : ThrustTables s.memory)
    (data : ∀ c∈route q pick thing facing xout yout,
      E1M1QueryImages.Payload s.memory q c ∧ E1M1AimPreRayMemory.PayloadSafe s q c)
    (separated : E1M1TraversalEntry.Protected q)
    (callbackSafe : E1M1QueryCallback.CallbackSafe q (E1M1AimPreRayMemory.layout s))
    (cursorCall : Apart 0x2c028 (q.sp-140))
    (room : budget (context q thing facing) (route q pick thing facing xout yout)≤128)
    (portals : Nat → Option Portal) (walls : Nat → Prop) (who : Word)
    (watched : List Word)
    (covered : ∀ a∈reads q s (angle facing) (route q pick thing facing xout yout), a∈watched)
    (kept : ∀ a∈watched, load32 third.core.memory a=load32 s.memory a)
    (initial : ∀ grid stamps after,
      E1M1LiveWalk.source q.world (context q thing facing).trace 64
        (E1M1FiringGridState.initial (path q thing.x thing.y
          (thing.attackEndpoint (angle facing) (Fixed.ofInt 1024)).1
          (thing.attackEndpoint (angle facing) (Fixed.ofInt 1024)).2) xout yout)
        (Array.replicate q.world.lines.size false) {trace:=(context q thing facing).trace}=
        .ok (E1M1LoopReplay.pack grid stamps after) →
      E1M1AimPreRayCatalog.Initial (context q thing facing) s q.world shooter after.collected portals walls who ∧
      (∃ traced, Source (context q thing facing) q.world shooter thing after traced (Fixed.ofInt 1024) portals walls) ∧
      (∀ a∈E1M1AimRetryCatalog.reads after.collected (resolve q.lines q.objects) portals, a∈watched))
    (savedSafe : E1M1AimCallerRegisters.SavedSafe s)
    (returnSafe : E1M1PathMapQuery.Safe s (s.regs 4))
    (watchedRead : ∀ a∈watched, E1M1AimPreRayMemory.Read q s a)
    (watchedSafe : ∀ a∈watched, E1M1AimSavedWords.Protect (E1M1AimQueryCatalog.view q s) a)
    (stampSafe : ∀ a∈E1M1AimStampQuery.stampWords q.lines 475, E1M1AimEntryFrame.SafeWord (q.sp-112) a)
    (stampProtected : ∀ a∈E1M1AimStampQuery.stampWords q.lines 475,
      E1M1AimSavedWords.Protect (E1M1AimQueryCatalog.view q s) a) :
    let cfg := context q thing facing
    let cells := route q pick thing facing xout yout
    ∃ (after traced : PathResult) (out : X86Control.State) (answer : AimResult) (n : Nat),
      n≤264+bound cfg cells+7*after.collected.size+
        after.collected.size*(157+7*after.collected.size) ∧
      X86ReturnCleanup.Prefix FloorCaller.cm E1M1AimProgramLink.program [] n third out ∧
      q.world.pathTraverse thing.x thing.y (thing.attackEndpoint (angle facing) (Fixed.ofInt 1024)).1
        (thing.attackEndpoint (angle facing) (Fixed.ofInt 1024)).2 3 (fun _ _ => true)=.ok traced ∧
      q.world.aimLineAttack shooter (angle facing) (Fixed.ofInt 1024)=.ok answer ∧
      E1M1AimCallerRegisters.Restores third.core out ∧ out.pc=0x2d819 ∧
      E1M1AimActorCaller.Image after.collected (resolve q.lines q.objects) out answer ∧
      E1M1BulletAim.ProbeResult out.core answer ∧
      (∀ a∈watched, load32 out.core.memory a=load32 s.memory a) ∧
      E1M1AimStampImage.Image third.core.memory out.core.memory q.lines ((q.epoch+1)+1)
        (history cfg (Array.replicate q.world.lines.size false) cells) := by
  let cfg := context q thing facing
  have preparedData := prepared q s third thing facing _ h request tables data
    (fun a ha => kept a (covered a ha)) (fun a ha => watchedRead a (covered a ha))
  have entry := inputs q s third thing facing _ h request preparedData epoch fresh
  have commonNext : Common cfg :=
    ⟨common.mapLayout,common.stamps,common.returns,common.epochSafe,common.stampSafe,
      common.locals,common.cursor,common.records,common.dimension⟩
  have payloads : ∀ c∈route q pick thing facing xout yout, inside cfg c=true →
      E1M1QueryImages.Payload third.core.memory cfg c ∧ E1M1AimPreRayMemory.PayloadSafe third.core cfg c := by
    intro c member _
    obtain ⟨v,p⟩ := preparedData.payloads c member
    exact ⟨⟨v.encoded,v.back,v.objects,v.linked,v.selection⟩,
      ⟨p.lines,p.back,p.objects,p.links,p.global,p.selected⟩⟩
  have returnNext := E1M1AimRetryData.safe s third.core _ request.stack returnSafe
  rw [←request.stack] at returnNext
  obtain ⟨after,traced,out,answer,n,hn,run,pathSource,aimSource,restored,target,related,words,stampImage,_⟩ :=
    E1M1AimActorStampCall.execution cfg pick third.core third.flags thing (angle facing) (Fixed.ofInt 1024)
      entry shooter shooterValue (by decide) profile xout yout okX okY commonNext height statics scenes payloads
      ⟨separated.cursor,separated.records⟩
      (E1M1AimRetryCatalog.callback cfg s third.core request.stack
        ⟨callbackSafe.initial,callbackSafe.walk,callbackSafe.records⟩) cursorCall room portals walls who
      (by
        intro grid stamps after source
        obtain ⟨catalog,model,coverage⟩ := initial grid stamps after source
        exact ⟨E1M1AimRetryCatalog.initial cfg s third.core q.world shooter after.collected portals walls who
          request.stack request.actor catalog (fun a ha => kept a (coverage a ha)),model⟩)
      (E1M1AimRetryCatalog.saved s third.core request.stack savedSafe) returnNext watched
      (fun a ha => E1M1AimRetryCatalog.read q s third.core a request.stack (watchedRead a ha))
      (fun a ha => E1M1AimSavedWords.transport _ _ a rfl (watchedSafe a ha)) stampSafe
      (fun a ha => E1M1AimSavedWords.transport _ _ a rfl (stampProtected a ha))
  rw [OriginalPathXStep.at_pc _ _ request.pc] at run
  have pc : out.pc=0x2d819 := by rw [restored.pc,request.returnWord]; rfl
  exact ⟨after,traced,out,answer,n,hn,run,pathSource,aimSource,restored,pc,target,related,
    fun a ha => (words a ha).trans (kept a ha),stampImage⟩
end Doom.Proofs.E1M1AimActorThirdCall
