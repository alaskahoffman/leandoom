import Doom.Proofs.E1M1AimActorStampQuery
import Doom.Proofs.E1M1AimStampCall
import Doom.Proofs.E1M1AimStampOrigin
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimActorStampCall
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

/-- Start before ray construction and carry the exact stamp image through the
complete source aim call and the authenticated original return chain. -/
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
    (returnSafe : E1M1PathMapQuery.Safe s (s.regs 4))
    (watched : List Word)
    (watchedRead : ∀ addr∈watched, E1M1AimPreRayMemory.Read q s addr)
    (watchedSafe : ∀ addr∈watched, E1M1AimSavedWords.Protect (E1M1AimQueryCatalog.view q s) addr)
    (stampSafe : ∀ a∈E1M1AimStampQuery.stampWords q.lines 475, E1M1AimEntryFrame.SafeWord (q.sp-112) a)
    (stampProtected : ∀ a∈E1M1AimStampQuery.stampWords q.lines 475,
      E1M1AimSavedWords.Protect (E1M1AimQueryCatalog.view q s) a) :
    let g := E1M1FiringGridState.initial (path q thing.x thing.y (thing.attackEndpoint angle distance).1 (thing.attackEndpoint angle distance).2) xout yout
    let cells := sourceRoute pick 64 g
    ∃ (after traced : PathResult) (out : X86Control.State) (answer : AimResult) (n : Nat),
      n≤264+bound q cells+7*after.collected.size+
        after.collected.size*(157+7*after.collected.size) ∧
      X86ReturnCleanup.Prefix FloorCaller.cm E1M1AimProgramLink.program [] n ⟨s,f,0x2bb80⟩ out ∧
      q.world.pathTraverse thing.x thing.y (thing.attackEndpoint angle distance).1 (thing.attackEndpoint angle distance).2 3 (fun _ _ => true)=.ok traced ∧
      q.world.aimLineAttack shooter angle distance=.ok answer ∧
      E1M1AimCallerRegisters.Restores s out ∧
      E1M1AimActorCaller.Image after.collected (resolve q.lines q.objects) out answer ∧
      E1M1BulletAim.ProbeResult out.core answer ∧
      (∀ addr∈watched, load32 out.core.memory addr=load32 s.memory addr) ∧
      E1M1AimStampImage.Image s.memory out.core.memory q.lines q.epoch
        (history q (Array.replicate q.world.lines.size false) cells) ∧
      (E1M1AimStampImage.Fresh s.memory q.lines (q.epoch+1) 475 →
        E1M1AimStampImage.Fresh out.core.memory q.lines (load32 out.core.memory 0x13580+1) 475) := by
  have data : ∀ c∈sourceRoute pick 64 (E1M1FiringGridState.initial
      (path q thing.x thing.y (thing.attackEndpoint angle distance).1 (thing.attackEndpoint angle distance).2) xout yout),
      inside q c=true → E1M1QueryImages.Payload (traversal s).core.memory q c ∧
        E1M1QueryImages.Protected (traversal s).core q c := by
    intro c member used
    exact E1M1AimPreRayMemory.payload s q c (payloads c member used).1 (payloads c member used).2
  have setup := E1M1AimSetupLink.execution s f
  have entry := E1M1AimSetupEntry.entry q s thing angle distance h
  have argument := congrArg (fun t => t.2.2) (E1M1AimSetupEntry.call s thing angle distance _ _ h.geometry)
  obtain ⟨after,traced,out,answer,n,hn,run,pathSource,aimSource,value,restored,image,related,kept,stampImage,_⟩ :=
    E1M1AimActorStampQuery.execution q pick (traversal s).core (traversal s).flags thing.x thing.y
      (thing.attackEndpoint angle distance).1 (thing.attackEndpoint angle distance).2
      entry profile xout yout okX okY common height statics scenes data separated
      (E1M1AimPreRayMemory.callback q s callbackSafe) argument cursorCall room
      q.world shooter thing distance portals walls who (by
        intro grid stamps after source
        obtain ⟨catalog,traced,model⟩ := initial grid stamps after source
        have remaining := E1M1AimPreRayCatalog.remaining q s q.world shooter thing angle distance
          after.collected portals walls who h.geometry catalog
        exact ⟨E1M1AimSetupCatalog.initial q s q.world shooter thing angle distance after.collected
          portals walls who h remaining,traced,model⟩)
      watched (fun addr member => E1M1AimPreRayMemory.later q s addr (watchedRead addr member).2)
      (fun addr member => E1M1AimSavedWords.transport
        (E1M1AimQueryCatalog.view q s) (E1M1AimQueryCatalog.view q (traversal s).core) addr
        (by simp [E1M1AimQueryCatalog.view,put,write]) (watchedSafe addr member))
      stampSafe (fun a member => E1M1AimSavedWords.transport
        (E1M1AimQueryCatalog.view q s) (E1M1AimQueryCatalog.view q (traversal s).core) a
        (by simp [E1M1AimQueryCatalog.view,put,write]) (stampProtected a member))
  have historySize : (history q (Array.replicate q.world.lines.size false)
      (sourceRoute pick 64 (E1M1FiringGridState.initial
        (path q thing.x thing.y (thing.attackEndpoint angle distance).1 (thing.attackEndpoint angle distance).2)
        xout yout))).size=475 := by
    rw [E1M1AimStampOrigin.history_size,Array.size_replicate,h.lineCount]
  have originalImage := E1M1AimStampOrigin.preray q s thing angle distance h out _ historySize stampImage
  refine ⟨after,traced,out,answer,36+n,by omega,setup.trans run,pathSource,
    E1M1AimEntryQuery.production q.world shooter thing angle distance traced answer
      shooterValue positive pathSource aimSource,
    E1M1AimCallerRegisters.restores q s out h.stack savedSafe returnSafe restored,image,related,
    fun addr member => (kept addr member).trans
      (E1M1PathMapQuery.traversal_frame s addr (watchedRead addr member).1),originalImage,?_⟩
  intro fresh
  have nextFresh := E1M1AimStampImage.next_fresh s.memory out.core.memory q.lines q.epoch _ originalImage
    (by simpa only [historySize] using fresh)
  simpa only [historySize] using nextFresh

/-- A source miss carries that same history through the real retry decision and CALL. -/
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
    (watched : List Word)
    (watchedRead : ∀ addr∈watched, E1M1AimPreRayMemory.Read q s addr)
    (watchedSafe : ∀ addr∈watched, E1M1AimSavedWords.Protect (E1M1AimQueryCatalog.view q s) addr)
    (retrySafe : ∀ addr∈watched, Apart addr 0x2c0c0 ∧ Apart addr (s.regs 4))
    (second : Bool)
    (controller : s.regs 6=s.regs 0 ∧ s.regs 1=angle.raw.toBitVec)
    (resume : (load32 s.memory (s.regs 4)).toNat=if second then 0x2d7f8 else 0x2d7d5)
    (stampSafe : ∀ a∈E1M1AimStampQuery.stampWords q.lines 475, E1M1AimEntryFrame.SafeWord (q.sp-112) a)
    (stampProtected : ∀ a∈E1M1AimStampQuery.stampWords q.lines 475,
      E1M1AimSavedWords.Protect (E1M1AimQueryCatalog.view q s) a)
    (stampRetry : ∀ a∈E1M1AimStampQuery.stampWords q.lines 475, Apart a 0x2c0c0 ∧ Apart a (s.regs 4)) :
    let g := E1M1FiringGridState.initial (path q thing.x thing.y (thing.attackEndpoint angle distance).1 (thing.attackEndpoint angle distance).2) xout yout
    let cells := sourceRoute pick 64 g
    ∃ (after traced : PathResult) (out : X86Control.State) (answer : AimResult) (n : Nat),
      n≤264+bound q cells+7*after.collected.size+
        after.collected.size*(157+7*after.collected.size) ∧
      X86ReturnCleanup.Prefix FloorCaller.cm E1M1AimProgramLink.program [] n ⟨s,f,0x2bb80⟩ out ∧
      q.world.pathTraverse thing.x thing.y (thing.attackEndpoint angle distance).1 (thing.attackEndpoint angle distance).2 3 (fun _ _ => true)=.ok traced ∧
      q.world.aimLineAttack shooter angle distance=.ok answer ∧
      E1M1AimCallerRegisters.Restores s out ∧
      E1M1AimActorCaller.Image after.collected (resolve q.lines q.objects) out answer ∧
      E1M1BulletAim.ProbeResult out.core answer ∧
      (∀ addr∈watched, load32 out.core.memory addr=load32 s.memory addr) ∧
      E1M1AimStampImage.Image s.memory out.core.memory q.lines q.epoch
        (history q (Array.replicate q.world.lines.size false) cells) ∧
      (E1M1AimStampImage.Fresh s.memory q.lines (q.epoch+1) 475 →
        E1M1AimStampImage.Fresh out.core.memory q.lines (load32 out.core.memory 0x13580+1) 475) ∧
      (answer.target=none →
        X86ReturnCleanup.Prefix FloorCaller.cm E1M1AimProgramLink.program []
          (n+(4+(if second then 4 else 5))) ⟨s,f,0x2bb80⟩ (E1M1BulletAim.nextQuery second out.core) ∧
        E1M1AimRetryRequest.Request second s (E1M1BulletAim.nextQuery second out.core) ∧
        (E1M1BulletAim.nextQuery second out.core).core.regs 0=s.regs 0 ∧
        (E1M1BulletAim.nextQuery second out.core).core.regs 2=
          angle.raw.toBitVec+(if second then 0xf8000000 else 0x04000000) ∧
        (∀ addr∈watched, load32 (E1M1BulletAim.nextQuery second out.core).core.memory addr=
          load32 s.memory addr) ∧
        E1M1AimStampImage.Image s.memory (E1M1BulletAim.nextQuery second out.core).core.memory q.lines q.epoch
          (history q (Array.replicate q.world.lines.size false) cells) ∧
        (E1M1AimStampImage.Fresh s.memory q.lines (q.epoch+1) 475 →
          E1M1AimStampImage.Fresh (E1M1BulletAim.nextQuery second out.core).core.memory q.lines
            (load32 (E1M1BulletAim.nextQuery second out.core).core.memory 0x13580+1) 475)) := by
  obtain ⟨after,traced,out,answer,n,hn,run,pathSource,aimSource,restored,image,related,kept,stampImage,freshOut⟩ :=
    execution q pick s f thing angle distance h shooter shooterValue positive profile xout yout okX okY
      common height statics scenes payloads separated callbackSafe cursorCall room portals walls who initial savedSafe returnSafe watched watchedRead watchedSafe stampSafe stampProtected
  refine ⟨after,traced,out,answer,n,hn,run,pathSource,aimSource,restored,image,related,kept,stampImage,freshOut,?_⟩
  intro miss
  have request := E1M1AimRetryRequest.request second s out restored
  have historySize : (history q (Array.replicate q.world.lines.size false)
      (sourceRoute pick 64 (E1M1FiringGridState.initial
        (path q thing.x thing.y (thing.attackEndpoint angle distance).1 (thing.attackEndpoint angle distance).2)
        xout yout))).size=475 := by
    rw [E1M1AimStampOrigin.history_size,Array.size_replicate,h.lineCount]
  have retryImage := E1M1AimStampQuery.transport s.memory out.core.memory _ q.lines q.epoch _ 475
    historySize stampImage (fun a member => E1M1AimRetryRequest.frame second out.core a (stampRetry a member).1
      (by simpa only [restored.stack,BitVec.add_sub_cancel] using (stampRetry a member).2))
  refine ⟨run.trans (E1M1AimRetryRequest.execution second out answer related miss (restored.pc.trans resume)),
    request,request.actor.trans controller.1,by rw [request.angle,controller.2],
    fun addr member => (E1M1AimRetryRequest.frame second out.core addr (retrySafe addr member).1
      (by simpa only [restored.stack,BitVec.add_sub_cancel] using (retrySafe addr member).2)).trans
        (kept addr member),retryImage,?_⟩
  intro fresh
  have nextFresh := E1M1AimStampImage.next_fresh s.memory _ q.lines q.epoch _ retryImage
    (by simpa only [historySize] using fresh)
  simpa only [historySize] using nextFresh
end Doom.Proofs.E1M1AimActorStampCall
