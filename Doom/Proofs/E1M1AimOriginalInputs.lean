import Doom.Proofs.E1M1AimControllerSetup
import Doom.Proofs.E1M1AimActorPairController
import Doom.Proofs.E1M1AimActorThirdCall
import Doom.Proofs.E1M1AimActorObservation
import Doom.Proofs.E1M1AimSelectedCall
import Doom.Proofs.E1M1AimControllerTarget
import Doom.Proofs.E1M1AimControllerData
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimOriginalInputs
open Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1CellWalkInvariant (Context Cell Common State)
open E1M1MixedCellWalk (inside Admitted Images budget bound history)
open E1M1GridRoute (sourceRoute)
open E1M1QueryCollection (path)
open E1M1QueryCallback (CallbackSafe)
open E1M1AimCatalog (Portal)
open E1M1AimQueryCaller (Source)
open E1M1ThingFinish (resolve)
open E1M1AimRetryGeometry (nextAngle)
open E1M1AimRetryInputs (reads Prepared prepared)
open E1M1AimNextContext (context route)
attribute [local irreducible] load32 store32 SolidThing.shootHeight

open E1M1AimControllerInputs (layout SafeReads)

/-- Continuous execution from P_BulletSlope entry through its actual return,
with matching production slope, exact selected actor pointer and restored caller.
No target, query answer, or actor-kind conclusion is added as an input premise.
All input memory predicates now refer to original entry memory. A pure register
layout expresses future stack guards; explicit separation protects each input
read from the five real prologue writes. Reachability remains an obligation. -/
theorem execution (q : Context) (pick : Int32 → Int32 → Cell)
    (s : X86Memory.State) (f : Option Flags) (thing : SolidThing) (angle : Angle)
    (h : E1M1AimSetupEntry.Inputs q (layout s angle) thing angle (Fixed.ofInt 1024))
    (shooter : Nat) (shooterValue : q.world.things[shooter]?=some thing)
    (profile : E1M1QuerySource.supported q.world=true)
    (xout yout : Int32 × Fixed × Fixed)
    (okX : (path q thing.x thing.y (thing.attackEndpoint angle (Fixed.ofInt 1024)).1 (thing.attackEndpoint angle (Fixed.ofInt 1024)).2).xStep=.ok xout)
    (okY : (path q thing.x thing.y (thing.attackEndpoint angle (Fixed.ofInt 1024)).1 (thing.attackEndpoint angle (Fixed.ofInt 1024)).2).yStep=.ok yout)
    (common : Common q) (height : q.world.grid.height=q.height)
    (statics : ∀ c∈sourceRoute pick 64 (E1M1FiringGridState.initial (path q thing.x thing.y (thing.attackEndpoint angle (Fixed.ofInt 1024)).1 (thing.attackEndpoint angle (Fixed.ofInt 1024)).2) xout yout), Admitted q c)
    (scenes : ∀ c∈sourceRoute pick 64 (E1M1FiringGridState.initial (path q thing.x thing.y (thing.attackEndpoint angle (Fixed.ofInt 1024)).1 (thing.attackEndpoint angle (Fixed.ofInt 1024)).2) xout yout),
      inside q c=true → E1M1CellLineSource.SceneLines q c)
    (payloads : ∀ c∈sourceRoute pick 64 (E1M1FiringGridState.initial (path q thing.x thing.y (thing.attackEndpoint angle (Fixed.ofInt 1024)).1 (thing.attackEndpoint angle (Fixed.ofInt 1024)).2) xout yout),
      inside q c=true → E1M1QueryImages.Payload s.memory q c ∧ E1M1AimPreRayMemory.PayloadSafe (layout s angle) q c ∧
      SafeReads s (E1M1AimRetryData.cellReads q c))
    (separated : E1M1TraversalEntry.Protected q)
    (callbackSafe : CallbackSafe q (E1M1AimPreRayMemory.layout (layout s angle)))
    (cursorCall : Apart 0x2c028 (q.sp-140))
    (room : budget q (sourceRoute pick 64 (E1M1FiringGridState.initial (path q thing.x thing.y (thing.attackEndpoint angle (Fixed.ofInt 1024)).1 (thing.attackEndpoint angle (Fixed.ofInt 1024)).2) xout yout))≤128)
    (portals : Nat → Option Portal) (walls : Nat → Prop) (who : Word)
    (initial : ∀ grid stamps after,
      E1M1LiveWalk.source q.world q.trace 64
        (E1M1FiringGridState.initial (path q thing.x thing.y (thing.attackEndpoint angle (Fixed.ofInt 1024)).1 (thing.attackEndpoint angle (Fixed.ofInt 1024)).2) xout yout)
        (Array.replicate q.world.lines.size false) {trace:=q.trace}=
        .ok (E1M1LoopReplay.pack grid stamps after) →
      E1M1AimPreRayCatalog.Initial q (layout s angle) q.world shooter after.collected portals walls who ∧
      SafeReads s (E1M1AimRetryCatalog.reads after.collected (resolve q.lines q.objects) portals) ∧
      ∃ path, Source q q.world shooter thing after path (Fixed.ofInt 1024) portals walls)
    (savedSafe : E1M1AimCallerRegisters.SavedSafe (layout s angle))
    (returnSafe : E1M1PathMapQuery.Safe (layout s angle) ((layout s angle).regs 4))
    (nextPick : Int32 → Int32 → Cell) (nextX nextY : Int32 × Fixed × Fixed)
    (tables : ThrustTables s.memory)
    (nextData : ∀ c∈(route q nextPick thing angle false nextX nextY), E1M1QueryImages.Payload s.memory q c ∧ E1M1AimPreRayMemory.PayloadSafe (layout s angle) q c ∧
      SafeReads s (E1M1AimRetryData.cellReads q c))
    (extra : List Word)
    (watchedRead : ∀ addr∈(reads q (layout s angle) (nextAngle false angle) (route q nextPick thing angle false nextX nextY) ++ extra), E1M1AimPreRayMemory.Read q (layout s angle) addr)
    (watchedSafe : ∀ addr∈(reads q (layout s angle) (nextAngle false angle) (route q nextPick thing angle false nextX nextY) ++ extra), E1M1AimSavedWords.Protect (E1M1AimQueryCatalog.view q (layout s angle)) addr)
    (retrySafe : ∀ addr∈(reads q (layout s angle) (nextAngle false angle) (route q nextPick thing angle false nextX nextY) ++ extra), Apart addr 0x2c0c0 ∧ Apart addr ((layout s angle).regs 4))
    (stampSafe : ∀ a∈E1M1AimStampQuery.stampWords q.lines 475, E1M1AimEntryFrame.SafeWord (q.sp-112) a)
    (stampProtected : ∀ a∈E1M1AimStampQuery.stampWords q.lines 475,
      E1M1AimSavedWords.Protect (E1M1AimQueryCatalog.view q (layout s angle)) a)
    (stampRetry : ∀ a∈E1M1AimStampQuery.stampWords q.lines 475, Apart a 0x2c0c0 ∧ Apart a ((layout s angle).regs 4))
    (before : E1M1AimStampImage.Fresh s.memory q.lines (q.epoch+1) 475)
    (beforeTwo : E1M1AimStampImage.Fresh s.memory q.lines ((q.epoch+1)+1) 475)
    (nextOkX : (path q thing.x thing.y (thing.attackEndpoint (nextAngle false angle) (Fixed.ofInt 1024)).1
      (thing.attackEndpoint (nextAngle false angle) (Fixed.ofInt 1024)).2).xStep=.ok nextX)
    (nextOkY : (path q thing.x thing.y (thing.attackEndpoint (nextAngle false angle) (Fixed.ofInt 1024)).1
      (thing.attackEndpoint (nextAngle false angle) (Fixed.ofInt 1024)).2).yStep=.ok nextY)
    (nextStatics : ∀ c∈route q nextPick thing angle false nextX nextY, Admitted (context q thing angle false) c)
    (nextScenes : ∀ c∈route q nextPick thing angle false nextX nextY,
      inside (context q thing angle false) c=true → E1M1CellLineSource.SceneLines (context q thing angle false) c)
    (nextRoom : budget (context q thing angle false) (route q nextPick thing angle false nextX nextY)≤128)
    (nextPortals : Nat → Option Portal) (nextWalls : Nat → Prop)
    (nextInitial : ∀ grid stamps after,
      E1M1LiveWalk.source q.world (context q thing angle false).trace 64
        (E1M1FiringGridState.initial (path q thing.x thing.y
          (thing.attackEndpoint (nextAngle false angle) (Fixed.ofInt 1024)).1
          (thing.attackEndpoint (nextAngle false angle) (Fixed.ofInt 1024)).2) nextX nextY)
        (Array.replicate q.world.lines.size false) {trace:=(context q thing angle false).trace}=
        .ok (E1M1LoopReplay.pack grid stamps after) →
      E1M1AimPreRayCatalog.Initial (context q thing angle false) (layout s angle) q.world shooter after.collected nextPortals nextWalls who ∧
      SafeReads s (E1M1AimRetryCatalog.reads after.collected (resolve q.lines q.objects) nextPortals) ∧
      (∃ traced, Source (context q thing angle false) q.world shooter thing after traced (Fixed.ofInt 1024) nextPortals nextWalls) ∧
      (∀ a∈E1M1AimRetryCatalog.reads after.collected (resolve q.lines q.objects) nextPortals,
        a∈(reads q (layout s angle) (nextAngle false angle) (route q nextPick thing angle false nextX nextY) ++ extra)))
    (thirdPick : Int32 → Int32 → Cell) (thirdX thirdY : Int32 × Fixed × Fixed)
    (thirdOkX : (path q thing.x thing.y
      (thing.attackEndpoint (E1M1AimThirdCall.angle angle) (Fixed.ofInt 1024)).1
      (thing.attackEndpoint (E1M1AimThirdCall.angle angle) (Fixed.ofInt 1024)).2).xStep=.ok thirdX)
    (thirdOkY : (path q thing.x thing.y
      (thing.attackEndpoint (E1M1AimThirdCall.angle angle) (Fixed.ofInt 1024)).1
      (thing.attackEndpoint (E1M1AimThirdCall.angle angle) (Fixed.ofInt 1024)).2).yStep=.ok thirdY)
    (thirdStatics : ∀ c∈E1M1AimThirdCall.route q thirdPick thing angle thirdX thirdY,
      Admitted (E1M1AimThirdCall.context q thing angle) c)
    (thirdScenes : ∀ c∈E1M1AimThirdCall.route q thirdPick thing angle thirdX thirdY,
      inside (E1M1AimThirdCall.context q thing angle) c=true →
        E1M1CellLineSource.SceneLines (E1M1AimThirdCall.context q thing angle) c)
    (thirdData : ∀ c∈E1M1AimThirdCall.route q thirdPick thing angle thirdX thirdY,
      E1M1QueryImages.Payload s.memory q c ∧ E1M1AimPreRayMemory.PayloadSafe (layout s angle) q c ∧
      SafeReads s (E1M1AimRetryData.cellReads q c))
    (thirdRoom : budget (E1M1AimThirdCall.context q thing angle)
      (E1M1AimThirdCall.route q thirdPick thing angle thirdX thirdY)≤128)
    (thirdPortals : Nat → Option Portal) (thirdWalls : Nat → Prop)
    (thirdCovered : ∀ a∈reads q (layout s angle) (E1M1AimThirdCall.angle angle)
        (E1M1AimThirdCall.route q thirdPick thing angle thirdX thirdY),
      a∈(reads q (layout s angle) (nextAngle false angle) (route q nextPick thing angle false nextX nextY) ++ extra))
    (thirdInitial : ∀ grid stamps after,
      E1M1LiveWalk.source q.world (E1M1AimThirdCall.context q thing angle).trace 64
        (E1M1FiringGridState.initial (path q thing.x thing.y
          (thing.attackEndpoint (E1M1AimThirdCall.angle angle) (Fixed.ofInt 1024)).1
          (thing.attackEndpoint (E1M1AimThirdCall.angle angle) (Fixed.ofInt 1024)).2) thirdX thirdY)
        (Array.replicate q.world.lines.size false) {trace:=(E1M1AimThirdCall.context q thing angle).trace}=
        .ok (E1M1LoopReplay.pack grid stamps after) →
      E1M1AimPreRayCatalog.Initial (E1M1AimThirdCall.context q thing angle) (layout s angle) q.world shooter
        after.collected thirdPortals thirdWalls who ∧
      SafeReads s (E1M1AimRetryCatalog.reads after.collected (resolve q.lines q.objects) thirdPortals) ∧
      (∃ traced, Source (E1M1AimThirdCall.context q thing angle) q.world shooter thing after traced
        (Fixed.ofInt 1024) thirdPortals thirdWalls) ∧
      (∀ a∈E1M1AimRetryCatalog.reads after.collected (resolve q.lines q.objects) thirdPortals,
        a∈(reads q (layout s angle) (nextAngle false angle) (route q nextPick thing angle false nextX nextY) ++ extra)))
    (stackCovered : ∀ a∈E1M1AimControllerFrame.slots (layout s angle),
      a∈(reads q (layout s angle) (nextAngle false angle) (route q nextPick thing angle false nextX nextY) ++ extra))
    (setupSafe : SafeReads s (E1M1AimControllerSetup.reads q s angle))
    (tableSafe : E1M1AimControllerData.TableSafe s)
    (freshSafe : ∀ j<475, ∀ b∈E1M1AimControllerEntry.writes s,
      Apart (OriginalLineVisits.stamp q.lines j) b)
    (value : load32 s.memory (s.regs 0+32)=angle.raw.toBitVec)
    (angleSafe : ∀ b∈OriginalBulletSlope.saveWrites s, Apart (s.regs 0+32) b) :
    ∃ (selected : AutoAim.Selection) (out : X86Control.State) (n : Nat),
      q.world.bulletAim shooter angle=.ok selected ∧
      X86ReturnCleanup.Prefix FloorCaller.cm E1M1AimProgramLink.program [] n ⟨s,f,0x2d7c0⟩ out ∧
      load32 out.core.memory 0x2c0c0=selected.slope.raw.toBitVec ∧
      (out.core.regs 4=s.regs 4+4 ∧ out.pc=(load32 s.memory (s.regs 4)).toNat ∧
      out.core.regs 5=s.regs 5 ∧ out.core.regs 7=s.regs 7 ∧
      out.core.regs 6=s.regs 6 ∧ out.core.regs 2=s.regs 2 ∧
      out.core.regs 1=s.regs 1 ∧ out.core.regs 3=s.regs 3) ∧
      E1M1AimActorObservation.Observed q.objects out selected := by
  have regs := E1M1AimControllerInputs.registers s f angle value angleSafe
  have stack := congrFun regs 4
  have readEq (probe : Angle) (cells : List Cell) :
      reads q (E1M1AimControllerEntry.entry s f).core probe cells=reads q (layout s angle) probe cells := by
    simp only [E1M1AimRetryInputs.reads,E1M1AimRetryGeometry.reads,OriginalAimSetup.actorReads,congrFun regs 0]
  have hAt : E1M1AimSetupEntry.Inputs q (E1M1AimControllerEntry.entry s f).core thing angle (Fixed.ofInt 1024) := E1M1AimControllerSetup.setup q s f thing angle regs h tables setupSafe
  have payloadsAt : ∀ c∈sourceRoute pick 64 (E1M1FiringGridState.initial (path q thing.x thing.y (thing.attackEndpoint angle (Fixed.ofInt 1024)).1 (thing.attackEndpoint angle (Fixed.ofInt 1024)).2) xout yout),
      inside q c=true → E1M1QueryImages.Payload (E1M1AimControllerEntry.entry s f).core.memory q c ∧ E1M1AimPreRayMemory.PayloadSafe (E1M1AimControllerEntry.entry s f).core q c := fun c member used => E1M1AimControllerInputs.payload q c s f angle regs
    ⟨(payloads c member used).1,(payloads c member used).2.1⟩ (payloads c member used).2.2
  have nextDataAt : ∀ c∈(route q nextPick thing angle false nextX nextY), E1M1QueryImages.Payload (E1M1AimControllerEntry.entry s f).core.memory q c ∧ E1M1AimPreRayMemory.PayloadSafe (E1M1AimControllerEntry.entry s f).core q c := fun c member => E1M1AimControllerInputs.payload q c s f angle regs
    ⟨(nextData c member).1,(nextData c member).2.1⟩ (nextData c member).2.2
  have thirdDataAt : ∀ c∈E1M1AimThirdCall.route q thirdPick thing angle thirdX thirdY,
      E1M1QueryImages.Payload (E1M1AimControllerEntry.entry s f).core.memory q c ∧ E1M1AimPreRayMemory.PayloadSafe (E1M1AimControllerEntry.entry s f).core q c := fun c member => E1M1AimControllerInputs.payload q c s f angle regs
    ⟨(thirdData c member).1,(thirdData c member).2.1⟩ (thirdData c member).2.2
  have initialAt : ∀ grid stamps after,
      E1M1LiveWalk.source q.world q.trace 64
        (E1M1FiringGridState.initial (path q thing.x thing.y (thing.attackEndpoint angle (Fixed.ofInt 1024)).1 (thing.attackEndpoint angle (Fixed.ofInt 1024)).2) xout yout)
        (Array.replicate q.world.lines.size false) {trace:=q.trace}=
        .ok (E1M1LoopReplay.pack grid stamps after) →
      E1M1AimPreRayCatalog.Initial q (E1M1AimControllerEntry.entry s f).core q.world shooter after.collected portals walls who ∧
      ∃ path, Source q q.world shooter thing after path (Fixed.ofInt 1024) portals walls := fun grid stamps after source =>
    ⟨E1M1AimControllerInputs.catalog q s f angle q.world shooter after.collected portals walls who regs
      (initial grid stamps after source).1 (initial grid stamps after source).2.1,
      (initial grid stamps after source).2.2⟩
  have nextInitialAt : ∀ grid stamps after,
      E1M1LiveWalk.source q.world (context q thing angle false).trace 64
        (E1M1FiringGridState.initial (path q thing.x thing.y
          (thing.attackEndpoint (nextAngle false angle) (Fixed.ofInt 1024)).1
          (thing.attackEndpoint (nextAngle false angle) (Fixed.ofInt 1024)).2) nextX nextY)
        (Array.replicate q.world.lines.size false) {trace:=(context q thing angle false).trace}=
        .ok (E1M1LoopReplay.pack grid stamps after) →
      E1M1AimPreRayCatalog.Initial (context q thing angle false) (E1M1AimControllerEntry.entry s f).core q.world shooter after.collected nextPortals nextWalls who ∧
      (∃ traced, Source (context q thing angle false) q.world shooter thing after traced (Fixed.ofInt 1024) nextPortals nextWalls) ∧
      (∀ a∈E1M1AimRetryCatalog.reads after.collected (resolve q.lines q.objects) nextPortals,
        a∈(reads q (E1M1AimControllerEntry.entry s f).core (nextAngle false angle) (route q nextPick thing angle false nextX nextY) ++ extra)) := by
    intro grid stamps after source
    obtain ⟨catalog,readSafe,model,covered⟩ := nextInitial grid stamps after source
    refine ⟨E1M1AimControllerInputs.catalog (context q thing angle false) s f angle q.world shooter
      after.collected nextPortals nextWalls who regs catalog readSafe,model,?_⟩
    simpa only [readEq] using covered
  have thirdInitialAt : ∀ grid stamps after,
      E1M1LiveWalk.source q.world (E1M1AimThirdCall.context q thing angle).trace 64
        (E1M1FiringGridState.initial (path q thing.x thing.y
          (thing.attackEndpoint (E1M1AimThirdCall.angle angle) (Fixed.ofInt 1024)).1
          (thing.attackEndpoint (E1M1AimThirdCall.angle angle) (Fixed.ofInt 1024)).2) thirdX thirdY)
        (Array.replicate q.world.lines.size false) {trace:=(E1M1AimThirdCall.context q thing angle).trace}=
        .ok (E1M1LoopReplay.pack grid stamps after) →
      E1M1AimPreRayCatalog.Initial (E1M1AimThirdCall.context q thing angle) (E1M1AimControllerEntry.entry s f).core q.world shooter
        after.collected thirdPortals thirdWalls who ∧
      (∃ traced, Source (E1M1AimThirdCall.context q thing angle) q.world shooter thing after traced
        (Fixed.ofInt 1024) thirdPortals thirdWalls) ∧
      (∀ a∈E1M1AimRetryCatalog.reads after.collected (resolve q.lines q.objects) thirdPortals,
        a∈(reads q (E1M1AimControllerEntry.entry s f).core (nextAngle false angle) (route q nextPick thing angle false nextX nextY) ++ extra)) := by
    intro grid stamps after source
    obtain ⟨catalog,readSafe,model,covered⟩ := thirdInitial grid stamps after source
    refine ⟨E1M1AimControllerInputs.catalog (E1M1AimThirdCall.context q thing angle) s f angle q.world shooter
      after.collected thirdPortals thirdWalls who regs catalog readSafe,model,?_⟩
    simpa only [readEq] using covered
  have callbackAt : CallbackSafe q (E1M1AimPreRayMemory.layout (E1M1AimControllerEntry.entry s f).core) := E1M1AimRetryCatalog.callback q (layout s angle) _ stack callbackSafe
  have savedAt : E1M1AimCallerRegisters.SavedSafe (E1M1AimControllerEntry.entry s f).core := E1M1AimRetryCatalog.saved (layout s angle) _ stack savedSafe
  have returnAt := E1M1AimRetryData.safe (layout s angle) _ _ stack returnSafe
  rw [←stack] at returnAt
  have watchedReadAt : ∀ addr∈(reads q (E1M1AimControllerEntry.entry s f).core (nextAngle false angle) (route q nextPick thing angle false nextX nextY) ++ extra), E1M1AimPreRayMemory.Read q (E1M1AimControllerEntry.entry s f).core addr := by
    intro addr member
    apply E1M1AimRetryCatalog.read q (layout s angle) _ addr stack
    exact watchedRead addr (by simpa only [readEq] using member)
  have watchedSafeAt : ∀ addr∈(reads q (E1M1AimControllerEntry.entry s f).core (nextAngle false angle) (route q nextPick thing angle false nextX nextY) ++ extra), E1M1AimSavedWords.Protect (E1M1AimQueryCatalog.view q (E1M1AimControllerEntry.entry s f).core) addr := by
    intro addr member
    apply E1M1AimSavedWords.transport (E1M1AimQueryCatalog.view q (layout s angle)) _ addr rfl
    exact watchedSafe addr (by simpa only [readEq] using member)
  have retrySafeAt : ∀ addr∈(reads q (E1M1AimControllerEntry.entry s f).core (nextAngle false angle) (route q nextPick thing angle false nextX nextY) ++ extra), Apart addr 0x2c0c0 ∧ Apart addr ((E1M1AimControllerEntry.entry s f).core.regs 4) := by simpa only [readEq,stack] using retrySafe
  have stampProtectedAt : ∀ a∈E1M1AimStampQuery.stampWords q.lines 475,
      E1M1AimSavedWords.Protect (E1M1AimQueryCatalog.view q (E1M1AimControllerEntry.entry s f).core) a := fun a member => E1M1AimSavedWords.transport
    (E1M1AimQueryCatalog.view q (layout s angle))
    (E1M1AimQueryCatalog.view q (E1M1AimControllerEntry.entry s f).core) a rfl (stampProtected a member)
  have stampRetryAt : ∀ a∈E1M1AimStampQuery.stampWords q.lines 475, Apart a 0x2c0c0 ∧ Apart a ((E1M1AimControllerEntry.entry s f).core.regs 4) := by simpa only [stack] using stampRetry
  have thirdCoveredAt : ∀ a∈reads q (E1M1AimControllerEntry.entry s f).core (E1M1AimThirdCall.angle angle)
        (E1M1AimThirdCall.route q thirdPick thing angle thirdX thirdY),
      a∈(reads q (E1M1AimControllerEntry.entry s f).core (nextAngle false angle) (route q nextPick thing angle false nextX nextY) ++ extra) := by simpa only [readEq] using thirdCovered
  have stackCoveredAt : ∀ a∈E1M1AimControllerFrame.slots (E1M1AimControllerEntry.entry s f).core,
      a∈(reads q (E1M1AimControllerEntry.entry s f).core (nextAngle false angle) (route q nextPick thing angle false nextX nextY) ++ extra) := by
    simpa only [E1M1AimControllerFrame.slots,stack,readEq] using stackCovered
  exact E1M1AimActorController.execution
    q pick s f thing angle hAt shooter shooterValue profile xout yout okX okY common height statics scenes payloadsAt separated callbackAt cursorCall room portals walls who initialAt savedAt returnAt nextPick nextX nextY tables nextDataAt extra watchedReadAt watchedSafeAt retrySafeAt stampSafe stampProtectedAt stampRetryAt before beforeTwo nextOkX nextOkY nextStatics nextScenes nextRoom nextPortals nextWalls nextInitialAt thirdPick thirdX thirdY thirdOkX thirdOkY thirdStatics thirdScenes thirdDataAt thirdRoom thirdPortals thirdWalls thirdCoveredAt thirdInitialAt stackCoveredAt tableSafe freshSafe value angleSafe
end Doom.Proofs.E1M1AimOriginalInputs
