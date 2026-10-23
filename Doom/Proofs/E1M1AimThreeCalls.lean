import Doom.Proofs.E1M1AimThirdCall
import Doom.Proofs.E1M1AimMissZero
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimThreeCalls
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

/-- From the first actual aim-call entry, execute all required probes and the
controller return. Original-memory contracts remain explicit, but no executed
probe answer, reached callback state, or zero-on-miss premise is assumed. -/
theorem execution (q : Context) (pick : Int32 → Int32 → Cell)
    (s : X86Memory.State) (f : Option Flags) (thing : SolidThing) (angle : Angle)
    (h : E1M1AimSetupEntry.Inputs q s thing angle (Fixed.ofInt 1024))
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
      inside q c=true → E1M1QueryImages.Payload s.memory q c ∧ E1M1AimPreRayMemory.PayloadSafe s q c)
    (separated : E1M1TraversalEntry.Protected q)
    (callbackSafe : CallbackSafe q (E1M1AimPreRayMemory.layout s))
    (cursorCall : Apart 0x2c028 (q.sp-140))
    (room : budget q (sourceRoute pick 64 (E1M1FiringGridState.initial (path q thing.x thing.y (thing.attackEndpoint angle (Fixed.ofInt 1024)).1 (thing.attackEndpoint angle (Fixed.ofInt 1024)).2) xout yout))≤128)
    (portals : Nat → Option Portal) (walls : Nat → Prop) (who : Word)
    (initial : ∀ grid stamps after,
      E1M1LiveWalk.source q.world q.trace 64
        (E1M1FiringGridState.initial (path q thing.x thing.y (thing.attackEndpoint angle (Fixed.ofInt 1024)).1 (thing.attackEndpoint angle (Fixed.ofInt 1024)).2) xout yout)
        (Array.replicate q.world.lines.size false) {trace:=q.trace}=
        .ok (E1M1LoopReplay.pack grid stamps after) →
      E1M1AimPreRayCatalog.Initial q s q.world shooter after.collected portals walls who ∧
      ∃ path, Source q q.world shooter thing after path (Fixed.ofInt 1024) portals walls)
    (savedSafe : E1M1AimCallerRegisters.SavedSafe s)
    (returnSafe : E1M1PathMapQuery.Safe s (s.regs 4))
    (nextPick : Int32 → Int32 → Cell) (nextX nextY : Int32 × Fixed × Fixed)
    (tables : ThrustTables s.memory)
    (nextData : ∀ c∈(route q nextPick thing angle false nextX nextY), E1M1QueryImages.Payload s.memory q c ∧ E1M1AimPreRayMemory.PayloadSafe s q c)
    (extra : List Word)
    (watchedRead : ∀ addr∈(reads q s (nextAngle false angle) (route q nextPick thing angle false nextX nextY) ++ extra), E1M1AimPreRayMemory.Read q s addr)
    (watchedSafe : ∀ addr∈(reads q s (nextAngle false angle) (route q nextPick thing angle false nextX nextY) ++ extra), E1M1AimSavedWords.Protect (E1M1AimQueryCatalog.view q s) addr)
    (retrySafe : ∀ addr∈(reads q s (nextAngle false angle) (route q nextPick thing angle false nextX nextY) ++ extra), Apart addr 0x2c0c0 ∧ Apart addr (s.regs 4))
    (controller : s.regs 6=s.regs 0 ∧ s.regs 1=angle.raw.toBitVec)
    (resume : (load32 s.memory (s.regs 4)).toNat=0x2d7d5)
    (stampSafe : ∀ a∈E1M1AimStampQuery.stampWords q.lines 475, E1M1AimEntryFrame.SafeWord (q.sp-112) a)
    (stampProtected : ∀ a∈E1M1AimStampQuery.stampWords q.lines 475,
      E1M1AimSavedWords.Protect (E1M1AimQueryCatalog.view q s) a)
    (stampRetry : ∀ a∈E1M1AimStampQuery.stampWords q.lines 475, Apart a 0x2c0c0 ∧ Apart a (s.regs 4))
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
      E1M1AimPreRayCatalog.Initial (context q thing angle false) s q.world shooter after.collected nextPortals nextWalls who ∧
      (∃ traced, Source (context q thing angle false) q.world shooter thing after traced (Fixed.ofInt 1024) nextPortals nextWalls) ∧
      (∀ a∈E1M1AimRetryCatalog.reads after.collected (resolve q.lines q.objects) nextPortals,
        a∈(reads q s (nextAngle false angle) (route q nextPick thing angle false nextX nextY) ++ extra)))
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
      E1M1QueryImages.Payload s.memory q c ∧ E1M1AimPreRayMemory.PayloadSafe s q c)
    (thirdRoom : budget (E1M1AimThirdCall.context q thing angle)
      (E1M1AimThirdCall.route q thirdPick thing angle thirdX thirdY)≤128)
    (thirdPortals : Nat → Option Portal) (thirdWalls : Nat → Prop)
    (thirdCovered : ∀ a∈reads q s (E1M1AimThirdCall.angle angle)
        (E1M1AimThirdCall.route q thirdPick thing angle thirdX thirdY),
      a∈(reads q s (nextAngle false angle) (route q nextPick thing angle false nextX nextY) ++ extra))
    (thirdInitial : ∀ grid stamps after,
      E1M1LiveWalk.source q.world (E1M1AimThirdCall.context q thing angle).trace 64
        (E1M1FiringGridState.initial (path q thing.x thing.y
          (thing.attackEndpoint (E1M1AimThirdCall.angle angle) (Fixed.ofInt 1024)).1
          (thing.attackEndpoint (E1M1AimThirdCall.angle angle) (Fixed.ofInt 1024)).2) thirdX thirdY)
        (Array.replicate q.world.lines.size false) {trace:=(E1M1AimThirdCall.context q thing angle).trace}=
        .ok (E1M1LoopReplay.pack grid stamps after) →
      E1M1AimPreRayCatalog.Initial (E1M1AimThirdCall.context q thing angle) s q.world shooter
        after.collected thirdPortals thirdWalls who ∧
      (∃ traced, Source (E1M1AimThirdCall.context q thing angle) q.world shooter thing after traced
        (Fixed.ofInt 1024) thirdPortals thirdWalls) ∧
      (∀ a∈E1M1AimRetryCatalog.reads after.collected (resolve q.lines q.objects) thirdPortals,
        a∈(reads q s (nextAngle false angle) (route q nextPick thing angle false nextX nextY) ++ extra))) :
    ∃ (selected : AutoAim.Selection) (out : X86Control.State) (n : Nat),
      q.world.bulletAim shooter angle=.ok selected ∧
      X86ReturnCleanup.Prefix FloorCaller.cm E1M1AimProgramLink.program [] n ⟨s,f,0x2bb80⟩ out ∧
      load32 out.core.memory 0x2c0c0=selected.slope.raw.toBitVec := by
  obtain ⟨after,traced,out,answer,n,hn,run,pathSource,aimSource,restored,image,related,kept,
    stampImage,center,continueOnMiss⟩ :=
    E1M1AimPairController.execution q pick s f thing angle h shooter shooterValue profile
      xout yout okX okY common height statics scenes payloads separated callbackSafe cursorCall room
      portals walls who initial savedSafe returnSafe nextPick nextX nextY tables nextData extra
      watchedRead watchedSafe retrySafe controller resume stampSafe stampProtected stampRetry before
      beforeTwo nextOkX nextOkY nextStatics nextScenes nextRoom nextPortals nextWalls nextInitial
  cases targetEq : answer.target with
  | some id =>
    obtain ⟨source,whole,slope⟩ := center (by rw [targetEq]; rfl)
    exact ⟨_,_,_,source,whole,slope⟩
  | none =>
    obtain ⟨request,inputs,futureAfter,futurePath,finish,futureAnswer,m,hm,nextRun,twoRun,pathResult,
      aimResult,restoredNext,returned,target,result,words,exactImage,right,continueLeft⟩ := continueOnMiss targetEq
    cases rightEq : futureAnswer.target with
    | some id =>
      obtain ⟨source,whole,slope⟩ := right (by rw [rightEq]; rfl)
      exact ⟨_,_,_,source,whole,slope⟩
    | none =>
      obtain ⟨toThird,thirdRequest,pc,stack,actor,leftAngle,range,returnWord,thirdImage,thirdFresh,thirdWords⟩ :=
        continueLeft rightEq
      have request3 : E1M1AimThirdCall.Request s (E1M1BulletAim.nextQuery true finish.core) angle :=
        ⟨pc,stack,actor,leftAngle,range,returnWord⟩
      obtain ⟨lastAfter,lastPath,lastOut,lastAnswer,k,hk,lastRun,lastPathSource,lastAim,
        lastRestored,lastPc,lastImage,lastRelated,lastWords,lastStamps⟩ :=
        E1M1AimThirdCall.execution q thirdPick s (E1M1BulletAim.nextQuery true finish.core) thing angle h
          request3 thirdImage.counter thirdFresh shooter shooterValue profile thirdX thirdY thirdOkX thirdOkY
          common height thirdStatics thirdScenes tables thirdData separated callbackSafe cursorCall thirdRoom
          thirdPortals thirdWalls who _ thirdCovered thirdWords thirdInitial savedSafe returnSafe
          watchedRead watchedSafe stampSafe stampProtected
      obtain ⟨tailCount,tailBound,tailRun,tailSlope⟩ :=
        E1M1AimControllerExit.last lastOut lastAnswer lastRelated lastPc
      have query0 : BulletAim.query q.world shooter angle 0=.ok answer := by
        simpa only [BulletAim.query,UInt32.add_zero] using aimSource
      obtain ⟨selected,source,slope⟩ := E1M1BulletAim.last_correspondence q.world shooter angle
        answer futureAnswer lastAnswer lastOut.core lastOut.flags query0 aimResult lastAim
        (by rw [targetEq]; rfl) (by rw [rightEq]; rfl) lastRelated (by
          intro absent
          apply E1M1AimMissZero.aim q.world shooter (E1M1AimThirdCall.angle angle) (Fixed.ofInt 1024)
            lastAnswer lastAim
          cases eq : lastAnswer.target <;> simp_all)
      exact ⟨selected,_,_,source,(toThird.trans lastRun).trans tailRun,slope⟩
end Doom.Proofs.E1M1AimThreeCalls
