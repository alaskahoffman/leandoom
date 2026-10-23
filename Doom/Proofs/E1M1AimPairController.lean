import Doom.Proofs.E1M1AimThirdRequest
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimPairController
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

/-- The complete center/right calls now terminate live autoaim on either hit.
A double miss executes the third request with preserved data and fresh stamps,
derived from the two completed histories and original future-epoch freshness.
The third query body and controller prologue are outside this theorem. -/
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
        a∈(reads q s (nextAngle false angle) (route q nextPick thing angle false nextX nextY) ++ extra))) :
    let g := E1M1FiringGridState.initial (path q thing.x thing.y
      (thing.attackEndpoint angle (Fixed.ofInt 1024)).1 (thing.attackEndpoint angle (Fixed.ofInt 1024)).2) xout yout
    let cells := sourceRoute pick 64 g
    let cfg := context q thing angle false
    let futureCells := route q nextPick thing angle false nextX nextY
    let freshSeen := Array.replicate q.world.lines.size false
    ∃ (after traced : PathResult) (out : X86Control.State) (answer : AimResult) (n : Nat),
      n≤264+bound q cells+7*after.collected.size+
        after.collected.size*(157+7*after.collected.size) ∧
      X86ReturnCleanup.Prefix FloorCaller.cm E1M1AimProgramLink.program [] n ⟨s,f,0x2bb80⟩ out ∧
      q.world.pathTraverse thing.x thing.y (thing.attackEndpoint angle (Fixed.ofInt 1024)).1
        (thing.attackEndpoint angle (Fixed.ofInt 1024)).2 3 (fun _ _ => true)=.ok traced ∧
      q.world.aimLineAttack shooter angle (Fixed.ofInt 1024)=.ok answer ∧
      E1M1AimCallerRegisters.Restores s out ∧
      E1M1AimReturnedTarget.Image after.collected (resolve q.lines q.objects) out answer ∧
      E1M1BulletAim.ProbeResult out.core answer ∧
      (∀ addr∈(reads q s (nextAngle false angle) futureCells ++ extra), load32 out.core.memory addr=load32 s.memory addr) ∧
      E1M1AimStampImage.Image s.memory out.core.memory q.lines q.epoch (history q freshSeen cells) ∧
      (answer.target.isSome=true →
        q.world.bulletAim shooter angle=.ok (BulletAim.selection angle 0 answer) ∧
        X86ReturnCleanup.Prefix FloorCaller.cm E1M1AimProgramLink.program [] (n+9)
          ⟨s,f,0x2bb80⟩ (E1M1BulletAim.accepted false out.core) ∧
        load32 (E1M1BulletAim.accepted false out.core).core.memory 0x2c0c0=
          (BulletAim.selection angle 0 answer).slope.raw.toBitVec) ∧
      (answer.target=none →
        let next := E1M1BulletAim.nextQuery false out.core
        E1M1AimRetryRequest.Request false s next ∧
        E1M1AimSetupEntry.Inputs cfg next.core thing (nextAngle false angle) (Fixed.ofInt 1024) ∧
        ∃ (futureAfter futurePath : PathResult) (finish : X86Control.State) (futureAnswer : AimResult) (m : Nat),
          m≤264+bound cfg futureCells+7*futureAfter.collected.size+
            futureAfter.collected.size*(157+7*futureAfter.collected.size) ∧
          X86ReturnCleanup.Prefix FloorCaller.cm E1M1AimProgramLink.program [] m next finish ∧
          X86ReturnCleanup.Prefix FloorCaller.cm E1M1AimProgramLink.program []
            ((n+9)+m) ⟨s,f,0x2bb80⟩ finish ∧
          q.world.pathTraverse thing.x thing.y
            (thing.attackEndpoint (nextAngle false angle) (Fixed.ofInt 1024)).1
            (thing.attackEndpoint (nextAngle false angle) (Fixed.ofInt 1024)).2 3 (fun _ _ => true)=.ok futurePath ∧
          q.world.aimLineAttack shooter (nextAngle false angle) (Fixed.ofInt 1024)=.ok futureAnswer ∧
          E1M1AimCallerRegisters.Restores next.core finish ∧
          finish.pc=0x2d7f8 ∧
          E1M1AimReturnedTarget.Image futureAfter.collected (resolve q.lines q.objects) finish futureAnswer ∧
          E1M1BulletAim.ProbeResult finish.core futureAnswer ∧
          (∀ a∈(reads q s (nextAngle false angle) futureCells ++ extra),
            load32 finish.core.memory a=load32 s.memory a) ∧
          E1M1AimStampImage.Image next.core.memory finish.core.memory q.lines (q.epoch+1)
            (history cfg freshSeen futureCells) ∧
          (futureAnswer.target.isSome=true →
            q.world.bulletAim shooter angle=.ok (BulletAim.selection angle 0x04000000 futureAnswer) ∧
            X86ReturnCleanup.Prefix FloorCaller.cm E1M1AimProgramLink.program [] (((n+9)+m)+9)
              ⟨s,f,0x2bb80⟩ (E1M1BulletAim.accepted true finish.core) ∧
            load32 (E1M1BulletAim.accepted true finish.core).core.memory 0x2c0c0=
              (BulletAim.selection angle 0x04000000 futureAnswer).slope.raw.toBitVec) ∧
          (futureAnswer.target=none →
            let third := E1M1BulletAim.nextQuery true finish.core
            X86ReturnCleanup.Prefix FloorCaller.cm E1M1AimProgramLink.program [] (((n+9)+m)+8)
              ⟨s,f,0x2bb80⟩ third ∧
            E1M1AimRetryRequest.Request true next.core third ∧
            third.pc=0x2bb80 ∧ third.core.regs 4=s.regs 4 ∧ third.core.regs 0=s.regs 0 ∧
            third.core.regs 2=(angle.raw+0xfc000000).toBitVec ∧ third.core.regs 3=0x04000000 ∧
            load32 third.core.memory (third.core.regs 4)=0x2d819 ∧
            E1M1AimStampImage.Image next.core.memory third.core.memory q.lines (q.epoch+1)
              (history cfg freshSeen futureCells) ∧
            E1M1AimStampImage.Fresh third.core.memory q.lines ((q.epoch+1)+1) 475 ∧
            (∀ a∈(reads q s (nextAngle false angle) futureCells ++ extra),
              load32 third.core.memory a=load32 s.memory a))) := by
  obtain ⟨after,traced,out,answer,n,hn,run,pathSource,aimSource,restored,image,related,kept,stampImage,continueOnMiss⟩ :=
    E1M1AimRetryPair.execution q pick s f thing angle (Fixed.ofInt 1024) h shooter shooterValue
      (by decide) profile xout yout okX okY common height statics scenes payloads separated callbackSafe
      cursorCall room portals walls who initial savedSafe returnSafe false nextPick nextX nextY
      tables nextData extra watchedRead watchedSafe retrySafe controller resume stampSafe stampProtected
      stampRetry before nextOkX nextOkY nextStatics nextScenes nextRoom nextPortals nextWalls nextInitial
  refine ⟨after,traced,out,answer,n,hn,run,pathSource,aimSource,restored,image,related,kept,stampImage,?_,?_⟩
  · intro hit
    obtain ⟨source,tail,slope⟩ := E1M1AimControllerExit.center q.world shooter angle out answer
      aimSource related hit (restored.pc.trans resume)
    exact ⟨source,run.trans tail,slope⟩
  · intro miss
    obtain ⟨request,inputs,futureAfter,futurePath,finish,futureAnswer,m,hm,nextRun,twoRun,pathResult,
      aimResult,restoredNext,returned,target,result,words,exactImage,_⟩ := continueOnMiss miss
    refine ⟨request,inputs,futureAfter,futurePath,finish,futureAnswer,m,hm,nextRun,twoRun,pathResult,
      aimResult,restoredNext,returned,target,result,words,exactImage,?_,?_⟩
    · intro hit
      obtain ⟨source,tail,slope⟩ := E1M1AimControllerExit.right q.world shooter angle answer futureAnswer finish
        aimSource aimResult miss result hit returned
      exact ⟨source,twoRun.trans tail,slope⟩
    · intro noRight
      have nextRequest := E1M1AimRetryRequest.request true (E1M1BulletAim.nextQuery false out.core).core finish restoredNext
      have args := E1M1AimThirdRequest.arguments s (E1M1BulletAim.nextQuery false out.core)
        (E1M1BulletAim.nextQuery true finish.core) angle request nextRequest controller
      have firstSize : (history q (Array.replicate q.world.lines.size false)
          (sourceRoute pick 64 (E1M1FiringGridState.initial
            (path q thing.x thing.y (thing.attackEndpoint angle (Fixed.ofInt 1024)).1
              (thing.attackEndpoint angle (Fixed.ofInt 1024)).2) xout yout))).size=475 := by
        rw [E1M1AimStampOrigin.history_size,Array.size_replicate,h.lineCount]
      have nextSize : (history (context q thing angle false) (Array.replicate q.world.lines.size false)
          (route q nextPick thing angle false nextX nextY)).size=475 := by
        rw [E1M1AimStampOrigin.history_size,Array.size_replicate,h.lineCount]
      have safeFirst : ∀ a∈E1M1AimStampQuery.stampWords q.lines 475,
          Apart a 0x2c0c0 ∧ Apart a (out.core.regs 4-4) := by
        intro a ha
        simpa only [restored.stack,BitVec.add_sub_cancel] using stampRetry a ha
      have safeNext : ∀ a∈E1M1AimStampQuery.stampWords q.lines 475,
          Apart a 0x2c0c0 ∧ Apart a (finish.core.regs 4-4) := by
        intro a ha
        simpa only [restoredNext.stack,request.stack,BitVec.add_sub_cancel] using stampRetry a ha
      have firstImage := E1M1AimThirdRequest.retry_image false s.memory out q.lines q.epoch _ 475
        firstSize stampImage safeFirst
      have fresh := E1M1AimThirdRequest.consecutive_fresh s.memory _ finish.core.memory q.lines q.epoch
        _ _ 475 firstSize nextSize firstImage exactImage beforeTwo
      have thirdImage := E1M1AimThirdRequest.retry_image true _ finish q.lines (q.epoch+1) _ 475
        nextSize exactImage safeNext
      have thirdFresh := E1M1AimThirdRequest.retry_fresh true finish q.lines ((q.epoch+1)+1) 475 fresh safeNext
      refine ⟨twoRun.trans (E1M1AimRetryRequest.execution true finish futureAnswer result noRight returned),
        nextRequest,args.1,args.2.1,args.2.2.1,args.2.2.2.1,args.2.2.2.2.1,args.2.2.2.2.2,
        thirdImage,thirdFresh,?_⟩
      intro a ha
      exact (E1M1AimRetryRequest.frame true finish.core a (retrySafe a ha).1
        (by simpa only [restoredNext.stack,request.stack,BitVec.add_sub_cancel] using (retrySafe a ha).2)).trans
          (words a ha)
end Doom.Proofs.E1M1AimPairController
