import Doom.Proofs.E1M1AimNextCollection
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimRetryCollection
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

/-- A complete original aim call and real miss-to-retry CALL continue through
the next generated cell collection. All reached data and stamp contracts come
from initial memory; next-route metadata and capacity remain explicit. -/
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
    (second : Bool) (nextPick : Int32 → Int32 → Cell) (nextX nextY : Int32 × Fixed × Fixed)
    (tables : ThrustTables s.memory)
    (nextData : ∀ c∈(route q nextPick thing angle second nextX nextY), E1M1QueryImages.Payload s.memory q c ∧ E1M1AimPreRayMemory.PayloadSafe s q c)
    (watchedRead : ∀ addr∈reads q s (nextAngle second angle) (route q nextPick thing angle second nextX nextY), E1M1AimPreRayMemory.Read q s addr)
    (watchedSafe : ∀ addr∈reads q s (nextAngle second angle) (route q nextPick thing angle second nextX nextY), E1M1AimSavedWords.Protect (E1M1AimQueryCatalog.view q s) addr)
    (retrySafe : ∀ addr∈reads q s (nextAngle second angle) (route q nextPick thing angle second nextX nextY), Apart addr 0x2c0c0 ∧ Apart addr (s.regs 4))
    (controller : s.regs 6=s.regs 0 ∧ s.regs 1=angle.raw.toBitVec)
    (resume : (load32 s.memory (s.regs 4)).toNat=if second then 0x2d7f8 else 0x2d7d5)
    (stampSafe : ∀ a∈E1M1AimStampQuery.stampWords q.lines 475, E1M1AimEntryFrame.SafeWord (q.sp-112) a)
    (stampProtected : ∀ a∈E1M1AimStampQuery.stampWords q.lines 475,
      E1M1AimSavedWords.Protect (E1M1AimQueryCatalog.view q s) a)
    (stampRetry : ∀ a∈E1M1AimStampQuery.stampWords q.lines 475, Apart a 0x2c0c0 ∧ Apart a (s.regs 4))
    (before : E1M1AimStampImage.Fresh s.memory q.lines (q.epoch+1) 475)
    (nextOkX : (path q thing.x thing.y (thing.attackEndpoint (nextAngle second angle) (Fixed.ofInt 1024)).1
      (thing.attackEndpoint (nextAngle second angle) (Fixed.ofInt 1024)).2).xStep=.ok nextX)
    (nextOkY : (path q thing.x thing.y (thing.attackEndpoint (nextAngle second angle) (Fixed.ofInt 1024)).1
      (thing.attackEndpoint (nextAngle second angle) (Fixed.ofInt 1024)).2).yStep=.ok nextY)
    (nextStatics : ∀ c∈route q nextPick thing angle second nextX nextY, Admitted (context q thing angle second) c)
    (nextScenes : ∀ c∈route q nextPick thing angle second nextX nextY,
      inside (context q thing angle second) c=true → E1M1CellLineSource.SceneLines (context q thing angle second) c)
    (nextRoom : budget (context q thing angle second) (route q nextPick thing angle second nextX nextY)≤128) :
    let g := E1M1FiringGridState.initial (path q thing.x thing.y
      (thing.attackEndpoint angle distance).1 (thing.attackEndpoint angle distance).2) xout yout
    let cells := sourceRoute pick 64 g
    let cfg := context q thing angle second
    let futureCells := route q nextPick thing angle second nextX nextY
    let nextGrid := E1M1FiringGridState.initial (path q thing.x thing.y
      (thing.attackEndpoint (nextAngle second angle) (Fixed.ofInt 1024)).1
      (thing.attackEndpoint (nextAngle second angle) (Fixed.ofInt 1024)).2) nextX nextY
    let freshSeen := Array.replicate q.world.lines.size false
    ∃ (after traced : PathResult) (out : X86Control.State) (answer : AimResult) (n : Nat),
      n≤264+bound q cells+7*after.collected.size+
        after.collected.size*(157+7*after.collected.size) ∧
      X86ReturnCleanup.Prefix FloorCaller.cm E1M1AimProgramLink.program [] n ⟨s,f,0x2bb80⟩ out ∧
      q.world.pathTraverse thing.x thing.y (thing.attackEndpoint angle distance).1
        (thing.attackEndpoint angle distance).2 3 (fun _ _ => true)=.ok traced ∧
      q.world.aimLineAttack shooter angle distance=.ok answer ∧
      E1M1AimCallerRegisters.Restores s out ∧
      E1M1AimReturnedTarget.Image after.collected (resolve q.lines q.objects) out answer ∧
      E1M1BulletAim.ProbeResult out.core answer ∧
      (∀ addr∈reads q s (nextAngle second angle) futureCells, load32 out.core.memory addr=load32 s.memory addr) ∧
      E1M1AimStampImage.Image s.memory out.core.memory q.lines q.epoch (history q freshSeen cells) ∧
      (answer.target=none →
        let next := E1M1BulletAim.nextQuery second out.core
        X86ReturnCleanup.Prefix FloorCaller.cm E1M1AimProgramLink.program []
          (n+(4+(if second then 4 else 5))) ⟨s,f,0x2bb80⟩ next ∧
        E1M1AimRetryRequest.Request second s next ∧
        Prepared q next.core thing (nextAngle second angle) futureCells ∧
        E1M1AimSetupEntry.Inputs cfg next.core thing (nextAngle second angle) (Fixed.ofInt 1024) ∧
        futureCells≠[] ∧ futureCells.length≤64 ∧ ∃ collected futureAfter,
          (∃ m≤211+bound cfg futureCells,
            X86ReturnCleanup.Prefix FloorCaller.cm E1M1AimProgramLink.program []
              ((n+(4+(if second then 4 else 5)))+m) ⟨s,f,0x2bb80⟩ collected) ∧
          E1M1LiveWalk.source q.world cfg.trace 64 nextGrid freshSeen {trace:=cfg.trace}=
            .ok (E1M1LoopReplay.pack (E1M1PathAdvance.observe collected.core) (history cfg freshSeen futureCells) futureAfter) ∧
          (∀ visit, q.world.pathTraverse thing.x thing.y
            (thing.attackEndpoint (nextAngle second angle) (Fixed.ofInt 1024)).1
            (thing.attackEndpoint (nextAngle second angle) (Fixed.ofInt 1024)).2 3 visit=
              E1M1QuerySource.visitHits futureAfter visit) ∧
          State cfg collected futureAfter (history cfg freshSeen futureCells) ∧
          futureAfter.collected.size≤budget cfg futureCells ∧
          E1M1PathAdvance.observe collected.core=E1M1CellWalk.grid nextGrid futureCells ∧ collected.pc=0x2cafd ∧
          Images cfg futureCells collected.core.memory ∧
          (∀ addr, E1M1AimPreRayMemory.Read cfg next.core addr →
            load32 collected.core.memory addr=load32 next.core.memory addr) ∧
          E1M1AimStampImage.Image next.core.memory collected.core.memory q.lines (q.epoch+1)
            (history cfg freshSeen futureCells)) := by
  obtain ⟨after,traced,out,answer,n,hn,run,pathSource,aimSource,restored,image,related,kept,stampImage,_,continueOnMiss⟩ :=
    E1M1AimStampCall.retry q pick s f thing angle distance h shooter shooterValue positive profile
      xout yout okX okY common height statics scenes payloads separated callbackSafe cursorCall room
      portals walls who initial savedSafe returnSafe (reads q s (nextAngle second angle)
        (route q nextPick thing angle second nextX nextY))
      watchedRead watchedSafe retrySafe second controller resume stampSafe stampProtected stampRetry
  refine ⟨after,traced,out,answer,n,hn,run,pathSource,aimSource,restored,image,related,kept,stampImage,?_⟩
  intro miss
  obtain ⟨continued,request,_,_,frame,nextImage,_⟩ := continueOnMiss miss
  have data := prepared q s (E1M1BulletAim.nextQuery second out.core) thing angle distance second
    (route q nextPick thing angle second nextX nextY) h request controller tables nextData frame watchedRead
  have historySize : (history q (Array.replicate q.world.lines.size false)
      (sourceRoute pick 64 (E1M1FiringGridState.initial
        (path q thing.x thing.y (thing.attackEndpoint angle distance).1 (thing.attackEndpoint angle distance).2)
        xout yout))).size=475 := by
    rw [E1M1AimStampOrigin.history_size,Array.size_replicate,h.lineCount]
  obtain ⟨inputs,nonempty,length,collected,futureAfter,⟨m,hm,nextRun⟩,source,tail,state,used,obs,pc,images,words,exactImage⟩ :=
    E1M1AimNextCollection.execution q nextPick s (E1M1BulletAim.nextQuery second out.core)
      thing angle distance second h request _ historySize nextImage before nextX nextY nextOkX nextOkY
      data profile common height nextStatics nextScenes nextRoom
  exact ⟨continued,request,data,inputs,nonempty,length,collected,futureAfter,
    ⟨m,hm,continued.trans nextRun⟩,source,tail,state,used,obs,pc,images,words,exactImage⟩
end Doom.Proofs.E1M1AimRetryCollection
