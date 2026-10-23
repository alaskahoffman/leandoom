import Doom.Proofs.E1M1AimStampCall
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimStampRestart
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
open E1M1AimRetryGeometry (nextAngle)
open E1M1AimRetryInputs (reads Prepared prepared setup)
attribute [local irreducible] load32 store32 SolidThing.shootHeight

/-- Execute the next ray and path initialization from the reached retry CALL.
Freshness is derived from the preceding exact history and original words.
The new image starts at this probe's entry, while preserving all old stamp values. -/
theorem restart (q : Context) (s : X86Memory.State) (next : X86Control.State)
    (thing : SolidThing) (angle : Angle) (distance : Fixed) (second : Bool) (cells : List Cell)
    (h : E1M1AimSetupEntry.Inputs q s thing angle distance)
    (request : E1M1AimRetryRequest.Request second s next)
    (data : Prepared q next.core thing (nextAngle second angle) cells)
    (seen : Array Bool) (size : seen.size=475)
    (image : E1M1AimStampImage.Image s.memory next.core.memory q.lines q.epoch seen)
    (before : E1M1AimStampImage.Fresh s.memory q.lines (q.epoch+1) 475)
    (nextX nextY : Int32 × Fixed × Fixed)
    (okX : (path q thing.x thing.y (thing.attackEndpoint (nextAngle second angle) (Fixed.ofInt 1024)).1
      (thing.attackEndpoint (nextAngle second angle) (Fixed.ofInt 1024)).2).xStep=.ok nextX)
    (okY : (path q thing.x thing.y (thing.attackEndpoint (nextAngle second angle) (Fixed.ofInt 1024)).1
      (thing.attackEndpoint (nextAngle second angle) (Fixed.ofInt 1024)).2).yStep=.ok nextY) :
    let out := E1M1PathMapSetup.grid (traversal next.core).core
    ∃ k≤175,
      X86ReturnCleanup.Prefix FloorCaller.cm E1M1AimProgramLink.program [] (36+k) next out ∧
      OriginalLineVisits.Represents out.core.memory q.lines (q.epoch+1) (Array.replicate 475 false) ∧
      E1M1AimStampImage.Image next.core.memory out.core.memory q.lines (q.epoch+1) (Array.replicate 475 false) ∧
      out.pc=0x2ca7f ∧
      E1M1PathAdvance.observe out.core=E1M1FiringGridState.initial
        (path q thing.x thing.y (thing.attackEndpoint (nextAngle second angle) (Fixed.ofInt 1024)).1
          (thing.attackEndpoint (nextAngle second angle) (Fixed.ofInt 1024)).2) nextX nextY := by
  obtain ⟨ray,geometry,_⟩ := setup q next thing (nextAngle second angle) cells request.pc data
  have epochSafe := E1M1AimRetryData.safe s next.core 0x13580 request.stack h.epochSafe
  have stampSafe (j : Nat) (hj : j<475) := E1M1AimRetryData.safe s next.core
    (OriginalLineVisits.stamp q.lines j) request.stack (h.stampSafe j (by rw [h.lineCount]; exact hj))
  have rayImage := E1M1AimStampImage.transport s.memory next.core.memory (traversal next.core).core.memory
    q.lines q.epoch seen image (E1M1PathMapQuery.traversal_frame next.core _ epochSafe)
    (fun j hj => E1M1PathMapQuery.traversal_frame next.core _ (stampSafe j (by omega)))
  have visited := E1M1AimStampImage.restart s.memory (traversal next.core).core q.lines q.epoch seen
    _ _ _ _ _ _ geometry rayImage (by simpa only [size] using before)
    (E1M1PathMapQuery.traversal_safe next.core _ epochSafe).2
    (fun j hj => E1M1PathMapQuery.traversal_safe next.core _ (stampSafe j (by omega)))
  rw [size] at visited
  have resetImage : E1M1AimStampImage.Image next.core.memory
      (E1M1PathMapSetup.grid (traversal next.core).core).core.memory q.lines (q.epoch+1)
      (Array.replicate 475 false) := by
    refine ⟨visited.1,?_⟩
    intro j hj
    have bound : j<475 := by simpa only [Array.size_replicate] using hj
    rw [getElem!_pos _ j hj,Array.getElem_replicate]
    simp only [Bool.false_eq_true,if_false]
    exact (E1M1PathMapSetup.grid_frame _ _ _ _ _ _ _ geometry _
      (E1M1PathMapQuery.traversal_safe next.core _ (stampSafe j bound))).trans
      (E1M1PathMapQuery.traversal_frame next.core _ (stampSafe j bound))
  obtain ⟨k,hk,init⟩ := E1M1QueryPrefix.execution (traversal next.core).core (traversal next.core).flags
    _ _ _ _ _ _ geometry nextX nextY okX okY
  have initAt : (traversal next.core).pc=0x2c8a0 := rfl
  rw [OriginalPathXStep.at_pc _ _ initAt] at init
  have query := (init.transfer E1M1TraversalEntry.program [] E1M1TraversalEntry.contains_collection (by simp)).transfer
    E1M1FirstIntercept.program [] E1M1FirstIntercept.contains_entry (by simp)
  have linked := (X86ReturnCleanup.lift query).transfer E1M1AimProgramLink.program E1M1AimProgramLink.contains_query
  have numeric := E1M1QueryInit.numeric (traversal next.core).core _ _ _ _ _ _ geometry nextX nextY okX okY
  exact ⟨k,hk,ray.trans linked,visited,resetImage,numeric.2.1,numeric.1⟩

/-- Join the original complete aim call, real retry, next ray and next path
initialization. No freshness premise is made about a reached intermediate state.
The next cell collection and full second/third probes remain separate. -/
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
    (second : Bool) (nextCells : List Cell)
    (tables : ThrustTables s.memory)
    (nextData : ∀ c∈nextCells, E1M1QueryImages.Payload s.memory q c ∧ E1M1AimPreRayMemory.PayloadSafe s q c)
    (watchedRead : ∀ addr∈reads q s (nextAngle second angle) nextCells, E1M1AimPreRayMemory.Read q s addr)
    (watchedSafe : ∀ addr∈reads q s (nextAngle second angle) nextCells, E1M1AimSavedWords.Protect (E1M1AimQueryCatalog.view q s) addr)
    (retrySafe : ∀ addr∈reads q s (nextAngle second angle) nextCells, Apart addr 0x2c0c0 ∧ Apart addr (s.regs 4))
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
      E1M1AimReturnedTarget.Image after.collected (resolve q.lines q.objects) out answer ∧
      E1M1BulletAim.ProbeResult out.core answer ∧
      (∀ addr∈reads q s (nextAngle second angle) nextCells, load32 out.core.memory addr=load32 s.memory addr) ∧
      E1M1AimStampImage.Image s.memory out.core.memory q.lines q.epoch
        (history q (Array.replicate q.world.lines.size false) cells) ∧
      (answer.target=none →
        X86ReturnCleanup.Prefix FloorCaller.cm E1M1AimProgramLink.program []
          (n+(4+(if second then 4 else 5))) ⟨s,f,0x2bb80⟩ (E1M1BulletAim.nextQuery second out.core) ∧
        E1M1AimRetryRequest.Request second s (E1M1BulletAim.nextQuery second out.core) ∧
        (E1M1BulletAim.nextQuery second out.core).core.regs 0=s.regs 0 ∧
        (E1M1BulletAim.nextQuery second out.core).core.regs 2=
          angle.raw.toBitVec+(if second then 0xf8000000 else 0x04000000) ∧
        (∀ addr∈reads q s (nextAngle second angle) nextCells, load32 (E1M1BulletAim.nextQuery second out.core).core.memory addr=
          load32 s.memory addr) ∧
        Prepared q (E1M1BulletAim.nextQuery second out.core).core thing (nextAngle second angle) nextCells ∧
        X86ReturnCleanup.Prefix FloorCaller.cm E1M1AimProgramLink.program []
          ((n+(4+(if second then 4 else 5)))+36) ⟨s,f,0x2bb80⟩
          (traversal (E1M1BulletAim.nextQuery second out.core).core) ∧
        OriginalPathInit.Inputs (traversal (E1M1BulletAim.nextQuery second out.core).core).core
          (Fixed.ofInt q.world.grid.origin.x) (Fixed.ofInt q.world.grid.origin.y) thing.x thing.y
          (thing.attackEndpoint (nextAngle second angle) (Fixed.ofInt 1024)).1
          (thing.attackEndpoint (nextAngle second angle) (Fixed.ofInt 1024)).2 ∧
        E1M1PathMapSetup.MapInputs (traversal (E1M1BulletAim.nextQuery second out.core).core).core
          q.base q.lines q.words q.width q.height ∧
        E1M1AimStampImage.Image s.memory (E1M1BulletAim.nextQuery second out.core).core.memory q.lines q.epoch
          (history q (Array.replicate q.world.lines.size false) cells) ∧
        (E1M1AimStampImage.Fresh s.memory q.lines (q.epoch+1) 475 →
          ∀ nextX nextY,
          (path q thing.x thing.y (thing.attackEndpoint (nextAngle second angle) (Fixed.ofInt 1024)).1
            (thing.attackEndpoint (nextAngle second angle) (Fixed.ofInt 1024)).2).xStep=.ok nextX →
          (path q thing.x thing.y (thing.attackEndpoint (nextAngle second angle) (Fixed.ofInt 1024)).1
            (thing.attackEndpoint (nextAngle second angle) (Fixed.ofInt 1024)).2).yStep=.ok nextY →
          let ready := E1M1PathMapSetup.grid (traversal (E1M1BulletAim.nextQuery second out.core).core).core
          ∃ k≤175,
            X86ReturnCleanup.Prefix FloorCaller.cm E1M1AimProgramLink.program []
              ((n+(4+(if second then 4 else 5)))+(36+k)) ⟨s,f,0x2bb80⟩ ready ∧
            OriginalLineVisits.Represents ready.core.memory q.lines (q.epoch+1) (Array.replicate 475 false) ∧
            E1M1AimStampImage.Image (E1M1BulletAim.nextQuery second out.core).core.memory ready.core.memory
              q.lines (q.epoch+1) (Array.replicate 475 false) ∧
            ready.pc=0x2ca7f ∧
            E1M1PathAdvance.observe ready.core=E1M1FiringGridState.initial
              (path q thing.x thing.y (thing.attackEndpoint (nextAngle second angle) (Fixed.ofInt 1024)).1
                (thing.attackEndpoint (nextAngle second angle) (Fixed.ofInt 1024)).2) nextX nextY)) := by
  obtain ⟨after,traced,out,answer,n,hn,run,pathSource,aimSource,restored,image,related,kept,stampImage,_,continueOnMiss⟩ :=
    E1M1AimStampCall.retry q pick s f thing angle distance h shooter shooterValue positive profile
      xout yout okX okY common height statics scenes payloads separated callbackSafe cursorCall room
      portals walls who initial savedSafe returnSafe (reads q s (nextAngle second angle) nextCells)
      watchedRead watchedSafe retrySafe second controller resume stampSafe stampProtected stampRetry
  refine ⟨after,traced,out,answer,n,hn,run,pathSource,aimSource,restored,image,related,kept,stampImage,?_⟩
  intro miss
  obtain ⟨continued,request,actor,angleReg,frame,nextImage,_⟩ := continueOnMiss miss
  have data := prepared q s (E1M1BulletAim.nextQuery second out.core) thing angle distance second
    nextCells h request controller tables nextData frame watchedRead
  obtain ⟨setupRun,geometry,map⟩ := setup q (E1M1BulletAim.nextQuery second out.core) thing
    (nextAngle second angle) nextCells request.pc data
  refine ⟨continued,request,actor,angleReg,frame,data,continued.trans setupRun,geometry,map,nextImage,?_⟩
  intro before nextX nextY nextOkX nextOkY
  have historySize : (history q (Array.replicate q.world.lines.size false)
      (sourceRoute pick 64 (E1M1FiringGridState.initial
        (path q thing.x thing.y (thing.attackEndpoint angle distance).1 (thing.attackEndpoint angle distance).2)
        xout yout))).size=475 := by
    rw [E1M1AimStampOrigin.history_size,Array.size_replicate,h.lineCount]
  obtain ⟨k,hk,runNext,visits,newImage,pc,numeric⟩ := restart q s
    (E1M1BulletAim.nextQuery second out.core) thing angle distance second nextCells h request data
      _ historySize nextImage before nextX nextY nextOkX nextOkY
  exact ⟨k,hk,continued.trans runNext,visits,newImage,pc,numeric⟩
end Doom.Proofs.E1M1AimStampRestart
