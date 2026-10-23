import Doom.Proofs.E1M1AimRetryGeometry
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimRetryInputs
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
attribute [local irreducible] load32 store32 SolidThing.shootHeight

/-- Finite reads for next-angle geometry, the full blockmap and supplied cells.
Visited stamps and the epoch are deliberately absent: those are changed data. -/
def reads (q : Context) (s : X86Memory.State) (angle : Angle) (cells : List Cell) : List Word :=
  E1M1AimRetryData.mapReads q.base q.words ++ E1M1AimRetryGeometry.reads s angle ++
    cells.flatMap (E1M1AimRetryData.cellReads q)

/-- Reusable next-call data. This is not the complete setup-entry contract:
epoch/freshness, the new trace, catalogs and route/capacity still need joining. -/
structure Prepared (q : Context) (s : X86Memory.State) (thing : SolidThing)
    (angle : Angle) (cells : List Cell) : Prop where
  geometry : E1M1AimGeometry.Inputs s thing angle (Fixed.ofInt 1024)
    (Fixed.ofInt q.world.grid.origin.x) (Fixed.ofInt q.world.grid.origin.y)
  map : E1M1PathMapQuery.MapInputs s q.base q.lines q.words q.width q.height
  payloads : ∀ c∈cells, E1M1QueryImages.Payload s.memory q c ∧ E1M1AimPreRayMemory.PayloadSafe s q c

/-- Convert the actual restored retry request and finite memory frame into
next-angle geometry and complete map/cell payloads, with reusable guards. -/
theorem prepared (q : Context) (s : X86Memory.State) (next : X86Control.State)
    (thing : SolidThing) (angle : Angle) (distance : Fixed) (second : Bool) (cells : List Cell)
    (h : E1M1AimSetupEntry.Inputs q s thing angle distance)
    (request : E1M1AimRetryRequest.Request second s next)
    (controller : s.regs 6=s.regs 0 ∧ s.regs 1=angle.raw.toBitVec)
    (tables : ThrustTables s.memory)
    (data : ∀ c∈cells, E1M1QueryImages.Payload s.memory q c ∧ E1M1AimPreRayMemory.PayloadSafe s q c)
    (kept : ∀ a∈reads q s (nextAngle second angle) cells, load32 next.core.memory a=load32 s.memory a)
    (safe : ∀ a∈reads q s (nextAngle second angle) cells, E1M1AimPreRayMemory.Read q s a) :
    Prepared q next.core thing (nextAngle second angle) cells := by
  have mapKeep (a : Word) (ha : a∈E1M1AimRetryData.mapReads q.base q.words) :=
    kept a (List.mem_append_left _ (List.mem_append_left _ ha))
  have geometryKeep (a : Word) (ha : a∈E1M1AimRetryGeometry.reads s (nextAngle second angle)) :=
    kept a (List.mem_append_left _ (List.mem_append_right _ ha))
  refine ⟨E1M1AimRetryGeometry.geometry s next.core thing angle (nextAngle second angle)
    distance (Fixed.ofInt 1024) _ _ h.geometry tables (request.actor.trans controller.1) request.stack
    ?_ request.range geometryKeep ?_,
    E1M1AimRetryData.map s next.core _ _ _ _ _ request.stack h.map mapKeep,?_⟩
  · rw [request.angle,controller.2,E1M1AimRetryGeometry.angle_bits]
  · intro a ha
    exact (safe a (List.mem_append_left _ (List.mem_append_right _
      (List.mem_append_right _ ha)))).1.saves
  · intro c member
    exact ⟨E1M1AimRetryData.payload s.memory next.core.memory q c (data c member).1
      (fun a ha => kept a (List.mem_append_right _ (List.mem_flatMap.mpr ⟨c,member,ha⟩))),
      E1M1AimRetryData.payload_safe s next.core q c request.stack (data c member).2⟩

/-- The prepared data drives the next real callee through ray/setup to its
path-traversal CALL, without executing the next collection or assuming stamps. -/
theorem setup (q : Context) (next : X86Control.State) (thing : SolidThing)
    (angle : Angle) (cells : List Cell) (pc : next.pc=0x2bb80)
    (data : Prepared q next.core thing angle cells) :
    X86ReturnCleanup.Prefix FloorCaller.cm E1M1AimProgramLink.program [] 36 next (traversal next.core) ∧
    OriginalPathInit.Inputs (traversal next.core).core
      (Fixed.ofInt q.world.grid.origin.x) (Fixed.ofInt q.world.grid.origin.y) thing.x thing.y
      (thing.attackEndpoint angle (Fixed.ofInt 1024)).1 (thing.attackEndpoint angle (Fixed.ofInt 1024)).2 ∧
    E1M1PathMapSetup.MapInputs (traversal next.core).core q.base q.lines q.words q.width q.height := by
  have run := E1M1AimSetupLink.execution next.core next.flags
  rw [OriginalPathXStep.at_pc _ _ pc] at run
  exact ⟨run,E1M1AimGeometry.path_inputs _ thing angle _ _ _ data.geometry,
    E1M1PathMapQuery.map_at_traversal _ _ _ _ _ _ data.map⟩

/-- From the original aim entry to the next probe's ray/setup: concrete next-read
contracts are derived from initial data and the complete-call memory frame.
The following path collection still requires fresh stamps and its source route. -/
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
      (∀ addr∈reads q s (nextAngle second angle) nextCells, load32 out.core.memory addr=load32 s.memory addr) ∧
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
          q.base q.lines q.words q.width q.height) := by
  obtain ⟨after,traced,out,answer,n,hn,run,pathSource,aimSource,restored,image,related,kept,retry⟩ :=
    E1M1AimCallFrame.retry q pick s f thing angle distance h shooter shooterValue positive profile
      xout yout okX okY common height statics scenes payloads separated callbackSafe cursorCall room
      portals walls who initial savedSafe returnSafe (reads q s (nextAngle second angle) nextCells)
      watchedRead watchedSafe retrySafe second controller resume
  refine ⟨after,traced,out,answer,n,hn,run,pathSource,aimSource,restored,image,related,kept,?_⟩
  intro miss
  obtain ⟨continued,request,actor,angleReg,frame⟩ := retry miss
  have data := prepared q s (E1M1BulletAim.nextQuery second out.core) thing angle distance second
    nextCells h request controller tables nextData frame watchedRead
  obtain ⟨setupRun,geometry,map⟩ := setup q (E1M1BulletAim.nextQuery second out.core) thing
    (nextAngle second angle) nextCells request.pc data
  exact ⟨continued,request,actor,angleReg,frame,data,continued.trans setupRun,geometry,map⟩
end Doom.Proofs.E1M1AimRetryInputs
