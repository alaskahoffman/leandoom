import Doom.Proofs.E1M1AimSetupLink
import Doom.Proofs.E1M1AimSetupCatalog
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimEntryQuery
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

/-- Connect the actual production aim function, not merely its extracted hit
loop, using the source query proved by execution. -/
theorem production (scene : Scene) (shooter : Nat) (thing : SolidThing) (angle : Angle)
    (distance : Fixed) (path : PathResult) (answer : AimResult)
    (shooterValue : scene.things[shooter]?=some thing) (positive : ¬distance.raw≤0)
    (traced : scene.pathTraverse thing.x thing.y (thing.attackEndpoint angle distance).1
      (thing.attackEndpoint angle distance).2 3 (fun _ _ => true)=.ok path)
    (processed : E1M1AimSource.afterPath scene shooter thing path distance=.ok answer) :
    scene.aimLineAttack shooter angle distance=.ok answer := by
  rw [E1M1AimSource.live]
  have before : E1M1AimSource.attackPath scene shooter angle distance=.ok (thing,path) := by
    simp [E1M1AimSource.attackPath,positive,shooterValue,traced]
    rfl
  rw [before]
  exact processed

/-- Real aim entry, ray, traversal, ordered hits and returns in one execution.
Entry geometry and generated globals are derived. Residual catalog/payload
contracts still explicitly refer to the computed traversal boundary. -/
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
      inside q c=true → E1M1QueryImages.Payload (traversal s).core.memory q c ∧ E1M1QueryImages.Protected (traversal s).core q c)
    (separated : E1M1TraversalEntry.Protected q)
    (callbackSafe : CallbackSafe q (traversal s).core)
    (cursorCall : Apart 0x2c028 (q.sp-140))
    (room : budget q (sourceRoute pick 64 (E1M1FiringGridState.initial (path q thing.x thing.y (thing.attackEndpoint angle distance).1 (thing.attackEndpoint angle distance).2) xout yout))≤128)
    (portals : Nat → Option Portal) (walls : Nat → Prop) (who : Word)
    (initial : ∀ grid stamps after,
      E1M1LiveWalk.source q.world q.trace 64
        (E1M1FiringGridState.initial (path q thing.x thing.y (thing.attackEndpoint angle distance).1 (thing.attackEndpoint angle distance).2) xout yout)
        (Array.replicate q.world.lines.size false) {trace:=q.trace}=
        .ok (E1M1LoopReplay.pack grid stamps after) →
      E1M1AimSetupCatalog.Remaining q (traversal s).core q.world shooter after.collected portals walls who ∧
      ∃ path, Source q q.world shooter thing after path distance portals walls) :
    let g := E1M1FiringGridState.initial (path q thing.x thing.y (thing.attackEndpoint angle distance).1 (thing.attackEndpoint angle distance).2) xout yout
    let cells := sourceRoute pick 64 g
    ∃ (after traced : PathResult) (out : X86Control.State) (answer : AimResult) (n : Nat),
      n≤264+bound q cells+7*after.collected.size+
        after.collected.size*(157+7*after.collected.size) ∧
      X86ReturnCleanup.Prefix FloorCaller.cm E1M1AimProgramLink.program [] n ⟨s,f,0x2bb80⟩ out ∧
      q.world.pathTraverse thing.x thing.y (thing.attackEndpoint angle distance).1 (thing.attackEndpoint angle distance).2 3 (fun _ _ => true)=.ok traced ∧
      q.world.aimLineAttack shooter angle distance=.ok answer ∧
      E1M1AimSavedCaller.Restores (traversal s) (q.sp-136) out ∧
      E1M1AimReturnedTarget.Image after.collected (resolve q.lines q.objects) out answer ∧
      E1M1BulletAim.ProbeResult out.core answer := by
  have setup := E1M1AimSetupLink.execution s f
  have entry := E1M1AimSetupEntry.entry q s thing angle distance h
  have argument := congrArg (fun t => t.2.2) (E1M1AimSetupEntry.call s thing angle distance _ _ h.geometry)
  obtain ⟨after,traced,out,answer,n,hn,run,pathSource,aimSource,value,restored,image,related⟩ :=
    E1M1AimQueryTarget.execution q pick (traversal s).core (traversal s).flags thing.x thing.y (thing.attackEndpoint angle distance).1 (thing.attackEndpoint angle distance).2
      entry profile xout yout okX okY common height statics scenes payloads separated callbackSafe argument
      cursorCall room q.world shooter thing distance portals walls who (by
        intro grid stamps after source
        obtain ⟨remaining,traced,model⟩ := initial grid stamps after source
        exact ⟨E1M1AimSetupCatalog.initial q s q.world shooter thing angle distance after.collected
          portals walls who h remaining,traced,model⟩)
  exact ⟨after,traced,out,answer,36+n,by omega,setup.trans run,pathSource,
    production q.world shooter thing angle distance traced answer shooterValue positive pathSource aimSource,
    restored,image,related⟩

/-- Extend the same aim-entry execution through the real center/right decision.
The landing PC is derived from the protected original caller return word. -/
theorem decision (q : Context) (pick : Int32 → Int32 → Cell)
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
      inside q c=true → E1M1QueryImages.Payload (traversal s).core.memory q c ∧ E1M1QueryImages.Protected (traversal s).core q c)
    (separated : E1M1TraversalEntry.Protected q)
    (callbackSafe : CallbackSafe q (traversal s).core)
    (cursorCall : Apart 0x2c028 (q.sp-140))
    (room : budget q (sourceRoute pick 64 (E1M1FiringGridState.initial (path q thing.x thing.y (thing.attackEndpoint angle distance).1 (thing.attackEndpoint angle distance).2) xout yout))≤128)
    (portals : Nat → Option Portal) (walls : Nat → Prop) (who : Word)
    (initial : ∀ grid stamps after,
      E1M1LiveWalk.source q.world q.trace 64
        (E1M1FiringGridState.initial (path q thing.x thing.y (thing.attackEndpoint angle distance).1 (thing.attackEndpoint angle distance).2) xout yout)
        (Array.replicate q.world.lines.size false) {trace:=q.trace}=
        .ok (E1M1LoopReplay.pack grid stamps after) →
      E1M1AimSetupCatalog.Remaining q (traversal s).core q.world shooter after.collected portals walls who ∧
      ∃ path, Source q q.world shooter thing after path distance portals walls)
    (second : Bool) (returnSafe : E1M1PathMapQuery.Safe s (s.regs 4))
    (resume : (load32 s.memory (s.regs 4)).toNat=if second then 0x2d7f8 else 0x2d7d5) :
    let g := E1M1FiringGridState.initial (path q thing.x thing.y (thing.attackEndpoint angle distance).1 (thing.attackEndpoint angle distance).2) xout yout
    let cells := sourceRoute pick 64 g
    ∃ (after : PathResult) (out : X86Control.State) (answer : AimResult) (n : Nat),
      n≤268+bound q cells+7*after.collected.size+
        after.collected.size*(157+7*after.collected.size) ∧
      X86ReturnCleanup.Prefix FloorCaller.cm E1M1AimProgramLink.program [] n ⟨s,f,0x2bb80⟩ out ∧
      q.world.aimLineAttack shooter angle distance=.ok answer ∧
      load32 out.core.memory 0x2c0c0=answer.slope.raw.toBitVec ∧
      out.pc=(if answer.target.isSome then 0x2d81e else (if second then 0x2d807 else 0x2d7e4)) := by
  obtain ⟨after,traced,out,answer,n,hn,run,pathSource,aimSource,restored,image,related⟩ :=
    execution q pick s f thing angle distance h shooter shooterValue positive profile xout yout
      okX okY common height statics scenes payloads separated callbackSafe cursorCall room portals walls who initial
  have saved := E1M1AimSetupCatalog.return_address q s h.stack returnSafe
  have pc := restored.2.1.trans ((congrArg BitVec.toNat saved).trans resume)
  obtain ⟨tail,slope,branch⟩ := E1M1AimTargetDecision.decision second out answer related pc
  exact ⟨after,OriginalBulletSlope.decision second out.core,answer,n+4,by omega,
    run.trans tail,aimSource,slope,branch⟩
end Doom.Proofs.E1M1AimEntryQuery
