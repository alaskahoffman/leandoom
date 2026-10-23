import Doom.Proofs.OriginalPreparedState
import Doom.Player

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace Doom.Proofs.PreparedRuntime
open Verification X86 X86Memory X86Control BlockSummary Collision

/-- The eleven proved fields projected directly from the live Player record. -/
def words (p : Player) : PreparedState.Words :=
  ⟨p.body.angle.raw.toBitVec,p.body.momx.raw.toBitVec,p.body.momy.raw.toBitVec,
   PlayerAnimation.statePointer p.animation.frame,p.animation.tics.toBitVec,p.reactionTime.toBitVec,
   p.view.height.raw.toBitVec,p.view.delta.raw.toBitVec,p.view.z.raw.toBitVec,p.view.bob.raw.toBitVec,p.cachedOnGround⟩

/-- Successful scene synchronization and a supported player actor suffice to
connect the helper-level expression to the actual runtime preparation method.
Explicit Ticcmd input bypasses keyboard translation. This is the live branch. -/
theorem prepare (m : Map) (p : Player) (keys : UInt32) (cmd : Ticcmd)
    (scene : Scene) (actor : SolidThing)
    (sync : p.syncScene m = .ok scene) (found : scene.things[0]? = some actor)
    (supported : actor.moveFlags.floating = false) :
    (p.prepareTick m keys (some cmd)).map (fun result => words result.1) =
      .ok (PreparedState.expected (actor.motion p.body) p.animation cmd p.reactionTime
        p.view p.levelTime p.cachedOnGround true) := by
  simp [Player.prepareTick,sync,Scene.preparePlayerPhysics,found,supported,
    words,PreparedState.expected,PlayerGround.ground,Motion.onGround,
    Except.bind,Except.map,Except.pure,bind,pure]

/-- Read the proved projection from the actual runtime result, preserving
failure explicitly rather than silently manufacturing a player state. -/
def output (result : Except String (Player × Ticcmd)) : Option PreparedState.Words :=
  match result with
  | .ok (p,_) => some (words p)
  | .error _ => none

/-- Original DOS bytes and live Player.prepareTick yield the same eleven
preparation fields from related initial states. Initialization/sync correctness,
remaining Player fields and later tic phases are separate obligations. -/
theorem correspondence (s : X86Memory.State) (flags : Option Flags)
    (m : Map) (p : Player) (keys : UInt32) (cmd : Ticcmd)
    (scene : Scene) (actor : SolidThing)
    (sync : p.syncScene m = .ok scene) (found : scene.things[0]? = some actor)
    (supported : actor.moveFlags.floating = false)
    (h : PlayerHeightJoin.Inputs s (actor.motion p.body) p.animation cmd p.reactionTime
      p.view p.levelTime p.cachedOnGround true) :
    (X86Routine.run PlayerPreparation.program [0x333d0] 225 ⟨s,flags,0x333b1⟩).map
      (fun t => PreparedState.read (s.regs 2) (PlayerCaller.object s) t.core.memory) =
      output (p.prepareTick m keys (some cmd)) := by
  obtain ⟨t,run,_,state,_,_⟩ := PreparedState.execution s flags (actor.motion p.body) p.animation cmd
    p.reactionTime p.view p.levelTime p.cachedOnGround true h
  have runtime := prepare m p keys cmd scene actor sync found supported
  rw [run]
  simp only [Option.map_some,state]
  cases hr : p.prepareTick m keys (some cmd) with
  | error error => simp [hr,Except.map] at runtime
  | ok result =>
    simp only [hr,Except.map,Except.ok.injEq] at runtime
    simp only [output,runtime]

end Doom.Proofs.PreparedRuntime
