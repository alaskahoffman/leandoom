import Doom.Proofs.OriginalFloorJoined
import Doom.Proofs.OriginalSectorRuntime
import Doom.Combat

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.FloorRuntime
open Verification X86 X86Memory X86Control BlockSummary Collision
open FloorDamage (Kind)

/-- Factoring the live request leaves the previous lookup, error, RNG, and
callback ordering intact for any damage implementation. -/
theorem effect_inline (s : Simulation) (damage : Simulation → Nat → Simulation) :
    s.applyFloorEffect damage =
      match s.map.sectorAt s.player.body.x s.player.body.y with
      | .error error => { s with physicsError := some error }
      | .ok index =>
        let sector := s.map.sectors[index]!
        let (amount,rng) := LevelSpecials.floorDamage sector.special s.player.body.z
          (Fixed.ofInt sector.floor) (s.inventory.suit > 0) (s.ticks-1) s.rng
        let next := { s with rng }
        if amount == 0 then next else damage next amount := by
  cases lookup : s.map.sectorAt s.player.body.x s.player.body.y <;>
    simp [Simulation.applyFloorEffect,Simulation.floorDamageRequest,lookup,Except.map,Functor.map,Except.bind,Except.pure,bind,pure]

/-- A lookup error does not invoke damage or invent an RNG observation. -/
theorem lookup_failure (s : Simulation) (error : String)
    (h : s.map.sectorAt s.player.body.x s.player.body.y = .error error)
    (damage : Simulation → Nat → Simulation) :
    s.floorDamageRequest = .error error ∧
    s.applyFloorEffect damage = { s with physicsError := some error } := by
  have request : s.floorDamageRequest = .error error := by
    simp [Simulation.floorDamageRequest,h,Functor.map,Except.bind,Except.pure,bind,pure]
  exact ⟨request,by simp [Simulation.applyFloorEffect,request]⟩

/-- This statement is about the actual combat callback, including no-damage
suit leakage draws; health handling is not entered on this branch. -/
theorem combat_no_damage (s : Simulation) (rng : DoomRandom)
    (h : s.floorDamageRequest = .ok (0,rng)) :
    s.hurtFromFloor = { s with rng } := by
  rw [Simulation.hurtFromFloor_request,h]
  rfl

/-- Ordinary damaging sectors are unchanged by the earlier secret check. -/
theorem ordinary_secret (kind : Kind) (z floor : Fixed) (count : Int32) :
    LevelSpecials.secret kind.special z floor count = (kind.special,count) := by
  cases kind <;> simp [LevelSpecials.secret,Kind.special]

theorem ordinary_result (kind : Kind) (s : Simulation) (q : Player) (index : Nat)
    (valid : index < s.map.sectors.size) (special : s.map.sectors[index]!.special = kind.special) :
    SectorRuntime.result s q index = { s with player := q } := by
  unfold SectorRuntime.result
  simp only [special,ordinary_secret]
  have record : { s.map.sectors[index]! with special := kind.special } = s.map.sectors[index]! := by
    rw [← special]
  have unchanged : s.map.sectors.set! index s.map.sectors[index]! = s.map.sectors := by
    simp [Array.set!_eq_setIfInBounds,Array.setIfInBounds,valid]
  rw [record,unchanged]

/-- The original ticking convention: interactionTick increments the Nat clock
before the floor callback, which consumes the prior tic without underflow. -/
theorem tick_clock (s : Simulation) : ({ s with ticks := s.ticks+1 } : Simulation).ticks-1 = s.ticks := by
  simp

/-- Derive the live request from the incoming synchronized actor/map. No
post-preparation position, second lookup, suit, clock or RNG fact is assumed. -/
theorem phase_execution (kind : Kind) (s : Simulation) (keys : UInt32) (cmd : Ticcmd)
    (scene : Scene) (actor : SolidThing) (index : Nat)
    (sync : (SectorRuntime.inputPlayer s).syncScene s.map = .ok scene)
    (found : scene.things[0]? = some actor) (supported : actor.moveFlags.floating = false)
    (lookup : s.map.sectorAt actor.x actor.y = .ok index) (valid : index < s.map.sectors.size)
    (special : s.map.sectors[index]!.special = kind.special) :
    ∃ q, s.prepareSectorTick keys (some cmd) = .ok ({ s with player := q },cmd) ∧
      PreparedRuntime.words q = PreparedState.expected (actor.motion s.player.body) s.player.animation cmd
        s.player.reactionTime s.player.view s.player.levelTime s.player.cachedOnGround true ∧
      q.body.x = actor.x ∧ q.body.y = actor.y ∧ q.body.z = actor.z ∧
      ({ s with player := q } : Simulation).floorDamageRequest =
        .ok (LevelSpecials.floorDamage kind.special actor.z (Fixed.ofInt s.map.sectors[index]!.floor)
          (s.inventory.suit > 0) (s.ticks-1) s.rng) := by
  obtain ⟨q,_,run,words,x,y,z⟩ := SectorRuntime.phase_execution s keys cmd scene actor index sync found supported lookup
  rw [ordinary_result kind s q index valid special] at run
  refine ⟨q,run,words,x,y,z,?_⟩
  simp [Simulation.floorDamageRequest,x,y,z,lookup,special,Except.map,Functor.map,Except.bind,Except.pure,bind,pure]

/-- Observe the exact request used by the live combat callback, before applying
health/armor/pain/death effects. A failed preparation or lookup has no output. -/
def output (run : Except Simulation (Simulation × Ticcmd)) :
    Option (PreparedState.Words × (Nat × Word × Word)) :=
  match run with
  | .error _ => none
  | .ok (s,_) =>
    match s.floorDamageRequest with
    | .error _ => none
    | .ok (amount,rng) => some (PreparedRuntime.words s.player,
        (amount,BitVec.ofNat 32 rng.play.toNat,BitVec.ofNat 32 rng.misc.toNat))

theorem runtime_observation (kind : Kind) (s : Simulation) (keys : UInt32) (cmd : Ticcmd)
    (scene : Scene) (actor : SolidThing) (index : Nat)
    (sync : (SectorRuntime.inputPlayer s).syncScene s.map = .ok scene)
    (found : scene.things[0]? = some actor) (supported : actor.moveFlags.floating = false)
    (lookup : s.map.sectorAt actor.x actor.y = .ok index) (valid : index < s.map.sectors.size)
    (special : s.map.sectors[index]!.special = kind.special) :
    output (s.prepareSectorTick keys (some cmd)) =
      let answer := LevelSpecials.floorDamage kind.special actor.z (Fixed.ofInt s.map.sectors[index]!.floor)
        (s.inventory.suit > 0) (s.ticks-1) s.rng
      some (PreparedState.expected (actor.motion s.player.body) s.player.animation cmd
          s.player.reactionTime s.player.view s.player.levelTime s.player.cachedOnGround true,
        (answer.1,BitVec.ofNat 32 answer.2.play.toNat,BitVec.ofNat 32 answer.2.misc.toNat)) := by
  obtain ⟨q,run,words,_,_,_,request⟩ := phase_execution kind s keys cmd scene actor index sync found supported lookup valid special
  rw [run]
  simp only [output,request,words]

/-- The live continuation receives the updated RNG even when damage is zero.
This quantifies over damage handling without claiming its DOS equivalence. -/
theorem phase_handoff (kind : Kind) (s : Simulation) (keys : UInt32) (cmd : Ticcmd)
    (scene : Scene) (actor : SolidThing) (index : Nat)
    (sync : (SectorRuntime.inputPlayer s).syncScene s.map = .ok scene)
    (found : scene.things[0]? = some actor) (supported : actor.moveFlags.floating = false)
    (lookup : s.map.sectorAt actor.x actor.y = .ok index) (valid : index < s.map.sectors.size)
    (special : s.map.sectors[index]!.special = kind.special)
    (damage : Simulation → Nat → Simulation) :
    ∃ q, s.prepareSectorTick keys (some cmd) = .ok ({ s with player := q },cmd) ∧
      ({ s with player := q } : Simulation).applyFloorEffect damage =
        let answer := LevelSpecials.floorDamage kind.special actor.z (Fixed.ofInt s.map.sectors[index]!.floor)
          (s.inventory.suit > 0) (s.ticks-1) s.rng
        let ready := { s with player := q, rng := answer.2 }
        if answer.1 == 0 then ready else damage ready answer.1 := by
  obtain ⟨q,run,_,_,_,_,request⟩ := phase_execution kind s keys cmd scene actor index sync found supported lookup valid special
  refine ⟨q,run,?_⟩
  simp only [Simulation.applyFloorEffect,request]

/-- Full state at the decision boundary: only player preparation and the RNG
have changed; inventory/suit, tick count and all map sectors still come from s. -/
theorem decision_frame (s : Simulation) (q : Player) (rng : DoomRandom) :
    ({ s with player := q, rng } : Simulation).inventory = s.inventory ∧
    ({ s with player := q, rng } : Simulation).ticks = s.ticks ∧
    ({ s with player := q, rng } : Simulation).map = s.map ∧
    ({ s with player := q, rng } : Simulation).secrets = s.secrets := by
  exact ⟨rfl,rfl,rfl,rfl⟩

def machineOutput (s : X86Memory.State) (t : X86Control.State) :=
  (PreparedState.read (s.regs 2) (PlayerCaller.object s) t.core.memory,FloorDamage.observe t)

/-- The original-byte joined path agrees with the actual request read by
Simulation.hurtFromFloor after the shared live preparation phase. -/
theorem correspondence (kind : Kind) (machine : X86Memory.State) (flags : Option Flags)
    (s : Simulation) (keys : UInt32) (cmd : Ticcmd) (scene : Scene) (actor : SolidThing) (index : Nat)
    (sync : (SectorRuntime.inputPlayer s).syncScene s.map = .ok scene)
    (found : scene.things[0]? = some actor) (supported : actor.moveFlags.floating = false)
    (lookup : s.map.sectorAt actor.x actor.y = .ok index) (valid : index < s.map.sectors.size)
    (special : s.map.sectors[index]!.special = kind.special)
    (h : FloorJoined.Inputs kind machine (actor.motion s.player.body) s.player.animation cmd s.player.reactionTime
      s.player.view s.player.levelTime s.player.cachedOnGround true (Fixed.ofInt s.map.sectors[index]!.floor)
      (s.ticks-1) (s.inventory.suit > 0) s.rng) :
    (X86CodeMemory.run FloorJoined.cm FloorJoined.program FloorDamage.exits 267
      ⟨machine,flags,0x333b1⟩).map (machineOutput machine) =
      output (s.prepareSectorTick keys (some cmd)) := by
  obtain ⟨t,run,words,damage,_,_,_⟩ := FloorJoined.execution kind machine flags (actor.motion s.player.body)
    s.player.animation cmd s.player.reactionTime s.player.view s.player.levelTime s.player.cachedOnGround true
    (Fixed.ofInt s.map.sectors[index]!.floor) (s.ticks-1) (s.inventory.suit > 0) s.rng h
  rw [run,runtime_observation kind s keys cmd scene actor index sync found supported lookup valid special]
  simp only [Option.map_some,machineOutput,words,damage,SolidThing.motion]

end Doom.Proofs.FloorRuntime
