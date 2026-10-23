import Doom.Proofs.OriginalSectorJoined
import Doom.Proofs.OriginalPreparedRuntime
import Doom.Simulation

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace Doom.Proofs.SectorRuntime
open Verification X86 X86Memory X86Control BlockSummary Collision

/-- The inventory synchronization performed by the live interaction tick. -/
def inputPlayer (s : Simulation) : Player := { s.player with inventory := s.inventory }

/-- Turning/thrust affect momentum, not the position used by sector lookup. -/
theorem position (body : Motion) (timer : Int32) (cmd : Ticcmd) :
    (PlayerReaction.move body timer cmd).x = body.x ∧
    (PlayerReaction.move body timer cmd).y = body.y ∧
    (PlayerReaction.move body timer cmd).z = body.z := by
  by_cases ht : timer = 0 <;> by_cases hg : body.z.raw ≤ body.floorz.raw <;>
    by_cases hf : cmd.forwardMove = 0 <;> by_cases hs : cmd.sideMove = 0 <;>
    by_cases hr : body.frame = 0 <;>
    simp [PlayerReaction.move,Motion.movePlayer,Motion.turn,Motion.thrust,Motion.onGround,ht,hg,hf,hs,hr]

/-- The actual preparation call succeeds, keeps its command, and supplies both
its established eleven fields and the synchronized actor's position. -/
theorem prepare (m : Map) (p : Player) (keys : UInt32) (cmd : Ticcmd)
    (scene : Scene) (actor : SolidThing)
    (sync : p.syncScene m = .ok scene) (found : scene.things[0]? = some actor)
    (supported : actor.moveFlags.floating = false) :
    ∃ q, p.prepareTick m keys (some cmd) = .ok (q,cmd) ∧
      PreparedRuntime.words q = PreparedState.expected (actor.motion p.body) p.animation cmd p.reactionTime
        p.view p.levelTime p.cachedOnGround true ∧
      q.body.x = actor.x ∧ q.body.y = actor.y ∧ q.body.z = actor.z := by
  have pos := position (actor.motion p.body) p.reactionTime cmd
  simp only [Player.prepareTick,sync,Scene.preparePlayerPhysics,found,supported,
    Except.bind,Except.pure,bind,pure,Bool.false_eq_true,↓reduceIte]
  refine ⟨_,rfl,?_,pos.1,pos.2.1,pos.2.2⟩
  simp [PreparedRuntime.words,PreparedState.expected,PlayerGround.ground,Motion.onGround]

/-- Factoring the live phase preserves the previous inline control flow for
any continuation, including which player is retained on each failure. -/
theorem phase_continuation (s : Simulation) (keys : UInt32) (command : Option Ticcmd)
    (next : Simulation → Ticcmd → Simulation) :
    (match s.prepareSectorTick keys command with
      | .error failed => failed
      | .ok (out,cmd) => next out cmd) =
    (match (inputPlayer s).prepareTick s.map keys command with
      | .error error => { s with physicsError := some error }
      | .ok (player,cmd) =>
        match ({ s with player } : Simulation).discoverSecret with
        | .error error => { s with player,physicsError := some error }
        | .ok out => next out cmd) := by
  cases hp : (inputPlayer s).prepareTick s.map keys command with
  | error error =>
    simp only [inputPlayer] at hp
    simp [Simulation.prepareSectorTick,hp]
  | ok pair =>
    rcases pair with ⟨player,cmd⟩
    simp only [inputPlayer] at hp
    cases hs : ({ s with player } : Simulation).discoverSecret <;>
      simp [Simulation.prepareSectorTick,hp,hs]

/-- Full simulation state produced at this phase boundary: only the prepared
player, secret count, and selected sector record are replaced. -/
def result (s : Simulation) (q : Player) (index : Nat) : Simulation :=
  let sector := s.map.sectors[index]!
  let (special,secrets) := LevelSpecials.secret sector.special q.body.z (Fixed.ofInt sector.floor) s.secrets
  { s with
    player := q, secrets := secrets,
    map := { s.map with sectors := s.map.sectors.set! index { sector with special } } }

/-- All premises concern the incoming scene/map. The post-preparation position
and successful secret lookup are derived, not assumed at the handoff. -/
theorem phase_execution (s : Simulation) (keys : UInt32) (cmd : Ticcmd)
    (scene : Scene) (actor : SolidThing) (index : Nat)
    (sync : (inputPlayer s).syncScene s.map = .ok scene)
    (found : scene.things[0]? = some actor) (supported : actor.moveFlags.floating = false)
    (lookup : s.map.sectorAt actor.x actor.y = .ok index) :
    ∃ q, (inputPlayer s).prepareTick s.map keys (some cmd) = .ok (q,cmd) ∧
      s.prepareSectorTick keys (some cmd) = .ok (result s q index,cmd) ∧
      PreparedRuntime.words q = PreparedState.expected (actor.motion s.player.body) s.player.animation cmd
        s.player.reactionTime s.player.view s.player.levelTime s.player.cachedOnGround true ∧
      q.body.x = actor.x ∧ q.body.y = actor.y ∧ q.body.z = actor.z := by
  obtain ⟨q,call,words,x,y,z⟩ := prepare s.map (inputPlayer s) keys cmd scene actor sync found supported
  refine ⟨q,call,?_,words,x,y,z⟩
  simp only [inputPlayer] at call
  simp [Simulation.prepareSectorTick,call,Simulation.discoverSecret,x,y,lookup,result,
    Except.bind,Except.pure,bind,pure]

/-- The live phase preserves the command, RNG, inventory, clock, errors, and
all other sector records. This follows from the actual returned state. -/
theorem phase_frame (s out : Simulation) (keys : UInt32) (cmd actualCmd : Ticcmd)
    (scene : Scene) (actor : SolidThing) (index : Nat)
    (sync : (inputPlayer s).syncScene s.map = .ok scene)
    (found : scene.things[0]? = some actor) (supported : actor.moveFlags.floating = false)
    (lookup : s.map.sectorAt actor.x actor.y = .ok index)
    (run : s.prepareSectorTick keys (some cmd) = .ok (out,actualCmd)) :
    actualCmd = cmd ∧ out.rng = s.rng ∧ out.inventory = s.inventory ∧
      out.ticks = s.ticks ∧ out.physicsError = s.physicsError ∧
      out.map.sectors.size = s.map.sectors.size ∧
      (∀ j, index ≠ j → out.map.sectors[j]! = s.map.sectors[j]!) := by
  obtain ⟨q,_,executed,_⟩ := phase_execution s keys cmd scene actor index sync found supported lookup
  rw [executed] at run
  obtain ⟨rfl,rfl⟩ := Except.ok.inj run
  refine ⟨rfl,rfl,rfl,rfl,rfl,Array.size_set! _ _ _,?_⟩
  intro j different
  exact Array.getElem!_set!_ne _ _ _ _ different

/-- Failed live phases have no fabricated observation. The successful result
is read from the actual Player and updated map sector, not recomputed helpers. -/
def output (index : Nat) (run : Except Simulation (Simulation × Ticcmd)) :
    Option (PreparedState.Words × BitVec 16 × Word) :=
  match run with
  | .error _ => none
  | .ok (s,_) => some (PreparedRuntime.words s.player,
      BitVec.ofNat 16 s.map.sectors[index]!.special,s.secrets.toBitVec)

theorem runtime_observation (s : Simulation) (keys : UInt32) (cmd : Ticcmd)
    (scene : Scene) (actor : SolidThing) (index : Nat)
    (sync : (inputPlayer s).syncScene s.map = .ok scene)
    (found : scene.things[0]? = some actor) (supported : actor.moveFlags.floating = false)
    (lookup : s.map.sectorAt actor.x actor.y = .ok index) (valid : index < s.map.sectors.size)
    (secret : s.map.sectors[index]!.special = 9) :
    output index (s.prepareSectorTick keys (some cmd)) =
      some (PreparedState.expected (actor.motion s.player.body) s.player.animation cmd
        s.player.reactionTime s.player.view s.player.levelTime s.player.cachedOnGround true,
        BitVec.ofNat 16 (LevelSpecials.secret 9 actor.z (Fixed.ofInt s.map.sectors[index]!.floor) s.secrets).1,
        (LevelSpecials.secret 9 actor.z (Fixed.ofInt s.map.sectors[index]!.floor) s.secrets).2.toBitVec) := by
  obtain ⟨q,_,run,words,_,_,z⟩ := phase_execution s keys cmd scene actor index sync found supported lookup
  rw [run]
  simp only [output,result,Array.getElem!_set!_self _ _ _ valid,words,z,secret]

def machineOutput (s : X86Memory.State) (t : X86Control.State) :
    PreparedState.Words × BitVec 16 × Word :=
  (PreparedState.read (s.regs 2) (PlayerCaller.object s) t.core.memory,
    load16 t.core.memory (SectorDispatch.sector s+(14#32)),load32 t.core.memory (s.regs 2+(212#32)))

/-- Original-byte preparation through secret-handler return agrees with the
actual phase used by Simulation.interactionTick. The DOS entry relation and
successful initial scene/BSP lookup are explicit; this is not a whole-tic claim. -/
theorem correspondence (machine : X86Memory.State) (flags : Option Flags)
    (s : Simulation) (keys : UInt32) (cmd : Ticcmd) (scene : Scene) (actor : SolidThing) (index : Nat)
    (sync : (inputPlayer s).syncScene s.map = .ok scene)
    (found : scene.things[0]? = some actor) (supported : actor.moveFlags.floating = false)
    (lookup : s.map.sectorAt actor.x actor.y = .ok index) (valid : index < s.map.sectors.size)
    (secret : s.map.sectors[index]!.special = 9)
    (h : SectorJoined.Inputs machine (actor.motion s.player.body) s.player.animation cmd s.player.reactionTime
      s.player.view s.player.levelTime s.player.cachedOnGround true
      (Fixed.ofInt s.map.sectors[index]!.floor) s.secrets) :
    (X86CodeMemory.run (SectorEntry.codeMemory SectorEntry.tableBytes) SectorJoined.program [0x333e5] 256
      ⟨machine,flags,0x333b1⟩).map (machineOutput machine) =
      output index (s.prepareSectorTick keys (some cmd)) := by
  obtain ⟨t,run,_,words,fields,_,_⟩ := SectorJoined.execution machine flags (actor.motion s.player.body)
    s.player.animation cmd s.player.reactionTime s.player.view s.player.levelTime s.player.cachedOnGround true
    (Fixed.ofInt s.map.sectors[index]!.floor) s.secrets h
  rw [run,runtime_observation s keys cmd scene actor index sync found supported lookup valid secret]
  simp only [Prod.mk.injEq] at fields
  simp only [Option.map_some,machineOutput,words,fields.1,fields.2,SolidThing.motion]

end Doom.Proofs.SectorRuntime
