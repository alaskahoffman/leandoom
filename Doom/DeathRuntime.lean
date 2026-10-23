import Doom.Simulation

namespace Doom

/-- Death adapter state for the single-player runtime; exposed for correspondence proofs. -/
def Simulation.deathWorld (s : Simulation) : Death.World := {
  players := s.deathStats, rng := s.rng, commercial := s.map.name.startsWith "MAP" }

private def Simulation.deathResult (s : Simulation) (id : Nat) (body : Death.Body)
    (world : Death.World) : Except String Simulation := do
  let mut s := { s with
    rng := world.rng, deathStats := world.players
    kills := world.players[0].kills.toInt.toNat }
  let firstDrop := s.map.things.size
  for event in world.events do
    s := { s with deathEvents := s.deathEvents.push (id,event) }
    if let .sound name global := event then
      s := if global then s.soundAt name none ⟨s.player.body.x,s.player.body.y⟩ else s.sound name (.actor id)
    if let .drop editor := event then
      -- P_SpawnMobj initializes lastlook with P_Random()%MAXPLAYERS, even
      -- for inert items. The drop has no AI, but the shared RNG draw matters.
      let (_,rng) := s.rng.nextPlay
      let target := s.map.things[id-1]!
      let dropped := s.map.things.size
      s := s.dosSpawn s!"thing:{dropped}" 154
      s := { s with
        rng, dropped := s.dropped.push dropped
        map := { s.map with things := s.map.things.push { target with kind := editor, angle := 0 } } }
  let mut scene ← s.player.syncScene s.map
  let some old := scene.things[id]? | throw "death: missing runtime actor"
  -- P_KillMobj passes the victim's exact fixed-point XY to P_SpawnMobj,
  -- with ONFLOORZ. The integer THINGS proxy cannot represent that position.
  for index in [firstDrop:s.map.things.size] do
    let dropId := index+1
    let dropped := scene.things[dropId]!
    let sector ← s.map.sectorAt old.x old.y
    let heights := scene.sectors[sector]!
    scene ← scene.unlinkThing dropId
    scene := { scene with things := scene.things.set! dropId { dropped with
      x := old.x, y := old.y, z := heights.floor,
      floor := heights.floor, ceiling := heights.ceiling,
      pickup := dropped.pickup.map (fun item => { item with dropped := true }) } }
    scene ← scene.linkThing dropId s.map.sectorAt
  let thing := { old with
    health := body.health, height := body.height
    solid := body.flags &&& 2 != 0, shootable := body.flags &&& 4 != 0,
    moveFlags := { old.moveFlags with dropoff := body.flags &&& 0x400 != 0, floating := body.flags &&& 0x4000 != 0 } }
  scene := { scene with things := scene.things.set! id thing }
  if body.removed then
    s := s.stopSound (.actor id)
    scene ← scene.unlinkThing id
    scene := { scene with things := scene.things.set! id { thing with removed := true, solid := false } }
    if id > 0 then
      s := { s with map := { s.map with things := s.map.things.set! (id-1) { s.map.things[id-1]! with flags := 0 } } }
  let player := { s.player with scene := some scene, mapActors := s.map.things }
  let player := if id == 0 then { player with body := { player.body with height := body.height, noGravity := body.flags &&& 0x200 != 0 } } else player
  return { s with player }

/-- Preserve the actor's identity and links. Solidity changes at A_Fall, not at
kill time; quarter-height corpses and signed health feed sector clipping. -/
def Simulation.killActor (s : Simulation) (index : Nat) (health : Int32)
    (source : Option (Option (Fin 4))) : Except String Simulation := do
  let actor := s.actors[index]!
  let some info := Death.info actor.kind | throw "death: unsupported actor type"
  let scene ← s.player.syncScene s.map
  let thing := scene.things[actor.thing+1]!
  let body : Death.Body := { kind := actor.kind, health, flags := info.flags, height := thing.height, info }
  let (body,world) ← Death.kill Death.frames body { s.deathWorld with source }
  let s ← s.deathResult (actor.thing+1) body world
  return { s with actors := s.actors.set! index { actor with health := 0, mode := .dying, age := 0, death := some body } }

def Simulation.killPlayer (s : Simulation) (health : Int32)
    (source : Option (Option (Fin 4))) : Except String Simulation := do
  let some info := Death.info 0 | throw "death: missing player metadata"
  let body : Death.Body := { kind := 0, player := some 0, health, flags := info.flags, height := s.player.body.height, info }
  let (body,world) ← Death.kill Death.frames body { s.deathWorld with source }
  let s ← s.deathResult 0 body world
  return { s with playerDeath := some body }

/-- Tick a corpse at its existing slot in the adapter's actor loop. Full vanilla
thinker interleaving and corpse XY/Z motion remain separate work. -/
def Simulation.tickCorpse (s : Simulation) (index : Nat) : Except String Simulation := do
  let actor := s.actors[index]!
  let some body := actor.death | return s
  if body.removed then return s
  if s.gibbed.contains actor.thing then return s
  let (body,world) ← Death.tick Death.frames body s.deathWorld
  let s ← s.deathResult (actor.thing+1) body world
  return { s with actors := s.actors.set! index { actor with death := some body, age := actor.age+1 } }

def Simulation.tickPlayerCorpse (s : Simulation) : Except String Simulation := do
  let some body := s.playerDeath | return s
  let (body,world) ← Death.tick Death.frames body s.deathWorld
  let s ← s.deathResult 0 body world
  return { s with playerDeath := some body }

end Doom
