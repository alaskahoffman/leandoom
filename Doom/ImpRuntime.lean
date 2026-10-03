import Doom.DeathRuntime
import Doom.Sight

namespace Doom
open Collision

def Simulation.impThing (s : Simulation) (id : Nat) : Except String SolidThing := do
  let scene ← s.player.syncScene s.map
  let some thing := scene.things[id]? | throw "imp: missing actor"
  let health := if id == 0 then Int32.ofNat s.inventory.health
    else (s.actors.find? (·.thing == id-1)).map (fun a => Int32.ofNat a.health) |>.getD thing.health
  return { thing with health }

private def impMove (s : Simulation) (a : Imp.State) : Except String (Simulation × Imp.State × Bool) := do
  if a.movedir == 8 then return (s,a,false)
  if a.movedir > 8 then throw "imp: invalid move direction"
  let scene ← s.player.syncScene s.map
  let body := scene.things[a.id]!
  let xs : Array Int32 := #[65536,47000,0,-47000,-65536,-47000,0,47000]
  let ys : Array Int32 := #[0,47000,65536,47000,0,-47000,-65536,-47000]
  let lighting : SectorLights.World := {
    map := s.map, thinkers := s.lights, rng := s.rng,
    busy := s.doors.map (·.sector) ++ s.movers.map (·.sector), movers := s.movers, moverSounds := s.moverSounds }
  let scene := { scene with lighting := some lighting }
  let result ← scene.tryMove a.id (body.x+⟨8*xs[a.movedir]!⟩) (body.y+⟨8*ys[a.movedir]!⟩) s.map.sectorAt
    (fun scene event => do
      let some world := scene.lighting | return scene
      let world ← world.crossAll event.line false
      return { scene with
        lighting := some world,
        lines := scene.lines.set! event.line { scene.lines[event.line]! with special := world.map.lines[event.line]!.special != 0 } }) false
  let mut s := s
  if !result.decision.accepted then
    if result.position.specials.isEmpty then return (s,a,false)
    let mut good := false
    for line in result.position.specials.reverse do
      let (next,ok) := s.monsterUse line
      s := next; good := good || ok
    return (s,{ a with movedir := 8 },good)
  if let some world := result.scene.lighting then
    s := { s with map := world.map, movers := world.movers, moverSounds := world.moverSounds }
  let body := result.scene.things[a.id]!
  let body := { body with z := body.floor }
  let scene := { result.scene with things := result.scene.things.set! a.id body }
  let index := a.id-1
  let thing := s.map.things[index]!
  let map := { s.map with things := s.map.things.set! index { thing with position := ⟨body.x.raw.toInt/65536,body.y.raw.toInt/65536⟩ } }
  return ({ s with map, player := { s.player with scene := some scene, mapActors := map.things } },a,true)

def impHooks : Imp.Hooks Simulation := {
  thing := Simulation.impThing,
  sight := fun s a b => do Sight.check s.map (← s.impThing a) (← s.impThing b),
  shadow := fun s id => id == 0 && s.inventory.pickupState.shadow,
  soundTarget := fun s id => ((s.player.scene.bind (fun scene => scene.things[id]?)).bind (fun thing => s.soundTargets[thing.sector]?.join)),
  move := impMove }

def Simulation.impRun (s : Simulation) (index : Nat) (entry : Option Nat := none) : Except String Simulation := do
  let some imp := s.actors[index]!.imp | throw "imp: missing state"
  let action := match entry with | none => Imp.tick impHooks | some id => Imp.enter impHooks 64 id
  let (_,world) ← action.run { host := s, actor := imp, rng := s.rng }
  let mut s := { world.host with rng := world.rng }
  let actor := s.actors[index]!
  let mode := if #[ImpData.TROO_STND,ImpData.TROO_STND2].contains world.actor.frame then ActorMode.idle
    else if #[ImpData.TROO_PAIN,ImpData.TROO_PAIN2].contains world.actor.frame then .pain
    else if #[ImpData.TROO_ATK1,ImpData.TROO_ATK2,ImpData.TROO_ATK3].contains world.actor.frame then .attack else .chase
  s := { s with actors := s.actors.set! index { actor with imp := some world.actor, mode, age := actor.age+1 } }
  let t := s.map.things[actor.thing]!
  let map := { s.map with things := s.map.things.set! actor.thing { t with angle := world.actor.angle.raw.toNat*360/4294967296 } }
  s := { s with map, player := { s.player with mapActors := map.things } }
  for event in world.events do
    s := { s with impEvents := s.impEvents.push (actor.thing,event) }
    if let .sound name := event then s := s.sound name (.actor (actor.thing+1))
  return s

/-- P_NoiseAlert's sector flood, persistent soundtarget, at most one blocking
line. A fresh traversal revisits a sector if reached using fewer sound blocks. -/
def Simulation.noiseAlert (s : Simulation) : Except String Simulation := do
  let sector ← s.map.sectorAt s.player.body.x s.player.body.y
  let mut stack := [(sector,0)]
  let mut visited := Array.replicate s.map.sectors.size 3
  let mut targets := s.soundTargets
  for _ in [:s.map.lines.size*4+s.map.sectors.size*2+1] do
    let (sector,blocks)::rest := stack | return { s with soundTargets := targets }
    stack := rest
    if visited[sector]! ≤ blocks+1 then continue
    visited := visited.set! sector (blocks+1)
    targets := targets.set! sector (some 0)
    let mut next := #[]
    for line in s.map.lines do
      if line.flags &&& 4 == 0 then continue
      let front := s.map.sides[line.front]!.sector
      let some back := s.map.sides[line.back]? | continue
      if front != sector && back.sector != sector then continue
      let a := s.map.sectors[front]!; let b := s.map.sectors[back.sector]!
      if min a.ceiling b.ceiling ≤ max a.floor b.floor then continue
      let blocking := line.flags &&& 64 != 0
      if blocking && blocks != 0 then continue
      next := next.push (if front == sector then back.sector else front, if blocking then 1 else blocks)
    stack := next.toList ++ stack
  throw "imp: sound traversal exceeded bound"

end Doom
