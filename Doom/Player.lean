import Doom.Controls
import Doom.WorldPhysics
import Doom.HeightClip
import Doom.ActorFlags
import Doom.Inventory
import Doom.PlayerAnim

namespace Doom
open Collision

/-- Runtime adapter for the reference-tested movement core. Camera/feet are
render/UI projections; fixed body and scene state are authoritative. Other
simulation systems (doors, combat and actors) are still prototype systems. -/
structure Player where
  inventory : Inventory := {}
  camera : Camera
  feet : Float
  velocityZ : Float := 0
  body : Motion := {}
  animation : PlayerAnim.State := {}
  reactionTime : Int32 := 0
  cachedOnGround : Bool := false
  view : ViewState := {}
  keyboard : KeyboardState := {}
  scene : Option Scene := none
  mapActors : Array Thing := #[]
  levelTime : Int32 := 0
  landingEvents : Nat := 0
  crossings : Array Crossing := #[]
  frictionSample : Option FrictionSample := none
  deriving Inhabited

private def mapActor (m : Map) (t : Thing) : Except String SolidThing := do
  let x := Fixed.ofInt t.position.x
  let y := Fixed.ofInt t.position.y
  let sector ← m.sectorAt x y
  let some sec := m.sectors[sector]? | throw "player: invalid actor sector"
  let spec := (thingDef t.kind).getD default
  let solid := t.active && spec.solid
  let pickup := if t.active then Pickup.itemOfEditor? t.kind else none
  let flags := actorFlags t.kind
  let linked := t.active && flags.isSome && (thingDef t.kind).isSome
  return {
    kind := t.kind, pickup, x, y, radius := Fixed.ofInt spec.radius, solid, sector,
    -- Disabled map slots also represent already removed pickups. Rebuilding
    -- one after its flags change must not resurrect an inert actor in the scene.
    removed := !t.active,
    z := Fixed.ofInt (if spec.ceiling then sec.ceiling - spec.height else sec.floor),
    height := Fixed.ofInt spec.height, floor := Fixed.ofInt sec.floor,
    ceiling := Fixed.ofInt sec.ceiling,
    health := flags.map (·.health) |>.getD 1000,
    shootable := t.active && flags.any (·.shootable),
    moveFlags := { noSector := !linked || flags.any (·.noSector), noBlockmap := !linked || flags.any (·.noBlockmap) } }

def Player.spawn (m : Map) : Except String Player := do
  let camera ← Camera.spawn m
  let some start := m.things.findIdx? (·.kind == 1) | throw "map has no player 1 start"
  let sector ← m.sectorAt camera.x camera.y
  let sec := m.sectors[sector]!
  -- P_SpawnPlayer reads a signed mapthing angle, then truncates to ANG45 steps.
  let degrees := (Int16.ofInt m.things[start]!.angle).toInt
  let angle : Angle := ⟨(Int32.ofInt (degrees.tdiv 45)).toUInt32 * 0x20000000⟩
  let body : Motion := {
    x := camera.x, y := camera.y, z := Fixed.ofInt sec.floor, angle,
    floorz := Fixed.ofInt sec.floor, ceilingz := Fixed.ofInt sec.ceiling }
  let mut scene ← Scene.fromMap m
  if !scene.grid.vanillaOffsets then throw "player: BLOCKMAP outside the vanilla profile"
  let actor : SolidThing := {
    x := body.x, y := body.y, z := body.z, radius := Fixed.ofInt 16, canPickup := true,
    floor := body.floorz, ceiling := body.ceilingz, health := 100, shootable := true,
    moveFlags := { dropoff := true } }
  scene := { scene with
    things := #[actor] ++ (← m.things.mapM (mapActor m)),
    pickupPlayer := some { actor := 0, profile := { commercial := m.name.startsWith "MAP" } } }
  -- Spawn links in map order; the player slot remains stable at index zero.
  for i in [:m.things.size] do
    let id := if i == start then 0 else i+1
    if !scene.things[id]!.removed then scene ← scene.linkThing id m.sectorAt
  return {
    camera := { camera with angle }, feet := body.z.toFloat, body,
    -- G_PlayerReborn zeroes viewz; P_CalcHeight first computes it during play.
    view := { z := ⟨0⟩ }, scene := some scene, mapActors := m.things }

private def number (n : Int) : Float := n.toInt64.toFloat

def segmentDistanceSq (x y : Float) (a b : Vertex) : Float :=
  let dx := number (b.x - a.x)
  let dy := number (b.y - a.y)
  let px := x - number a.x
  let py := y - number a.y
  let length := dx*dx + dy*dy
  let t := if length == 0 then 0 else max 0 (min 1 ((px*dx + py*dy) / length))
  (px-t*dx)*(px-t*dx) + (py-t*dy)*(py-t*dy)

/-- Mirror external prototype map changes without rebuilding actor-list order.
Only actors whose position/identity/activation changed are unlinked/relinked.
Consumed items are already unlinked by the collision core. -/
def Player.syncScene (p : Player) (m : Map) : Except String Scene := do
  let some original := p.scene | throw "player: missing collision scene"
  if m.things.size < p.mapActors.size then throw "player: removed actor slots"
  let sectors := m.sectors.map fun s => (⟨Fixed.ofInt s.floor, Fixed.ofInt s.ceiling⟩ : Heights)
  let mut lines := original.lines
  if lines.size != m.lines.size || sectors.size != original.sectors.size then
    throw "player: map topology changed"
  for i in [:lines.size] do
    let l := m.lines[i]!
    let front := sectors[m.sides[l.front]!.sector]!
    let back := if l.back < m.sides.size then some sectors[m.sides[l.back]!.sector]! else none
    lines := lines.set! i { lines[i]! with
      front, back, special := l.special != 0,
      blocking := l.flags &&& 1 != 0, twoSided := l.flags &&& 4 != 0, blockMonsters := l.flags &&& 2 != 0 }
  let mut scene := { original with lines, sectors }
  for i in [:m.things.size] do
    let t := m.things[i]!
    if let some old := p.mapActors[i]? then
      if old.position.x == t.position.x && old.position.y == t.position.y &&
          old.kind == t.kind && old.flags == t.flags then continue
      scene ← scene.unlinkThing (i+1)
      scene := { scene with things := scene.things.set! (i+1) (← mapActor m t) }
    else
      scene := { scene with things := scene.things.push (← mapActor m t) }
    if !scene.things[i+1]!.removed then scene ← scene.linkThing (i+1) m.sectorAt
  return scene

/-- SDL key-mask adapter to the separately reference-tested keyboard builder. -/
def walkingKeys (keys : UInt32) : MovementKeys := {
  forward := keyDown keys 2, backward := keyDown keys 4,
  left := keyDown keys 32, right := keyDown keys 64,
  strafeLeft := keyDown keys 8, strafeRight := keyDown keys 16,
  speed := keyDown keys 512, attack := keyDown keys 8192, use := keyDown keys 4096 }

/-- Prepare the command and view without advancing the player's position.
The runtime runs use/fire and counters between this and moveTick. -/
def Player.prepareTick (m : Map) (p : Player) (keys : UInt32)
    (command : Option Ticcmd := none) : Except String (Player × Ticcmd) := do
  let scene ← p.syncScene m
  let (cmd, keyboard) := match command with
    | some cmd => (cmd, p.keyboard)
    | none => p.keyboard.build (walkingKeys keys)
  let result ← scene.preparePlayerPhysics 0 p.body p.view cmd p.levelTime p.reactionTime p.cachedOnGround
  let animation := PlayerReaction.animate p.animation p.reactionTime cmd
  return ({ p with
    body := result.body, view := result.view, keyboard, animation,
    reactionTime := PlayerReaction.remaining p.reactionTime, cachedOnGround := result.onGround,
    camera := ⟨result.body.x, result.body.y, result.view.z, result.body.angle⟩,
    scene := some result.scene, mapActors := m.things }, cmd)

/-- Advance the prepared player's mobj. Resynchronize after player actions so
weapon damage, removed actors and changed inventory survive into collision. -/
def Player.moveTick (m : Map) (p : Player) (cmd : Ticcmd) (dropped : Array Nat := #[])
    (lighting : Option SectorLights.World := none) : Except String Player := do
  let mut scene ← p.syncScene m
  let some collector := scene.pickupPlayer | throw "player: missing pickup state"
  scene := { scene with pickupPlayer := some { collector with state := p.inventory.toPickup }, pickupEvents := #[], lighting }
  for index in dropped do
    let some thing := scene.things[index+1]? | throw "player: invalid dropped item"
    if let some item := thing.pickup then
      scene := { scene with things := scene.things.set! (index+1) { thing with pickup := some { item with dropped := true } } }
  let result ← scene.movePlayerPhysics 0 p.body p.view cmd m.sectorAt
    (fun current event => do
      let some world := current.lighting | return current
      let world ← world.crossAll event.line (current.pickupPlayer.any (·.actor == event.actor))
      let some line := current.lines[event.line]? | throw "player: crossed line disappeared"
      return { current with
        lighting := some world
        lines := current.lines.set! event.line { line with special := world.map.lines[event.line]!.special != 0 } }) (p.inventory.health == 0)
  let body := result.body
  let stopped := result.frictionSample.any fun f =>
    f.after.momx.raw == 0 && f.after.momy.raw == 0 &&
    f.before.z.raw ≤ f.before.floorz.raw && cmd.forwardMove == 0 && cmd.sideMove == 0
  let animation := if stopped && p.animation.frame ≥ 150 && p.animation.frame ≤ 153
    then (PlayerAnim.enter 149).1 else p.animation
  let some collector := result.scene.pickupPlayer | throw "player: lost pickup state"
  return { p with
    inventory := Inventory.fromPickup collector.state,
    camera := ⟨body.x, body.y, result.view.z, body.angle⟩,
    feet := body.z.toFloat, velocityZ := body.momz.toFloat, body, animation,
    view := result.view, scene := some result.scene, mapActors := m.things,
    levelTime := p.levelTime + 1, landingEvents := p.landingEvents + (if result.landing then 1 else 0),
    crossings := result.crossings, frictionSample := result.frictionSample }

/-- Movement-only adapter. Gameplay uses the split entry points to interleave
player actions at the original PlayerThink / mobj-thinker boundary. -/
def Player.tick (m : Map) (p : Player) (keys : UInt32) (dropped : Array Nat := #[])
    (lighting : Option SectorLights.World := none) (command : Option Ticcmd := none) : Except String Player := do
  let (p, cmd) ← p.prepareTick m keys command
  ({ p with inventory := p.inventory.tick } : Player).moveTick m cmd dropped lighting

end Doom
