/-
P_ThingHeightClip from Chocolate Doom 3.1.1 p_map.c,
commit 410d96855b5df5410ff591a90efeafa889119224.
Derived from id Software (1993-1996), Simon Howard (2005-2014).
SPDX-License-Identifier: GPL-2.0-or-later. See COPYING.md.
-/
import Doom.Move

namespace Doom.Collision

/-- Apply the original height adjustment after P_CheckPosition. Its boolean
success is intentionally irrelevant: even an early rejected query supplies the
floor/ceiling limits used here. All sums/differences wrap as signed fixed_t. -/
def SolidThing.clipHeight (thing : SolidThing) (floor ceiling : Fixed) : SolidThing × Bool :=
  let onFloor := thing.z == thing.floor
  let z := if onFloor then floor
    else if (thing.z + thing.height).raw > ceiling.raw then ceiling - thing.height
    else thing.z
  ({ thing with z, floor, ceiling }, (ceiling - floor).raw ≥ thing.height.raw)

structure HeightClipResult where
  scene : Scene
  fits : Bool
  position : PositionResult

/-- Original query-and-adjust sequence for supported inert/player/pickup actors.
The effectful query must run even when it rejects the position. Missile/skull
actions remain outside this query domain; SectorChange adds disposal policy. -/
def Scene.heightClip (scene : Scene) (id : Nat) (sectorAt : SectorAt) (player : Bool := true)
    : Except String HeightClipResult := do
  let some thing := scene.things[id]? | throw "height clip: invalid actor"
  if thing.removed then throw "height clip: removed actor"
  let sector ← sectorAt thing.x thing.y
  let some heights := scene.sectors[sector]? | throw "height clip: invalid sector"
  let (scene,position) ← scene.checkPositionWithEffects {
    x := thing.x, y := thing.y, radius := thing.radius, self := some id,
    noClip := thing.moveFlags.noClip, player } heights
  let (clipped,fits) := thing.clipHeight position.floor position.ceiling
  let clipped := match scene.pickupPlayer with
    | some p => if p.actor == id then { clipped with health := p.state.bodyHealth } else clipped
    | none => clipped
  return { scene := { scene with things := scene.things.set! id clipped }, fits, position }

end Doom.Collision
