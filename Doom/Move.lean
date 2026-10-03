/-
Player P_TryMove and ordered P_UnsetThingPosition/P_SetThingPosition semantics,
Chocolate Doom 3.1.1, commit 410d96855b5df5410ff591a90efeafa889119224.
Derived from id Software (1993-1996), Simon Howard (2005-2014).
SPDX-License-Identifier: GPL-2.0-or-later. See COPYING.md.
-/
import Doom.Collision

namespace Doom.Collision

abbrev SectorAt := Fixed → Fixed → Except String Nat

private def blockIndex (scene : Scene) (thing : SolidThing) : Option Nat :=
  let x := blockCoordinate thing.x (Fixed.ofInt scene.grid.origin.x)
  let y := blockCoordinate thing.y (Fixed.ofInt scene.grid.origin.y)
  if x < 0 || y < 0 || x ≥ scene.grid.width || y ≥ scene.grid.height then none
  else some (y.toNat * scene.grid.width + x.toNat)

private def containsActor (lists : Array (Array Nat)) (id : Nat) : Bool :=
  lists.any (·.contains id)

/-- Link an unlinked actor at both list heads. Subsector membership changes even
with NOSECTOR. The resolver is the caller's pure BSP lookup. -/
def Scene.linkThing (scene : Scene) (id : Nat) (sectorAt : SectorAt) : Except String Scene := do
  let some thing := scene.things[id]? | throw "move: invalid actor"
  if thing.removed then throw "move: cannot link a removed actor"
  if containsActor scene.links id || containsActor scene.sectorLinks id then
    throw "move: actor is already linked"
  let sector ← sectorAt thing.x thing.y
  if sector ≥ scene.sectors.size || scene.sectorLinks.size != scene.sectors.size then
    throw "move: invalid sector membership"
  let thing := { thing with sector }
  let mut scene := { scene with things := scene.things.set! id thing }
  if !thing.moveFlags.noSector then
    scene := { scene with sectorLinks := scene.sectorLinks.set! sector (#[id] ++ scene.sectorLinks[sector]!) }
  if !thing.moveFlags.noBlockmap then
    if let some cell := blockIndex scene thing then
      let some ids := scene.links[cell]? | throw "move: missing block cell"
      scene := { scene with links := scene.links.set! cell (#[id] ++ ids) }
  return scene

private def removeActor (lists : Array (Array Nat)) (cell id : Nat) : Except String (Array (Array Nat)) := do
  let some ids := lists[cell]? | throw "move: missing actor list"
  if (ids.filter (· == id)).size != 1 then throw "move: inconsistent actor linkage"
  return lists.set! cell (ids.filter (· != id))

/-- Preserve all other list members and their order; reject corrupt linkage
instead of attempting to emulate arbitrary C pointer corruption. -/
def Scene.unlinkThing (scene : Scene) (id : Nat) : Except String Scene := do
  let some thing := scene.things[id]? | throw "move: invalid actor"
  if thing.removed then
    if containsActor scene.links id || containsActor scene.sectorLinks id then
      throw "move: removed actor is still linked"
    return scene
  let mut scene := scene
  if !thing.moveFlags.noSector then
    scene := { scene with sectorLinks := ← removeActor scene.sectorLinks thing.sector id }
  if !thing.moveFlags.noBlockmap then
    if let some cell := blockIndex scene thing then
      scene := { scene with links := ← removeActor scene.links cell id }
  if containsActor scene.links id || containsActor scene.sectorLinks id then
    throw "move: actor linked outside its expected lists"
  return scene

structure MoveDecision where
  accepted : Bool
  floatOK : Bool
  deriving BEq, Repr

/-- Original guard order, including the intermediate floatok result. Every
height difference is signed 32-bit subtraction, not unbounded arithmetic. -/
def moveDecision (thing : SolidThing) (position : PositionResult) : MoveDecision :=
  if !position.clear then ⟨false, false⟩
  else if thing.moveFlags.noClip then ⟨true, false⟩
  else if (position.ceiling - position.floor).raw < thing.height.raw then ⟨false, false⟩
  else if !thing.moveFlags.teleport &&
      (position.ceiling - thing.z).raw < thing.height.raw then ⟨false, true⟩
  else if !thing.moveFlags.teleport &&
      (position.floor - thing.z).raw > 1572864 then ⟨false, true⟩
  else if !(thing.moveFlags.dropoff || thing.moveFlags.floating) &&
      (position.floor - position.dropoff).raw > 1572864 then ⟨false, true⟩
  else ⟨true, true⟩

structure Crossing where
  line : Nat
  oldSide : Bool
  actor : Nat
  x : Fixed
  y : Fixed
  sector : Nat
  deriving BEq, Repr

structure MoveResult where
  scene : Scene
  decision : MoveDecision
  position : PositionResult
  crossings : Array Crossing := #[]

/-- Player P_TryMove with immediate special callbacks after relinking. The
callback can change line specials/actor positions, which are re-read for the next
contact. It must not perform a nested position query that overwrites vanilla's
global spechit scratch state; such special handlers remain outside this port's
verified domain. Pickup effects survive failed moves; missiles/skulls are excluded. -/
def Scene.tryMove (scene : Scene) (id : Nat) (x y : Fixed) (sectorAt : SectorAt)
    (cross : Scene → Crossing → Except String Scene) (player : Bool := true) : Except String MoveResult := do
  let some thing := scene.things[id]? | throw "move: invalid actor"
  let sector ← sectorAt x y
  let some heights := scene.sectors[sector]? | throw "move: invalid destination sector"
  let (scene, position) ← scene.checkPositionWithEffects {
    x, y, radius := thing.radius, self := some id
    noClip := thing.moveFlags.noClip, player } heights
  let decision := moveDecision thing position
  if !decision.accepted then return ⟨scene, decision, position, #[]⟩
  let mut scene ← scene.unlinkThing id
  let moved := { thing with x, y, floor := position.floor, ceiling := position.ceiling }
  scene := { scene with things := scene.things.set! id moved }
  scene ← scene.linkThing id sectorAt
  let mut crossings := #[]
  if !(thing.moveFlags.teleport || thing.moveFlags.noClip) then
    for i in [:position.specials.size] do
      let lineId := position.specials[position.specials.size - 1 - i]!
      let some line := scene.lines[lineId]? | throw "move: callback removed a contacted line"
      let some current := scene.things[id]? | throw "move: callback removed moving actor"
      let oldSide := line.pointSide thing.x thing.y
      if line.pointSide current.x current.y != oldSide && line.special then
        let event : Crossing := ⟨lineId, oldSide, id, current.x, current.y, current.sector⟩
        crossings := crossings.push event
        scene ← cross scene event
  return ⟨scene, decision, position, crossings⟩

end Doom.Collision
