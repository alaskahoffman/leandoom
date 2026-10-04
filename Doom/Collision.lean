/-
Player position-check subset of p_map.c and p_maputl.c, Chocolate Doom 3.1.1,
commit 410d96855b5df5410ff591a90efeafa889119224.
Derived from id Software (1993-1996), Simon Howard (2005-2014).
SPDX-License-Identifier: GPL-2.0-or-later. See COPYING.md.
-/
import Doom.Bsp
import Doom.Pickup
import Doom.SectorLights

namespace Doom.Collision

structure Box where
  top : Fixed
  bottom : Fixed
  left : Fixed
  right : Fixed
  deriving Inhabited

inductive Slope where
  | horizontal | vertical | positive | negative
  deriving BEq, Inhabited

structure Heights where
  floor : Fixed
  ceiling : Fixed
  deriving Inhabited

structure Line where
  x : Fixed
  y : Fixed
  dx : Fixed
  dy : Fixed
  bbox : Box
  slope : Slope
  front : Heights
  back : Option Heights := none
  blocking : Bool := false
  special : Bool := false
  twoSided : Bool := false
  blockMonsters : Bool := false
  deriving Inhabited

/-- P_LoadLineDefs uses FixedDiv to classify non-axis slopes. -/
def Line.make (x y x2 y2 : Fixed) (front : Heights) (back : Option Heights)
    (blocking special : Bool) : Except String Line := do
  let dx := x2 - x
  let dy := y2 - y
  let slope ← if dx.raw == 0 then pure Slope.vertical
    else if dy.raw == 0 then pure Slope.horizontal
    else match Fixed.divChecked dy dx with
      | .ok ratio => pure (if ratio.raw > 0 then .positive else .negative)
      | .error e => throw s!"collision: original DOS division fault ({repr e}) in slope classification"
  return ⟨x, y, dx, dy, ⟨⟨max y.raw y2.raw⟩, ⟨min y.raw y2.raw⟩,
      ⟨min x.raw x2.raw⟩, ⟨max x.raw x2.raw⟩⟩, slope, front, back, blocking, special, back.isSome, false⟩

/-- P_PointOnLineSide deliberately lacks R_PointOnSide's sign-bit shortcut. -/
def Line.pointSide (line : Line) (x y : Fixed) : Bool :=
  if line.dx.raw == 0 then
    if x.raw ≤ line.x.raw then line.dy.raw > 0 else line.dy.raw < 0
  else if line.dy.raw == 0 then
    if y.raw ≤ line.y.raw then line.dx.raw < 0 else line.dx.raw > 0
  else
    let left := (⟨line.dy.raw >>> 16⟩ : Fixed) * (x - line.x)
    let right := (y - line.y) * (⟨line.dx.raw >>> 16⟩ : Fixed)
    right.raw ≥ left.raw

/-- none means the box crosses the infinite line; some is side 0/1. -/
def Line.boxSide (line : Line) (box : Box) : Option Bool :=
  let (a, b) := match line.slope with
    | .horizontal => ((box.top.raw > line.y.raw) != (line.dx.raw < 0),
                      (box.bottom.raw > line.y.raw) != (line.dx.raw < 0))
    | .vertical => ((box.right.raw < line.x.raw) != (line.dy.raw < 0),
                    (box.left.raw < line.x.raw) != (line.dy.raw < 0))
    | .positive => (line.pointSide box.left box.top, line.pointSide box.right box.bottom)
    | .negative => (line.pointSide box.right box.top, line.pointSide box.left box.bottom)
  if a == b then some a else none

structure MoveFlags where
  noClip : Bool := false
  teleport : Bool := false
  dropoff : Bool := false
  floating : Bool := false
  noSector : Bool := false
  noBlockmap : Bool := false
  deriving Inhabited

structure SolidThing where
  kind : Nat := 0
  x : Fixed
  y : Fixed
  radius : Fixed
  solid : Bool := true
  z : Fixed := ⟨0⟩
  height : Fixed := Fixed.ofInt 56
  floor : Fixed := ⟨0⟩
  ceiling : Fixed := Fixed.ofInt 128
  sector : Nat := 0
  moveFlags : MoveFlags := {}
  momx : Fixed := ⟨0⟩
  momy : Fixed := ⟨0⟩
  pickup : Option Pickup.Item := none
  canPickup : Bool := false
  removed : Bool := false
  health : Int32 := 1000
  shootable : Bool := false
  dropped : Bool := false
  gibbed : Bool := false
  deriving Inhabited

structure PickupPlayer where
  actor : Nat
  state : Pickup.State := {}
  profile : Pickup.Profile := {}

structure PickupEvent where
  item : Nat
  removed : Bool
  sound : Option Pickup.Sound
  message : String

/-- Cells omit the leading zero as in Map's parser. Line iteration restores it.
Thing lists are supplied in current bnext order, not sorted by actor ID. -/
structure Scene where
  grid : Blockmap
  lines : Array Line
  things : Array SolidThing := #[]
  links : Array (Array Nat)
  sectors : Array Heights := #[]
  sectorLinks : Array (Array Nat) := #[]
  pickupPlayer : Option PickupPlayer := none
  pickupEvents : Array PickupEvent := #[]
  -- Optional runtime special state travels with scene changes during P_TryMove.
  lighting : Option SectorLights.World := none

structure MissileQuery where
  z : Fixed
  height : Fixed
  source : Option Nat
  sourceKind : Nat
  kinds : Array Nat

structure Query where
  x : Fixed
  y : Fixed
  radius : Fixed
  self : Option Nat := none
  noClip : Bool := false
  player : Bool := true
  missile : Option MissileQuery := none

structure PositionResult where
  clear : Bool := true
  floor : Fixed
  ceiling : Fixed
  dropoff : Fixed
  ceilingLine : Option Nat := none
  specials : Array Nat := #[]
  visitedThings : Array Nat := #[]
  visitedLines : Array Nat := #[]
  missileHit : Option Nat := none
  deriving Repr

/-- Subtraction wraps before arithmetic shift by MAPBLOCKSHIFT (23). -/
def blockCoordinate (value origin : Fixed) : Int :=
  (value - origin).raw.toInt / 8388608

private def cellRange (lo hi : Int) (size : Nat) : Std.Legacy.Range :=
  -- Off-grid iterator calls have no effects. Keep x-major/y-minor order while
  -- excluding them, including the case where wrapped endpoints reverse a range.
  let start := (max 0 lo).toNat
  let stop := (min (Int.ofNat size) (hi + 1)).toNat
  { start, stop, step_pos := by decide }

/-- P_CheckPosition for a live player, inert/solid things and original pickups.
Pickup effects are committed before line/height checks; rejection retains them.
No missile, skull, monster, or movement-commit effects. The caller supplies the BSP
destination sector heights. Reject unsupported historical memory/abs overflows. -/
def Scene.checkPositionWithEffects (original : Scene) (query : Query) (sector : Heights)
    : Except String (Scene × PositionResult) := do
  let mut scene := original
  let grid := scene.grid
  if !grid.vanillaOffsets || grid.width ≥ 32768 || grid.height ≥ 32768 then
    throw "collision: unsigned extended BLOCKMAP is outside the vanilla profile"
  if grid.width == 0 || grid.height == 0 || grid.cells.size != grid.width * grid.height ||
      scene.links.size != grid.cells.size then throw "collision: invalid block grid"
  let mut result : PositionResult := { floor := sector.floor, ceiling := sector.ceiling, dropoff := sector.floor }
  if query.noClip then return (scene, result)
  let box : Box := ⟨query.y + query.radius, query.y - query.radius,
                    query.x - query.radius, query.x + query.radius⟩
  let ox := Fixed.ofInt grid.origin.x
  let oy := Fixed.ofInt grid.origin.y
  let margin := Fixed.ofInt 32
  let xl := blockCoordinate (box.left - margin) ox
  let xh := blockCoordinate (box.right + margin) ox
  let yl := blockCoordinate (box.bottom - margin) oy
  let yh := blockCoordinate (box.top + margin) oy
  for bx in cellRange xl xh grid.width do
    for cy in cellRange yl yh grid.height do
      let some ids := scene.links[cy * grid.width + bx]? | throw "collision: missing thing cell"
      for id in ids do
        let some thing := scene.things[id]? | throw "collision: invalid thing link"
        result := { result with visitedThings := result.visitedThings.push id }
        if thing.removed then throw "collision: removed actor is still linked"
        if !thing.solid && thing.pickup.isNone && !thing.shootable then continue
        let dx := (thing.x - query.x).raw.toInt
        let dy := (thing.y - query.y).raw.toInt
        if dx == -2147483648 || dy == -2147483648 then
          throw "collision: unverified abs(INT_MIN) in thing contact"
        let distance := (thing.radius + query.radius).raw.toInt
        if dx.natAbs ≥ distance || dy.natAbs ≥ distance then continue
        if query.self == some id then continue
        if let some missile := query.missile then
          if missile.z.raw > (thing.z+thing.height).raw || (missile.z+missile.height).raw < thing.z.raw then continue
          if missile.source.isSome && missile.sourceKind == missile.kinds[id]! then
            if missile.source == some id then continue
            if missile.kinds[id]! != 0 then return (scene,{ result with clear := false })
          if !thing.shootable then
            if thing.solid then return (scene,{ result with clear := false })
            continue
          return (scene,{ result with clear := false, missileHit := some id })
        if let some item := thing.pickup then
          if let some self := query.self then
            let some toucher := scene.things[self]? | throw "collision: invalid toucher"
            if toucher.canPickup then
              let some player := scene.pickupPlayer | throw "collision: missing pickup player state"
              if player.actor != self then throw "collision: unsupported pickup player"
              let touched := player.state.touch player.profile { item with z := thing.z } toucher.z toucher.height
              scene := { scene with
                pickupPlayer := some { player with state := touched.state },
                pickupEvents := scene.pickupEvents.push ⟨id, touched.removed, touched.sound, touched.state.message⟩ }
              if touched.removed then
                -- P_RemoveMobj unlinks the current node but leaves its bnext;
                -- iterating this cell's captured array preserves that successor.
                scene := { scene with
                  links := scene.links.map (·.filter (· != id)),
                  sectorLinks := scene.sectorLinks.map (·.filter (· != id)),
                  things := scene.things.set! id { thing with removed := true } }
        -- The original caches solidity BEFORE the touch callback removes it.
        if thing.solid then return (scene, { result with clear := false })
  let xl := blockCoordinate box.left ox
  let xh := blockCoordinate box.right ox
  let yl := blockCoordinate box.bottom oy
  let yh := blockCoordinate box.top oy
  let mut seen := Array.replicate scene.lines.size false
  for bx in cellRange xl xh grid.width do
    for cy in cellRange yl yh grid.height do
      let some ids := grid.cells[cy * grid.width + bx]? | throw "collision: missing line cell"
      for id in #[0] ++ ids do
        if id ≥ 32768 then throw "collision: signed BLOCKMAP linedef index is unverified"
        let some line := scene.lines[id]? | throw "collision: invalid block linedef"
        if seen[id]! then continue
        seen := seen.set! id true
        result := { result with visitedLines := result.visitedLines.push id }
        if box.right.raw ≤ line.bbox.left.raw || box.left.raw ≥ line.bbox.right.raw ||
            box.top.raw ≤ line.bbox.bottom.raw || box.bottom.raw ≥ line.bbox.top.raw then continue
        if (line.boxSide box).isSome then continue
        let some back := line.back | return (scene, { result with clear := false })
        if query.missile.isNone && (line.blocking || (!query.player && line.blockMonsters)) then return (scene, { result with clear := false })
        let top := min line.front.ceiling.raw back.ceiling.raw
        let bottom := max line.front.floor.raw back.floor.raw
        let low := min line.front.floor.raw back.floor.raw
        if top < result.ceiling.raw then
          result := { result with ceiling := ⟨top⟩, ceilingLine := some id }
        result := { result with floor := ⟨max bottom result.floor.raw⟩,
                                dropoff := ⟨min low result.dropoff.raw⟩ }
        if line.special then
          if result.specials.size ≥ 8 then throw "collision: spechit overflow profile is unverified"
          result := { result with specials := result.specials.push id }
  return (scene, result)

/-- Read-only diagnostic for scenes without active pickup effects. Movement
must use checkPositionWithEffects, so failed moves cannot discard pickups. -/
def Scene.checkPosition (scene : Scene) (query : Query) (sector : Heights) : Except String PositionResult := do
  if scene.pickupPlayer.isSome then throw "collision: use the effectful position query for pickups"
  return (← scene.checkPositionWithEffects query sector).2

/-- Build immutable line geometry from decoded WAD data. Dynamic actor links must
be supplied before checking a populated level; this starts with no actors. -/
def Scene.fromMap (map : Map) : Except String Scene := do
  let mut lines := #[]
  for line in map.lines do
    let some a := map.vertices[line.v1]? | throw "collision: bad first vertex"
    let some b := map.vertices[line.v2]? | throw "collision: bad second vertex"
    let heights (side : Nat) : Except String Heights := do
      let some side := map.sides[side]? | throw "collision: bad side"
      let some sector := map.sectors[side.sector]? | throw "collision: bad sector"
      return ⟨Fixed.ofInt sector.floor, Fixed.ofInt sector.ceiling⟩
    let front ← heights line.front
    let back ← if line.back == 65535 then pure none else some <$> heights line.back
    let geometry ← Line.make (Fixed.ofInt a.x) (Fixed.ofInt a.y)
      (Fixed.ofInt b.x) (Fixed.ofInt b.y) front back (line.flags &&& 1 != 0) (line.special != 0)
    lines := lines.push { geometry with twoSided := line.flags &&& 4 != 0, blockMonsters := line.flags &&& 2 != 0 }
  return { grid := map.blockmap, lines, links := Array.replicate map.blockmap.cells.size #[]
           sectors := map.sectors.map fun s => ⟨Fixed.ofInt s.floor, Fixed.ofInt s.ceiling⟩
           sectorLinks := Array.replicate map.sectors.size #[] }

end Doom.Collision
