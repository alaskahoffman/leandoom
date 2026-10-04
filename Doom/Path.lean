/-
P_PathTraverse and intercept helpers, Chocolate Doom 3.1.1,
commit 410d96855b5df5410ff591a90efeafa889119224.
Derived from id Software (1993-1996), Simon Howard (2005-2014).
SPDX-License-Identifier: GPL-2.0-or-later. See COPYING.md.
-/
import Doom.Collision

namespace Doom.Collision

structure Divline where
  x : Fixed
  y : Fixed
  dx : Fixed
  dy : Fixed
  deriving Repr

def Divline.pointSide (line : Divline) (x y : Fixed) : Bool :=
  if line.dx.raw == 0 then
    if x.raw ≤ line.x.raw then line.dy.raw > 0 else line.dy.raw < 0
  else if line.dy.raw == 0 then
    if y.raw ≤ line.y.raw then line.dx.raw < 0 else line.dx.raw > 0
  else
    let dx := x - line.x
    let dy := y - line.y
    if (line.dy.raw ^^^ line.dx.raw ^^^ dx.raw ^^^ dy.raw) < 0 then
      (line.dy.raw ^^^ dx.raw) < 0
    else
      let left := (⟨line.dy.raw >>> 8⟩ : Fixed) * ⟨dx.raw >>> 8⟩
      let right := (⟨dy.raw >>> 8⟩ : Fixed) * ⟨line.dx.raw >>> 8⟩
      right.raw ≥ left.raw

def checkedPathDiv (a b : Fixed) : Except String Fixed :=
  (Fixed.divChecked a b).mapError fun e => s!"path: original DOS division fault ({repr e})"

def checkedPathAbs (a : Fixed) : Except String Fixed :=
  if a.raw == -2147483648 then .error "path: unverified abs(INT_MIN)"
  else .ok ⟨Int32.ofInt a.raw.toInt.natAbs⟩

/-- Fraction along v2; the original C parameter order is intentionally retained. -/
def interceptVector (v2 v1 : Divline) : Except String Fixed := do
  let den := (⟨v1.dy.raw >>> 8⟩ : Fixed) * v2.dx - (⟨v1.dx.raw >>> 8⟩ : Fixed) * v2.dy
  if den.raw == 0 then return ⟨0⟩
  let num := (⟨(v1.x - v2.x).raw >>> 8⟩ : Fixed) * v1.dy +
    (⟨(v2.y - v1.y).raw >>> 8⟩ : Fixed) * v1.dx
  checkedPathDiv num den

structure Intercept where
  frac : Fixed
  isLine : Bool
  id : Nat
  deriving Repr, Inhabited

structure PathResult where
  completed : Bool := true
  trace : Divline
  blocks : Array (Bool × Int32 × Int32) := #[]
  collected : Array Intercept := #[]
  visited : Array Intercept := #[]
  deriving Repr

private def lineIntercept (trace : Divline) (line : Line) : Except String (Option Fixed) := do
  let (s1, s2) := if trace.dx.raw > 1048576 || trace.dy.raw > 1048576 ||
      trace.dx.raw < -1048576 || trace.dy.raw < -1048576 then
    (trace.pointSide line.x line.y, trace.pointSide (line.x + line.dx) (line.y + line.dy))
  else (line.pointSide trace.x trace.y, line.pointSide (trace.x + trace.dx) (trace.y + trace.dy))
  if s1 == s2 then return none
  let frac ← interceptVector trace ⟨line.x, line.y, line.dx, line.dy⟩
  return if frac.raw < 0 then none else some frac

private def thingIntercept (trace : Divline) (thing : SolidThing) : Except String (Option Fixed) := do
  let positive := (trace.dx.raw ^^^ trace.dy.raw) > 0
  let x1 := thing.x - thing.radius
  let x2 := thing.x + thing.radius
  let y1 := if positive then thing.y + thing.radius else thing.y - thing.radius
  let y2 := if positive then thing.y - thing.radius else thing.y + thing.radius
  if trace.pointSide x1 y1 == trace.pointSide x2 y2 then return none
  let frac ← interceptVector trace ⟨x1, y1, x2-x1, y2-y1⟩
  return if frac.raw < 0 then none else some frac

private def appendIntercept (r : PathResult) (hit : Intercept) : Except String PathResult :=
  if r.collected.size ≥ 128 then .error "path: intercept overflow profile is unverified"
  else .ok { r with collected := r.collected.push hit }

/-- P_PathTraverse: original one-unit boundary nudge, line-before-thing cell
visits, 64-iteration limit (including stalled cells), and first-inserted tie order.
flags: 1 lines, 2 things, 4 early-out. The visitor is read-only and returns true
to continue. Reject unverified arithmetic and intercept-overflow domains. -/
def Scene.pathTraverse (scene : Scene) (startX startY endX endY : Fixed)
    (flags : Nat) (visit : Intercept → Nat → Bool) : Except String PathResult := do
  let grid := scene.grid
  if !grid.vanillaOffsets || grid.width == 0 || grid.height == 0 ||
      grid.width ≥ 32768 || grid.height ≥ 32768 ||
      grid.cells.size != grid.width * grid.height || scene.links.size != grid.cells.size then
    throw "path: unsupported BLOCKMAP profile"
  let ox := Fixed.ofInt grid.origin.x
  let oy := Fixed.ofInt grid.origin.y
  let x1 := if (startX - ox).raw &&& 8388607 == 0 then startX + Fixed.ofInt 1 else startX
  let y1 := if (startY - oy).raw &&& 8388607 == 0 then startY + Fixed.ofInt 1 else startY
  let trace : Divline := ⟨x1, y1, endX-x1, endY-y1⟩
  let mut result : PathResult := { trace }
  let x1 := x1 - ox; let y1 := y1 - oy
  let x2 := endX - ox; let y2 := endY - oy
  let xt1 := x1.raw >>> 23; let yt1 := y1.raw >>> 23
  let xt2 := x2.raw >>> 23; let yt2 := y2.raw >>> 23
  let (mapxstep, portion, ystep) ← if xt2 == xt1 then
      pure ((0 : Int32), Fixed.ofInt 1, Fixed.ofInt 256)
    else do
      let fraction : Fixed := ⟨(x1.raw >>> 7) &&& 65535⟩
      let portion := if xt2 > xt1 then Fixed.ofInt 1 - fraction else fraction
      let step ← checkedPathDiv (y2-y1) (← checkedPathAbs (x2-x1))
      pure (if xt2 > xt1 then 1 else -1, portion, step)
  let mut yi := (⟨y1.raw >>> 7⟩ : Fixed) + portion * ystep
  let (mapystep, portion, xstep) ← if yt2 == yt1 then
      pure ((0 : Int32), Fixed.ofInt 1, Fixed.ofInt 256)
    else do
      let fraction : Fixed := ⟨(y1.raw >>> 7) &&& 65535⟩
      let portion := if yt2 > yt1 then Fixed.ofInt 1 - fraction else fraction
      let step ← checkedPathDiv (x2-x1) (← checkedPathAbs (y2-y1))
      pure (if yt2 > yt1 then 1 else -1, portion, step)
  let mut xi := (⟨x1.raw >>> 7⟩ : Fixed) + portion * xstep
  let mut mapx := xt1; let mut mapy := yt1
  let mut seen := Array.replicate scene.lines.size false
  for _ in [:64] do
    let inside := mapx.toInt ≥ 0 && mapy.toInt ≥ 0 &&
      mapx.toInt < grid.width && mapy.toInt < grid.height
    let cell := mapy.toInt.toNat * grid.width + mapx.toInt.toNat
    if flags &&& 1 != 0 then
      result := { result with blocks := result.blocks.push (true, mapx, mapy) }
      if inside then
        let some ids := grid.cells[cell]? | throw "path: missing line cell"
        for id in #[0] ++ ids do
          if id ≥ 32768 then throw "path: signed linedef index is unverified"
          let some line := scene.lines[id]? | throw "path: invalid linedef"
          if seen[id]! then continue
          seen := seen.set! id true
          if let some frac ← lineIntercept trace line then
            if flags &&& 4 != 0 && frac.raw < 65536 && line.back.isNone then
              return { result with completed := false }
            result ← appendIntercept result ⟨frac, true, id⟩
    if flags &&& 2 != 0 then
      result := { result with blocks := result.blocks.push (false, mapx, mapy) }
      if inside then
        let some ids := scene.links[cell]? | throw "path: missing thing cell"
        for id in ids do
          let some thing := scene.things[id]? | throw "path: invalid actor link"
          if let some frac ← thingIntercept trace thing then
            result ← appendIntercept result ⟨frac, false, id⟩
    if mapx == xt2 && mapy == yt2 then break
    if yi.raw >>> 16 == mapy then
      yi := yi + ystep; mapx := mapx + mapxstep
    else if xi.raw >>> 16 == mapx then
      xi := xi + xstep; mapy := mapy + mapystep
  -- Use the original strict-min selection rather than a sort with unspecified ties.
  let mut work := result.collected
  for _ in [:work.size] do
    let mut distance : Int32 := 2147483647
    let mut chosen := none
    for i in [:work.size] do
      if work[i]!.frac.raw < distance then
        distance := work[i]!.frac.raw; chosen := some i
    if distance > 65536 then break
    let some i := chosen | throw "path: missing finite intercept"
    let hit := work[i]!
    result := { result with visited := result.visited.push hit }
    if !visit hit (result.visited.size - 1) then return { result with completed := false }
    work := work.set! i { hit with frac := ⟨2147483647⟩ }
  return result

end Doom.Collision
