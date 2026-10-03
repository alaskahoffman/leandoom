/-
Arithmetic/BSP/RNG ports refer to Chocolate Doom 3.1.1, commit
410d96855b5df5410ff591a90efeafa889119224.
Derived from id Software (1993-1996) and Simon Howard (2005-2014).
SPDX-License-Identifier: GPL-2.0-or-later
See COPYING.md and tests/reference/manifest.json.
-/
import Doom.Map
import Doom.Fixed

namespace Doom

/-- R_PointOnSide: signed 32-bit differences, sign shortcut, then rounded products.
The rounded equality case belongs to side 1 even when an exact cross product
would put the point on side 0. All arguments here are raw 16.16 coordinates. -/
def pointOnSide (x y originX originY deltaX deltaY : Fixed) : Bool :=
  if deltaX.raw == 0 then
    if x.raw ≤ originX.raw then deltaY.raw > 0 else deltaY.raw < 0
  else if deltaY.raw == 0 then
    if y.raw ≤ originY.raw then deltaX.raw < 0 else deltaX.raw > 0
  else
    let dx := x - originX
    let dy := y - originY
    if (deltaY.raw ^^^ deltaX.raw ^^^ dx.raw ^^^ dy.raw) < 0 then
      (deltaY.raw ^^^ dx.raw) < 0
    else
      let left := Fixed.mul ⟨deltaY.raw >>> 16⟩ dx
      let right := Fixed.mul dy ⟨deltaX.raw >>> 16⟩
      right.raw ≥ left.raw

/-- Right child is side 0; map node fields are signed integer map units. -/
def Node.onLeft (node : Node) (x y : Fixed) : Bool :=
  pointOnSide x y (Fixed.ofInt node.origin.x) (Fixed.ofInt node.origin.y)
    (Fixed.ofInt node.delta.x) (Fixed.ofInt node.delta.y)

def Map.subsectorAt (m : Map) (x y : Fixed) : Except String Nat := do
  let mut child := if m.nodes.isEmpty then Child.subsector 0 else .node (m.nodes.size - 1)
  for _ in [:m.nodes.size + 1] do
    match child with
    | .subsector i =>
      if i < m.subsectors.size then return i
      throw "BSP: invalid subsector"
    | .node i =>
      let some n := m.nodes[i]? | throw "BSP: invalid node"
      child := if n.onLeft x y then n.left else n.right
  throw "BSP: point query exceeded traversal budget"

def Map.sectorAt (m : Map) (x y : Fixed) : Except String Nat := do
  let index ← m.subsectorAt x y
  let some sub := m.subsectors[index]? | throw "BSP: invalid subsector"
  let some seg := m.segs[sub.first]? | throw "BSP: empty subsector"
  let some line := m.lines[seg.linedef]? | throw "BSP: invalid linedef"
  let some side := m.sides[if seg.side == 0 then line.front else line.back]?
    | throw "BSP: absent sidedef"
  return side.sector

/-- Bounded, iterative traversal. Shared children are visited once. -/
def Map.frontToBack (m : Map) (x y : Fixed) : Array Nat := Id.run do
  let mut stack := [if m.nodes.isEmpty then Child.subsector 0 else .node (m.nodes.size - 1)]
  let mut seenNodes := Array.replicate m.nodes.size false
  let mut seenSubs := Array.replicate m.subsectors.size false
  let mut result := #[]
  for _ in [:m.nodes.size * 2 + 1] do
    match stack with
    | [] => break
    | child :: rest =>
      stack := rest
      match child with
      | .subsector i =>
        if i < seenSubs.size && !seenSubs[i]! then
          seenSubs := seenSubs.set! i true
          result := result.push i
      | .node i =>
        if i < seenNodes.size && !seenNodes[i]! then
          seenNodes := seenNodes.set! i true
          let n := m.nodes[i]!
          stack := if n.onLeft x y then n.left :: n.right :: stack else n.right :: n.left :: stack
  return result

end Doom
