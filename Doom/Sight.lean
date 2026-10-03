/-
DOOM 1.9 BSP sight traversal, pinned Chocolate Doom 3.1.1 p_sight.c.
Derived from id Software (1993-1996), Simon Howard (2005-2014).
SPDX-License-Identifier: GPL-2.0-or-later. See COPYING.md.
-/
import Doom.Path

namespace Doom.Sight
open Collision

/-- P_DivlineSide has a distinct three-way result, coarse products, and the
historical horizontal x==node.y test. Do not replace it with movement's helper. -/
def side (line : Divline) (x y : Fixed) : Nat :=
  if line.dx.raw == 0 then
    if x == line.x then 2 else if x.raw ≤ line.x.raw then
      if line.dy.raw > 0 then 1 else 0
    else if line.dy.raw < 0 then 1 else 0
  else if line.dy.raw == 0 then
    if x == line.y then 2 else if y.raw ≤ line.y.raw then
      if line.dx.raw < 0 then 1 else 0
    else if line.dx.raw > 0 then 1 else 0
  else
    let left := (line.dy.raw >>> 16) * ((x-line.x).raw >>> 16)
    let right := ((y-line.y).raw >>> 16) * (line.dx.raw >>> 16)
    if right < left then 0 else if left == right then 2 else 1

/-- P_CheckSight/P_CrossBSPNode/P_CrossSubsector, ordinary 1.9 maps. Actor
occlusion is intentionally absent. Missing REJECT bytes and invalid geometry
are rejected; DOS memory-overrun emulation is outside this profile. -/
def check (map : Map) (looker target : SolidThing) : Except String Bool := do
  let pair := looker.sector * map.sectors.size + target.sector
  let some reject := map.reject[pair/8]? | throw "sight: short REJECT table"
  if reject.toNat &&& (1 <<< (pair%8)) != 0 then return false
  let eye := looker.z + looker.height - (⟨looker.height.raw >>> 2⟩ : Fixed)
  let mut top := target.z + target.height - eye
  let mut bottom := target.z-eye
  let trace : Divline := ⟨looker.x,looker.y,target.x-looker.x,target.y-looker.y⟩
  let mut stack := [if map.nodes.isEmpty then Child.subsector 0 else .node (map.nodes.size-1)]
  let mut seen := Array.replicate map.lines.size false
  -- Validated trees need at most this many visits; reject cycles/shared DAGs
  -- whose expansion exceeds the supported tree domain.
  for _ in [:2*map.nodes.size+map.subsectors.size+1] do
    let child::rest := stack | return true
    stack := rest
    match child with
    | .node id =>
      let some node := map.nodes[id]? | throw "sight: invalid BSP node"
      let div : Divline := ⟨Fixed.ofInt node.origin.x, Fixed.ofInt node.origin.y,
        Fixed.ofInt node.delta.x, Fixed.ofInt node.delta.y⟩
      let start := side div looker.x looker.y
      let start := if start == 2 then 0 else start
      let first := if start == 0 then node.right else node.left
      let second := if start == 0 then node.left else node.right
      stack := if start == side div target.x target.y then first::stack else first::second::stack
    | .subsector id =>
      let some sub := map.subsectors[id]? | throw "sight: invalid subsector"
      for index in [sub.first:sub.first+sub.count] do
        let some seg := map.segs[index]? | throw "sight: invalid seg"
        let some line := map.lines[seg.linedef]? | throw "sight: invalid line"
        if seen[seg.linedef]! then continue
        seen := seen.set! seg.linedef true
        let a := map.vertices[line.v1]!
        let b := map.vertices[line.v2]!
        let ax := Fixed.ofInt a.x; let ay := Fixed.ofInt a.y
        let bx := Fixed.ofInt b.x; let byCoord := Fixed.ofInt b.y
        if side trace ax ay == side trace bx byCoord then continue
        let div : Divline := ⟨ax,ay,bx-ax,byCoord-ay⟩
        if side div looker.x looker.y == side div target.x target.y then continue
        if line.flags &&& 4 == 0 || line.back ≥ map.sides.size then return false
        let front := map.sectors[map.sides[line.front]!.sector]!
        let back := map.sectors[map.sides[line.back]!.sector]!
        if front.floor == back.floor && front.ceiling == back.ceiling then continue
        let openTop := Fixed.ofInt (min front.ceiling back.ceiling)
        let openBottom := Fixed.ofInt (max front.floor back.floor)
        if openBottom.raw ≥ openTop.raw then return false
        let frac ← interceptVector trace div
        if front.floor != back.floor then
          let slope ← checkedPathDiv (openBottom-eye) frac
          if slope.raw > bottom.raw then bottom := slope
        if front.ceiling != back.ceiling then
          let slope ← checkedPathDiv (openTop-eye) frac
          if slope.raw < top.raw then top := slope
        if top.raw ≤ bottom.raw then return false
  throw "sight: BSP traversal exceeded tree budget"

end Doom.Sight
