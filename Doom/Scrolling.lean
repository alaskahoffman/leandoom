/-
Special 48 list setup and updates from Chocolate Doom 3.1.1 p_spec.c,
commit 410d96855b5df5410ff591a90efeafa889119224.
Derived from id Software (1993-1996), Simon Howard (2005-2014).
SPDX-License-Identifier: GPL-2.0-or-later. See COPYING.md.
-/
import Doom.Map
import Doom.Fixed

namespace Doom.Scrolling

/-- P_SpawnSpecials retains a fixed list in linedef order, with 64 entries max. -/
def spawn (specials : Array Nat) : Except String (Array Nat) := do
  let mut lines := #[]
  for i in [:specials.size] do
    if specials[i]! == 48 then
      if lines.size ≥ 64 then throw "scrolling: more than 64 scrolling wall linedefs"
      lines := lines.push i
  return lines

/-- P_UpdateSpecials rechecks each saved linedef's current special. Shared front
sides receive one wrapping FRACUNIT increment per matching line, in list order. -/
def tick (lines specials fronts : Array Nat) (offsets : Array Fixed) : Except String (Array Fixed) := do
  let mut offsets := offsets
  for i in lines do
    let some special := specials[i]? | throw "scrolling: invalid linedef"
    if special != 48 then continue
    let some front := fronts[i]? | throw "scrolling: missing front sidedef"
    let some offset := offsets[front]? | throw "scrolling: invalid front sidedef"
    offsets := offsets.set! front (offset + Fixed.ofInt 1)
  return offsets

/-- WAD offsets start at whole units, and this action only adds whole units.
The raw fixed-point kernel also supports fractional offsets for differential tests. -/
def tickMap (map : Map) (lines : Array Nat) : Except String Map := do
  let offsets ← tick lines (map.lines.map (·.special)) (map.lines.map (·.front))
    (map.sides.map (fun side => Fixed.ofInt side.xOffset))
  let sides := map.sides.mapIdx fun i side => { side with xOffset := offsets[i]!.raw.toInt / 65536 }
  return { map with sides }

end Doom.Scrolling
