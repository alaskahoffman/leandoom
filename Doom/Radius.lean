/-
P_RadiusAttack/PIT_RadiusAttack, pinned Chocolate Doom 3.1.1 p_map.c.
Derived from id Software (1993-1996), Simon Howard (2005-2014).
SPDX-License-Identifier: GPL-2.0-or-later. See COPYING.md.
-/
import Doom.Sight

namespace Doom.Collision

/-- Damage falloff is Chebyshev distance minus target radius, shifted down to
whole units. No vertical-distance falloff; sight is a separate gate. -/
def radiusDamage (spot target : SolidThing) (damage : Int32) (kind : Nat)
    : Except String Int32 := do
  if !target.shootable || kind == 7 || kind == 16 then return 0
  let dx ← checkedPathAbs (target.x-spot.x)
  let dy ← checkedPathAbs (target.y-spot.y)
  let distance := max (0 : Int32) ((max dx.raw dy.raw - target.radius.raw) >>> 16)
  return if distance ≥ damage then 0 else damage-distance

/-- Original y-major block order and current bnext order. This emits ordered
damage requests. The current damage adapter does not move actors or cause
immediate nested radius attacks: barrel chains enter delayed explosion states. -/
def Scene.radiusAttack (scene : Scene) (spot : SolidThing) (damage : Int32)
    (kind : Nat → Nat) (sight : SolidThing → SolidThing → Except String Bool)
    : Except String (Array (Nat × Int32)) := do
  -- MAXRADIUS is already fixed point in p_local.h. Its contribution wraps
  -- away in this original expression; adding 32 map units would change visits.
  let distance : Fixed := ⟨(damage+2097152) <<< 16⟩
  let ox := Fixed.ofInt scene.grid.origin.x; let oy := Fixed.ofInt scene.grid.origin.y
  let xl := blockCoordinate (spot.x-distance) ox
  let xh := blockCoordinate (spot.x+distance) ox
  let yl := blockCoordinate (spot.y-distance) oy
  let yh := blockCoordinate (spot.y+distance) oy
  let mut hits := #[]
  for y in [(max 0 yl).toNat:(max 0 (min (Int.ofNat scene.grid.height) (yh+1))).toNat] do
    for x in [(max 0 xl).toNat:(max 0 (min (Int.ofNat scene.grid.width) (xh+1))).toNat] do
      let some ids := scene.links[y*scene.grid.width+x]? | throw "radius: invalid block links"
      for id in ids do
        let some target := scene.things[id]? | throw "radius: invalid actor link"
        let amount ← radiusDamage spot target damage (kind id)
        if amount > 0 then
          if (← sight target spot) then hits := hits.push (id,amount)
  return hits

end Doom.Collision
