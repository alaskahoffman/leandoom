/- Imp fireball branches of p_mobj.c, pinned Chocolate Doom 3.1.1.
Derived from id Software / Simon Howard. SPDX-License-Identifier: GPL-2.0-or-later. -/
import Doom.ImpData
import Doom.Slide
import Doom.Angles
import Doom.Motion

namespace Doom.Projectile
open Collision ImpData

inductive Event where
  | spawn (source target : Nat)
  | hit (target damage : Nat)
  | sound (name : String)
  | remove
  deriving Repr

structure Body where
  source : Nat
  motion : Motion
  frame : Nat := TBALL1
  tics : Int32 := 4
  exploding : Bool := false
  removed : Bool := false
  deriving Inhabited

/-- P_SpawnMobj lastlook draw, P_SpawnMissile, then P_CheckMissileSpawn's
duration draw and half-step. Collision at the resulting point runs immediately. -/
def spawn (source : Nat) (own dest : SolidThing) (shadow : Bool) (rng : DoomRandom)
    : Except String (Body × DoomRandom) := do
  let (_,rng) := rng.nextPlay
  let mut rng := rng
  let mut angle := Angle.fromVector (dest.x-own.x) (dest.y-own.y)
  if shadow then
    let (spread,next) := rng.subPlay
    rng := next
    angle := ⟨angle.raw + (Int32.ofInt spread <<< 20).toUInt32⟩
  let speed := Fixed.ofInt 10
  let dx := speed * angle.fineCosine; let dy := speed * angle.fineSine
  let distance ← approximateDistance (dest.x-own.x) (dest.y-own.y)
  let count := max 1 (distance.raw.toInt.tdiv speed.raw.toInt)
  let dz : Fixed := ⟨Int32.ofInt ((dest.z-own.z).raw.toInt.tdiv count)⟩
  let (roll,nextRng) := rng.nextPlay
  let motion : Motion := {
    x := own.x + (⟨dx.raw >>> 1⟩ : Fixed), y := own.y + (⟨dy.raw >>> 1⟩ : Fixed),
    z := own.z + Fixed.ofInt 32 + (⟨dz.raw >>> 1⟩ : Fixed),
    momx := dx, momy := dy, momz := dz, angle,
    floorz := own.floor, ceilingz := own.ceiling, height := Fixed.ofInt 8, noGravity := true }
  return ({ source, motion, tics := max 1 (4-Int32.ofNat (roll &&& 3)) },nextRng)

def explode (p : Body) (rng : DoomRandom) : Body × DoomRandom :=
  let (roll,rng) := rng.nextPlay
  ({ p with
    exploding := true, frame := TBALLX1, tics := max 1 (6-Int32.ofNat (roll &&& 3)),
    motion := { p.motion with momx := ⟨0⟩, momy := ⟨0⟩, momz := ⟨0⟩ } },rng)

def tickState (p : Body) : Except String Body := do
  if p.removed then return p
  let mut p := { p with tics := p.tics-1 }
  if p.tics == 0 then
    let some frame := frames.find? (·.id == p.frame) | throw "projectile: missing frame"
    if frame.next == 0 then return { p with removed := true }
    let some next := frames.find? (·.id == frame.next) | throw "projectile: missing next frame"
    p := { p with frame := next.id, tics := next.tics }
  return p

def position (scene : Scene) (map : Map) (p : Body) (x y : Fixed) : Except String (PositionResult × Bool) := do
  let sector ← map.sectorAt x y
  let kinds := #[0] ++ map.things.map (·.kind)
  let (_,result) ← scene.checkPositionWithEffects {
    x, y, radius := Fixed.ofInt 6, player := false,
    missile := some {
      z := p.motion.z, height := Fixed.ofInt 8, source := some p.source,
      sourceKind := kinds[p.source]!, kinds } } scene.sectors[sector]!
  let thing : SolidThing := {
    x, y, z := p.motion.z, radius := Fixed.ofInt 6,
    height := Fixed.ofInt 8, moveFlags := {dropoff := true} }
  return (result,(moveDecision thing result).accepted)

end Doom.Projectile
