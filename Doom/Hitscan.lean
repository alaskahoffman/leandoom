/-
P_AimLineAttack/P_LineAttack and their traversal callbacks, Chocolate Doom 3.1.1
p_map.c, commit 410d96855b5df5410ff591a90efeafa889119224.
Derived from id Software (1993-1996), Simon Howard (2005-2014).
SPDX-License-Identifier: GPL-2.0-or-later. See COPYING.md.
-/
import Doom.Path
import Doom.Angles
import Doom.AutoAim

namespace Doom.Collision

structure AimResult where
  slope : Fixed := ⟨0⟩
  target : Option Nat := none
  path : PathResult
  window : Option AutoAim.Window := none

inductive ShotEvent where
  | special (line : Nat)
  | puff (x y z : Fixed)
  | blood (x y z : Fixed) (damage : Int32)
  | damage (target : Nat) (amount : Int32)
  deriving Repr

structure ShotResult where
  events : Array ShotEvent := #[]
  path : PathResult

private def Scene.attackPath (scene : Scene) (shooter : Nat) (angle : Angle)
    (distance : Fixed) : Except String (SolidThing × PathResult) := do
  if distance.raw ≤ 0 then throw "hitscan: range must be positive"
  let some thing := scene.things[shooter]? | throw "hitscan: invalid shooter"
  -- Original integer-map-unit range multiplication, not FixedMul.
  let x := thing.x + (⟨(distance.raw >>> 16) * angle.fineCosine.raw⟩ : Fixed)
  let y := thing.y + (⟨(distance.raw >>> 16) * angle.fineSine.raw⟩ : Fixed)
  -- P_PathTraverse collects before invoking any callbacks. Sort once here, then
  -- consume that ordered list below, stopping at the original callback boundary.
  return (thing, ← scene.pathTraverse thing.x thing.y x y 3 (fun _ _ => true))

private def shootHeight (t : SolidThing) : Fixed :=
  t.z + (⟨t.height.raw >>> 1⟩ : Fixed) + Fixed.ofInt 8

private def stopped (path : PathResult) (count : Nat) : PathResult :=
  { path with completed := false, visited := path.visited.extract 0 count }

/-- Original vertical autoaim, narrowed by portals, then centered on the first
shootable actor's visible height. Solid decorations are not shooting targets. -/
def Scene.aimLineAttack (scene : Scene) (shooter : Nat) (angle : Angle)
    (distance : Fixed) : Except String AimResult := do
  let (thing,path) ← scene.attackPath shooter angle distance
  let z := shootHeight thing
  let mut top : Fixed := ⟨40960⟩
  let mut bottom : Fixed := ⟨-40960⟩
  let mut portals : Array AutoAim.Portal := #[]
  for i in [:path.visited.size] do
    let hit := path.visited[i]!
    let dist := distance * hit.frac
    if hit.isLine then
      let line := scene.lines[hit.id]!
      if !line.twoSided then return { path := stopped path (i+1) }
      let some back := line.back | throw "hitscan: missing two-sided back sector is unverified"
      let low : Fixed := ⟨max line.front.floor.raw back.floor.raw⟩
      let high : Fixed := ⟨min line.front.ceiling.raw back.ceiling.raw⟩
      if low.raw ≥ high.raw then return { path := stopped path (i+1) }
      portals := portals.push { distance := dist, bottom := low, top := high, line := hit.id }
      if line.front.floor != back.floor then bottom := ⟨max bottom.raw (← checkedPathDiv (low-z) dist).raw⟩
      if line.front.ceiling != back.ceiling then top := ⟨min top.raw (← checkedPathDiv (high-z) dist).raw⟩
      if top.raw ≤ bottom.raw then return { path := stopped path (i+1) }
    else
      let target := scene.things[hit.id]!
      if hit.id == shooter || !target.shootable then continue
      let ttop ← checkedPathDiv (target.z + target.height - z) dist
      if ttop.raw < bottom.raw then continue
      let tbottom ← checkedPathDiv (target.z-z) dist
      if tbottom.raw > top.raw then continue
      let window : AutoAim.Window := { portalBottom := bottom.raw, portalTop := top.raw, targetBottom := tbottom.raw, targetTop := ttop.raw, distance := dist, shootZ := z, target := hit.id, targetZ := target.z, targetHeight := target.height, portals }
      return { slope := AutoAim.center window.bottom window.top, target := some hit.id, path := stopped path (i+1), window := some window }
  return { path }

/-- Original traversal and effect order. Special-line requests precede the opening
check; impact effects precede damage. This read-only kernel records those requests.
A mutating shoot-special dispatcher must run during traversal before supporting
specials that change geometry (not present in E1M1). Sky flags are sided sectors. -/
def Scene.lineAttack (scene : Scene) (shooter : Nat) (angle : Angle)
    (distance slope : Fixed) (damage : Int32)
    (sky : Nat → Bool × Bool := fun _ => (false,false))
    (noBlood : Nat → Bool := fun _ => false) : Except String ShotResult := do
  let (thing,path) ← scene.attackPath shooter angle distance
  let z := shootHeight thing
  let mut events := #[]
  for i in [:path.visited.size] do
    let hit := path.visited[i]!
    let dist := distance * hit.frac
    if hit.isLine then
      let line := scene.lines[hit.id]!
      if line.special then events := events.push (.special hit.id)
      let mut blocked := !line.twoSided
      if !blocked then
        let some back := line.back | throw "hitscan: missing two-sided back sector is unverified"
        if line.front.floor != back.floor then
          let low : Fixed := ⟨max line.front.floor.raw back.floor.raw⟩
          if (← checkedPathDiv (low-z) dist).raw > slope.raw then blocked := true
        if !blocked && line.front.ceiling != back.ceiling then
          let high : Fixed := ⟨min line.front.ceiling.raw back.ceiling.raw⟩
          if (← checkedPathDiv (high-z) dist).raw < slope.raw then blocked := true
      if !blocked then continue
      let frac := hit.frac - (← checkedPathDiv (Fixed.ofInt 4) distance)
      let x := path.trace.x + path.trace.dx * frac
      let y := path.trace.y + path.trace.dy * frac
      let impactZ := z + slope * (frac * distance)
      let (frontSky,backSky) := sky hit.id
      if !(frontSky && (impactZ.raw > line.front.ceiling.raw || (line.back.isSome && backSky))) then
        events := events.push (.puff x y impactZ)
      return ⟨events,stopped path (i+1)⟩
    else
      let target := scene.things[hit.id]!
      if hit.id == shooter || !target.shootable then continue
      if (← checkedPathDiv (target.z + target.height - z) dist).raw < slope.raw then continue
      if (← checkedPathDiv (target.z-z) dist).raw > slope.raw then continue
      let frac := hit.frac - (← checkedPathDiv (Fixed.ofInt 10) distance)
      let x := path.trace.x + path.trace.dx * frac
      let y := path.trace.y + path.trace.dy * frac
      let impactZ := z + slope * (frac * distance)
      events := events.push (if noBlood hit.id then .puff x y impactZ else .blood x y impactZ damage)
      if damage != 0 then events := events.push (.damage hit.id damage)
      return ⟨events,stopped path (i+1)⟩
  return ⟨events,path⟩

/-- P_BulletSlope: center, then +1/64 turn, then -1/64 turn at 1024 units.
This chooses vertical slope only; the fired horizontal angle is not redirected. -/
def Scene.bulletAim (scene : Scene) (shooter : Nat) (angle : Angle) : Except String AutoAim.Selection := do
  for offset in #[0,0x04000000,0xfc000000] do
    let result ← scene.aimLineAttack shooter ⟨angle.raw + offset⟩ (Fixed.ofInt 1024)
    if result.target.isSome then
      return { slope := result.slope, facing := angle, offset, window := result.window }
  return { facing := angle }

/-- Compatibility projection; selection and traversal ordering are unchanged. -/
def Scene.bulletSlope (scene : Scene) (shooter : Nat) (angle : Angle) : Except String Fixed := do
  return (← scene.bulletAim shooter angle).slope

end Doom.Collision
