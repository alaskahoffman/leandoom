import Doom.Proofs.OriginalAimGuard
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1AimSource
open Collision
def attackPath (scene : Scene) (shooter : Nat) (angle : Angle)
    (distance : Fixed) : Except String (SolidThing × PathResult) := do
  if distance.raw ≤ 0 then throw "hitscan: range must be positive"
  let some thing := scene.things[shooter]? | throw "hitscan: invalid shooter"
  -- Original integer-map-unit range multiplication, not FixedMul.
  let (x,y) := thing.attackEndpoint angle distance
  -- P_PathTraverse collects before invoking any callbacks. Sort once here, then
  -- consume that ordered list below, stopping at the original callback boundary.
  return (thing, ← scene.pathTraverse thing.x thing.y x y 3 (fun _ _ => true))

def stopped (path : PathResult) (count : Nat) : PathResult :=
  { path with completed := false, visited := path.visited.extract 0 count }

/-- Exact live post-traversal loop; only its private path helper is exposed. -/
def afterPath (scene : Scene) (shooter : Nat) (thing : SolidThing)
    (path : PathResult) (distance : Fixed) : Except String AimResult := do
  let z := thing.shootHeight
  let mut top := aimTopSlope
  let mut bottom := aimBottomSlope
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

/-- This extraction is definitionally the production aiming function. -/
theorem live (scene : Scene) (shooter : Nat) (angle : Angle) (distance : Fixed) :
    scene.aimLineAttack shooter angle distance=(do
      let (thing,path) ← attackPath scene shooter angle distance
      afterPath scene shooter thing path distance) := by
  rfl

/-- With a one-sided first wall, the live loop stops at that hit. It does not
inspect later hits or produce a target, slope, or clipped window. -/
theorem first_wall (scene : Scene) (shooter : Nat) (thing : SolidThing)
    (path : PathResult) (distance : Fixed) (hit : Intercept)
    (nonempty : 0<path.visited.size) (first : path.visited[0]! = hit)
    (isLine : hit.isLine=true) (solid : scene.lines[hit.id]!.twoSided=false) :
    afterPath scene shooter thing path distance=.ok {path:=stopped path 1} := by
  have first' : path.visited[0]=hit := by simpa only [getElem!_pos path.visited 0 nonempty] using first
  obtain ⟨n,size⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : path.visited.size≠0)
  simp [afterPath,Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,size,
    List.range'_succ,List.forIn_cons,first',isLine,solid]
  rfl
/-- The same early-stop result for the production function, conditional on its
actual ordered path having this first wall. -/
theorem blocked_query (scene : Scene) (shooter : Nat) (angle : Angle) (distance : Fixed)
    (thing : SolidThing) (path : PathResult) (hit : Intercept)
    (traced : attackPath scene shooter angle distance=.ok (thing,path))
    (nonempty : 0<path.visited.size) (first : path.visited[0]! = hit)
    (isLine : hit.isLine=true) (solid : scene.lines[hit.id]!.twoSided=false) :
    scene.aimLineAttack shooter angle distance=.ok {path:=stopped path 1} := by
  rw [live,traced]
  exact first_wall scene shooter thing path distance hit nonempty first isLine solid
end Doom.Proofs.E1M1AimSource
