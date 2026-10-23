import Doom.Proofs.E1M1AimBlockingPrefix
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
namespace Doom.Proofs.E1M1AimLineDispatch
open Collision E1M1AimIteration

/-- A line either stops with its resulting bounds, or continues with a logged portal. -/
inductive Decision where
  | stop (lower upper : Fixed)
  | next (lower upper : Fixed) (entry : AutoAim.Portal)

/-- The source branch order: wall flags, sector opening, then the clipped window.
A missing back sector is not silently treated as a valid represented line. -/
def dispatch (scene : Scene) (hit : Intercept) (distance lower upper floorSlope ceilingSlope : Fixed) :
    Option Decision :=
  let line := scene.lines[hit.id]!
  if !line.twoSided then some (.stop lower upper)
  else match line.back with
    | none => none
    | some back =>
      if min line.front.ceiling.raw back.ceiling.raw ≤ max line.front.floor.raw back.floor.raw then
        some (.stop lower upper)
      else
        let lo := bottomAfter line.front back lower floorSlope
        let hi := topAfter line.front back upper ceilingSlope
        if lo.raw<hi.raw then some (.next lo hi (portal line.front back distance hit))
        else some (.stop lo hi)

theorem wall (scene : Scene) (hit : Intercept) (distance lower upper floorSlope ceilingSlope : Fixed)
    (solid : scene.lines[hit.id]!.twoSided=false) :
    dispatch scene hit distance lower upper floorSlope ceilingSlope=some (.stop lower upper) := by
  simp [dispatch,solid]

theorem closed (scene : Scene) (hit : Intercept) (distance lower upper floorSlope ceilingSlope : Fixed)
    (back : Heights) (two : scene.lines[hit.id]!.twoSided=true)
    (backSector : scene.lines[hit.id]!.back=some back)
    (blocked : min scene.lines[hit.id]!.front.ceiling.raw back.ceiling.raw ≤ max scene.lines[hit.id]!.front.floor.raw back.floor.raw) :
    dispatch scene hit distance lower upper floorSlope ceilingSlope=some (.stop lower upper) := by
  simp [dispatch,two,backSector,blocked]

theorem opened (scene : Scene) (hit : Intercept) (distance lower upper floorSlope ceilingSlope : Fixed)
    (back : Heights) (two : scene.lines[hit.id]!.twoSided=true)
    (backSector : scene.lines[hit.id]!.back=some back)
    (pass : max scene.lines[hit.id]!.front.floor.raw back.floor.raw < min scene.lines[hit.id]!.front.ceiling.raw back.ceiling.raw) :
    dispatch scene hit distance lower upper floorSlope ceilingSlope =
      if (bottomAfter scene.lines[hit.id]!.front back lower floorSlope).raw <
          (topAfter scene.lines[hit.id]!.front back upper ceilingSlope).raw then
        some (.next (bottomAfter scene.lines[hit.id]!.front back lower floorSlope)
          (topAfter scene.lines[hit.id]!.front back upper ceilingSlope)
          (portal scene.lines[hit.id]!.front back distance hit))
      else some (.stop (bottomAfter scene.lines[hit.id]!.front back lower floorSlope)
        (topAfter scene.lines[hit.id]!.front back upper ceilingSlope)) := by
  have gap : ¬min scene.lines[hit.id]!.front.ceiling.raw back.ceiling.raw ≤ max scene.lines[hit.id]!.front.floor.raw back.floor.raw := by
    simp only [Int32.le_iff_toInt_le,Int32.lt_iff_toInt_lt] at pass ⊢; omega
  simp only [dispatch,two,Bool.not_true,Bool.false_eq_true,if_false,backSector,if_neg gap]

end Doom.Proofs.E1M1AimLineDispatch
