import Doom.Proofs.E1M1AimActorBoundary
set_option backward.isDefEq.respectTransparency false
namespace Doom.Proofs.E1M1AimActorDispatch
open Collision

inductive Decision where
  | ignored
  | below
  | above
  | selected
  deriving DecidableEq, Repr

/-- Preserve source short-circuit order: identity/flags, top, then bottom.
Slope values are irrelevant until their corresponding branch is reached. -/
def dispatch (scene : Scene) (shooter : Nat) (hit : Intercept)
    (lower upper topSlope bottomSlope : Fixed) : Decision :=
  if hit.id=shooter ∨ scene.things[hit.id]!.shootable=false then .ignored
  else if topSlope.raw<lower.raw then .below
  else if upper.raw<bottomSlope.raw then .above
  else .selected

theorem ignored (scene : Scene) (shooter : Nat) (hit : Intercept)
    (lower upper topSlope bottomSlope : Fixed)
    (skip : hit.id=shooter ∨ scene.things[hit.id]!.shootable=false) :
    dispatch scene shooter hit lower upper topSlope bottomSlope=.ignored := by
  simp [dispatch,skip]

theorem eligible (scene : Scene) (shooter : Nat) (hit : Intercept)
    (lower upper topSlope bottomSlope : Fixed)
    (different : hit.id≠shooter) (shootable : scene.things[hit.id]!.shootable=true) :
    dispatch scene shooter hit lower upper topSlope bottomSlope=
      if topSlope.raw<lower.raw then .below
      else if upper.raw<bottomSlope.raw then .above else .selected := by
  simp [dispatch,different,shootable]

/-- Both equalities are admitted, matching the two strict original rejections. -/
theorem equality (scene : Scene) (shooter : Nat) (hit : Intercept) (lower upper : Fixed)
    (different : hit.id≠shooter) (shootable : scene.things[hit.id]!.shootable=true) :
    dispatch scene shooter hit lower upper lower upper=.selected := by
  rw [eligible scene shooter hit lower upper lower upper different shootable]
  simp only [Int32.lt_iff_toInt_lt,Int.lt_irrefl,ite_false]
end Doom.Proofs.E1M1AimActorDispatch
