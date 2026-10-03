/-
Player movement sequence derived from Chocolate Doom 3.1.1 p_user.c/p_mobj.c,
commit 410d96855b5df5410ff591a90efeafa889119224.
SPDX-License-Identifier: GPL-2.0-or-later. See COPYING.md.
-/
import Doom.PlayerPhysics
import Doom.Slide

namespace Doom.Collision

/-- Collision owns position, momentum and current space; Motion supplies the
player's angle, animation ordinal and vertical/cheat flags. -/
def SolidThing.motion (t : SolidThing) (extra : Motion) : Motion :=
  { extra with
    x := t.x, y := t.y, z := t.z, momx := t.momx, momy := t.momy,
    floorz := t.floor, ceilingz := t.ceiling, height := t.height }

def SolidThing.withMotion (t : SolidThing) (b : Motion) : SolidThing :=
  { t with
    x := b.x, y := b.y, z := b.z, momx := b.momx, momy := b.momy,
    floor := b.floorz, ceiling := b.ceilingz, height := b.height }

structure WorldPhysicsResult where
  scene : Scene
  body : Motion
  view : ViewState := {}
  attempts : Array SlideAttempt := #[]
  slides : Array SlideResult := #[]
  crossings : Array Crossing := #[]
  landing : Bool := false
  frictionSample : Option FrictionSample := none

/-- Live player P_XYMovement with real P_TryMove and P_SlideMove. The saved
split remainder survives a slide, even when the slide changes momentum.
Uses the same supported actor/callback domain as Scene.tryMove. -/
def Scene.advancePlayerXY (scene : Scene) (id : Nat) (extra : Motion) (cmd : Ticcmd)
    (sectorAt : SectorAt) (cross : Scene → Crossing → Except String Scene)
    : Except String WorldPhysicsResult := do
  let some t := scene.things[id]? | throw "physics: missing player"
  let body := t.motion extra
  let steps := body.xySteps
  if steps.isEmpty then return { scene, body }
  let body := { body with momx := clampMomentum body.momx, momy := clampMomentum body.momy }
  let scene := { scene with things := scene.things.set! id (t.withMotion body) }
  let mut result : WorldPhysicsResult := { scene, body }
  for (dx, dy) in steps do
    let some t := result.scene.things[id]? | throw "physics: callback removed player"
    let x := t.x + dx; let y := t.y + dy
    let moved ← result.scene.tryMove id x y sectorAt cross
    result := { result with
      scene := moved.scene,
      attempts := result.attempts.push ⟨x, y, moved.decision.accepted, moved.decision.floatOK⟩,
      crossings := result.crossings ++ moved.crossings }
    if !moved.decision.accepted then
      let slide ← result.scene.slideMove id sectorAt cross
      result := { result with
        scene := slide.scene,
        attempts := result.attempts ++ slide.attempts, slides := result.slides.push slide,
        crossings := result.crossings ++ slide.crossings }
  let some t := result.scene.things[id]? | throw "physics: callback removed player"
  let before := t.motion result.body
  let body := before.friction cmd
  return { result with
    body, frictionSample := some ⟨before, body, cmd⟩,
    scene := { result.scene with things := result.scene.things.set! id (t.withMotion body) } }

/-- Movement part of a live player's tic: command thrust/turn, view calculation,
XY collision/sliding/friction (including pickup effects), then conditional Z
movement. Sector actions, reaction time, weapons and animation ticking remain
separate ports. -/
def Scene.playerPhysics (scene : Scene) (id : Nat) (extra : Motion) (view : ViewState)
    (cmd : Ticcmd) (levelTime : Int32) (sectorAt : SectorAt)
    (cross : Scene → Crossing → Except String Scene) : Except String WorldPhysicsResult := do
  let some t := scene.things[id]? | throw "physics: missing player"
  if t.moveFlags.floating then throw "physics: floating actor is outside the live-player profile"
  let body := t.motion extra
  let onGround := body.z.raw ≤ body.floorz.raw
  let body := body.movePlayer cmd
  let view := view.calcHeight body levelTime onGround
  let scene := { scene with things := scene.things.set! id (t.withMotion body) }
  let result ← scene.advancePlayerXY id body cmd sectorAt cross
  let mut result := { result with view }
  if result.body.z != result.body.floorz || result.body.momz.raw != 0 then
    let (body, view, landing) := result.body.moveZ result.view
    let some t := result.scene.things[id]? | throw "physics: missing player after XY"
    result := { result with
      body, view, landing,
      scene := { result.scene with things := result.scene.things.set! id (t.withMotion body) } }
  return result

end Doom.Collision
