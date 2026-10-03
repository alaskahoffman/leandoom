/-
P_HitSlideLine, PTR_SlideTraverse, and P_SlideMove, Chocolate Doom 3.1.1,
commit 410d96855b5df5410ff591a90efeafa889119224.
Derived from id Software (1993-1996), Simon Howard (2005-2014).
SPDX-License-Identifier: GPL-2.0-or-later. See COPYING.md.
-/
import Doom.Path
import Doom.Move
import Doom.Angles

namespace Doom.Collision

def approximateDistance (dx dy : Fixed) : Except String Fixed := do
  let dx ← checkedPathAbs dx
  let dy ← checkedPathAbs dy
  return dx + dy - ⟨(if dx.raw < dy.raw then dx.raw else dy.raw) >>> 1⟩

def Line.hitSlide (line : Line) (x y mx my : Fixed) : Except String (Fixed × Fixed) := do
  if line.slope == .horizontal then return (mx, ⟨0⟩)
  if line.slope == .vertical then return (⟨0⟩, my)
  let base := (Angle.fromVector line.dx line.dy).raw
  let lineAngle : Angle := ⟨if line.pointSide x y then base + 0x80000000 else base⟩
  let delta := (Angle.fromVector mx my).raw - lineAngle.raw
  let deltaAngle : Angle := ⟨if delta > 0x80000000 then delta + 0x80000000 else delta⟩
  let length ← approximateDistance mx my
  let projected := length * deltaAngle.fineCosine
  return (projected * lineAngle.fineCosine, projected * lineAngle.fineSine)

private def blocksSlide (thing : SolidThing) (line : Line) : Except String Bool := do
  if !line.twoSided then return !line.pointSide thing.x thing.y
  let some back := line.back | throw "slide: two-sided line without a back sector"
  let top : Fixed := ⟨min line.front.ceiling.raw back.ceiling.raw⟩
  let bottom : Fixed := ⟨max line.front.floor.raw back.floor.raw⟩
  return (top - bottom).raw < thing.height.raw ||
    (top - thing.z).raw < thing.height.raw || (bottom - thing.z).raw > 1572864

structure SlideAttempt where
  x : Fixed
  y : Fixed
  accepted : Bool
  floatOK : Bool
  deriving Repr

structure SlideResult where
  scene : Scene
  attempts : Array SlideAttempt := #[]
  paths : Array PathResult := #[]
  crossings : Array Crossing := #[]

private def attempt (state : SlideResult) (id : Nat) (x y : Fixed) (sectorAt : SectorAt)
    (cross : Scene → Crossing → Except String Scene) : Except String (Bool × SlideResult) := do
  let moved ← state.scene.tryMove id x y sectorAt cross
  return (moved.decision.accepted, { state with
    scene := moved.scene
    attempts := state.attempts.push ⟨x, y, moved.decision.accepted, moved.decision.floatOK⟩
    crossings := state.crossings ++ moved.crossings })

private def stairstep (state : SlideResult) (id : Nat) (sectorAt : SectorAt)
    (cross : Scene → Crossing → Except String Scene) : Except String SlideResult := do
  let some thing := state.scene.things[id]? | throw "slide: invalid actor"
  let (ok, state) ← attempt state id thing.x (thing.y + thing.momy) sectorAt cross
  if ok then return state
  let some thing := state.scene.things[id]? | throw "slide: invalid actor"
  return (← attempt state id (thing.x + thing.momx) thing.y sectorAt cross).2

/-- Original three-corner slide, with two trace attempts before Y-then-X
stairstepping. Keeps the 0x800 approach fudge, unsigned angle quirks, first-hit
ties, and momentum changes even if the final move fails. Same callback domain
as Scene.tryMove; this is not the full XY friction/thinker sequence. -/
def Scene.slideMove (scene : Scene) (id : Nat) (sectorAt : SectorAt)
    (cross : Scene → Crossing → Except String Scene) : Except String SlideResult := do
  let mut state : SlideResult := { scene }
  for _ in [:2] do
    let some thing := state.scene.things[id]? | throw "slide: invalid actor"
    let leadx := if thing.momx.raw > 0 then thing.x + thing.radius else thing.x - thing.radius
    let trailx := if thing.momx.raw > 0 then thing.x - thing.radius else thing.x + thing.radius
    let leady := if thing.momy.raw > 0 then thing.y + thing.radius else thing.y - thing.radius
    let traily := if thing.momy.raw > 0 then thing.y - thing.radius else thing.y + thing.radius
    let blocked ← state.scene.lines.mapM (blocksSlide thing)
    let mut bestFrac : Fixed := ⟨65537⟩
    let mut bestLine := none
    for (x, y) in #[(leadx, leady), (trailx, leady), (leadx, traily)] do
      let path ← state.scene.pathTraverse x y (x + thing.momx) (y + thing.momy) 1
        fun hit _ => !blocked[hit.id]!
      state := { state with paths := state.paths.push path }
      if let some hit := path.visited.back? then
        if blocked[hit.id]! && hit.frac.raw < bestFrac.raw then
          bestFrac := hit.frac; bestLine := some hit.id
    let some lineId := bestLine | return ← stairstep state id sectorAt cross
    let approach := bestFrac - ⟨0x800⟩
    if approach.raw > 0 then
      let x := thing.x + thing.momx * approach
      let y := thing.y + thing.momy * approach
      let (ok, next) ← attempt state id x y sectorAt cross
      state := next
      if !ok then return ← stairstep state id sectorAt cross
    let remainder : Fixed := ⟨min 65536 (Fixed.ofInt 1 - (approach + ⟨0x800⟩)).raw⟩
    if remainder.raw ≤ 0 then return state
    -- A successful approach may have run immediate crossing callbacks.
    let some current := state.scene.things[id]? | throw "slide: callback removed actor"
    let some line := state.scene.lines[lineId]? | throw "slide: callback removed wall"
    let (mx, my) ← line.hitSlide current.x current.y (current.momx * remainder) (current.momy * remainder)
    let current := { current with momx := mx, momy := my }
    let scene := { state.scene with things := state.scene.things.set! id current }
    state := { state with scene }
    let (ok, next) ← attempt state id (current.x + mx) (current.y + my) sectorAt cross
    state := next
    if ok then return state
  stairstep state id sectorAt cross

end Doom.Collision
