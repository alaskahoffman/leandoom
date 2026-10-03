/-
Player horizontal subset of P_Thrust, P_MovePlayer and P_XYMovement,
Chocolate Doom 3.1.1, commit 410d96855b5df5410ff591a90efeafa889119224.
Derived from id Software (1993-1996), Simon Howard (2005-2014).
SPDX-License-Identifier: GPL-2.0-or-later. See COPYING.md.
-/
import Doom.Angles
import Doom.Ticcmd

namespace Doom

/-- Player motion state; no corpse, missile, floating-monster, or skull-flying flags.
frame 0 is S_PLAY, 1..4 are S_PLAY_RUN1..4. Animation ticking is separate. -/
structure Motion where
  x : Fixed := ⟨0⟩
  y : Fixed := ⟨0⟩
  momx : Fixed := ⟨0⟩
  momy : Fixed := ⟨0⟩
  angle : Angle := ⟨0⟩
  z : Fixed := ⟨0⟩
  floorz : Fixed := ⟨0⟩
  momz : Fixed := ⟨0⟩
  ceilingz : Fixed := Fixed.ofInt 128
  height : Fixed := Fixed.ofInt 56
  noGravity : Bool := false
  frame : Fin 5 := 0
  noMomentum : Bool := false
  deriving BEq, Repr, Inhabited

def Motion.thrust (body : Motion) (angle : Angle) (move : Fixed) : Motion :=
  { body with momx := body.momx + move * angle.fineCosine
              momy := body.momy + move * angle.fineSine }

/-- Turn first, then forward thrust, then side thrust. Airborne commands still
turn and start the walking state, but do not add momentum. -/
def Motion.movePlayer (body : Motion) (cmd : Ticcmd) : Motion := Id.run do
  let mut body := { body with
    angle := ⟨body.angle.raw + (Int32.ofInt (cmd.angleTurn.toInt * 65536)).toUInt32⟩ }
  if body.z.raw ≤ body.floorz.raw then
    if cmd.forwardMove != 0 then
      body := body.thrust body.angle ⟨Int32.ofInt (cmd.forwardMove.toInt * 2048)⟩
    if cmd.sideMove != 0 then
      body := body.thrust ⟨body.angle.raw - 0x40000000⟩ ⟨Int32.ofInt (cmd.sideMove.toInt * 2048)⟩
  if (cmd.forwardMove != 0 || cmd.sideMove != 0) && body.frame == 0 then
    body := { body with frame := 1 }
  return body

def clampMomentum (value : Fixed) : Fixed :=
  ⟨max (-1966080) (min 1966080 value.raw)⟩

/-- After MAXMOVE clamping, the original positive-only split can run at most
once. The first half uses truncating division; the remainder uses arithmetic
shift. Negative odd values therefore retain the historical one-unit difference. -/
def Motion.xySteps (body : Motion) : Array (Fixed × Fixed) :=
  if body.momx.raw == 0 && body.momy.raw == 0 then #[] else
  let x := (clampMomentum body.momx).raw.toInt
  let y := (clampMomentum body.momy).raw.toInt
  if x > 983040 || y > 983040 then
    #[(⟨Int32.ofInt (x.tdiv 2)⟩, ⟨Int32.ofInt (y.tdiv 2)⟩),
      (⟨Int32.ofInt (x / 2)⟩, ⟨Int32.ofInt (y / 2)⟩)]
  else #[(⟨Int32.ofInt x⟩, ⟨Int32.ofInt y⟩)]

/-- A structural bound on unobstructed XY attempts, not a collision-equivalence proof. -/
theorem Motion.xySteps_size_le_two (body : Motion) : body.xySteps.size ≤ 2 := by
  unfold xySteps
  split <;> simp_all only [Array.size_empty, Nat.zero_le]
  split <;> simp

/-- Player branch of the post-XY friction rules, after collision handling. -/
def Motion.friction (body : Motion) (cmd : Ticcmd) : Motion :=
  if body.noMomentum then { body with momx := ⟨0⟩, momy := ⟨0⟩ }
  else if body.z.raw > body.floorz.raw then body
  else if body.momx.raw > -4096 && body.momx.raw < 4096 &&
      body.momy.raw > -4096 && body.momy.raw < 4096 &&
      cmd.forwardMove == 0 && cmd.sideMove == 0 then
    { body with momx := ⟨0⟩, momy := ⟨0⟩, frame := 0 }
  else { body with momx := body.momx * ⟨0xe800⟩, momy := body.momy * ⟨0xe800⟩ }

/-- Read-only evidence captured around the real friction call for the demo. -/
structure FrictionSample where
  before : Motion
  after : Motion
  cmd : Ticcmd
  deriving Inhabited

/-- P_XYMovement in an explicitly unobstructed fixture. Every attempted position
is returned in order. This is not map collision or a complete player tic. -/
def Motion.advanceUnobstructed (body : Motion) (cmd : Ticcmd) : Motion × Array (Fixed × Fixed) := Id.run do
  let steps := body.xySteps
  -- The original early return also bypasses frame reset and cheat handling.
  if steps.isEmpty then return (body, #[])
  let mut body := { body with momx := clampMomentum body.momx, momy := clampMomentum body.momy }
  let mut attempts := #[]
  for (dx, dy) in steps do
    body := { body with x := body.x + dx, y := body.y + dy }
    attempts := attempts.push (body.x, body.y)
  return (body.friction cmd, attempts)

end Doom
