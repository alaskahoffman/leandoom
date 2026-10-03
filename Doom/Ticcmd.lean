/-
Keyboard subset of G_BuildTiccmd, Chocolate Doom 3.1.1,
commit 410d96855b5df5410ff591a90efeafa889119224.
Derived from id Software (1993-1996), Simon Howard (2005-2014).
SPDX-License-Identifier: GPL-2.0-or-later. See COPYING.md.
-/
namespace Doom

/-- Gameplay fields of a vanilla tic command. Network consistency/chat live elsewhere. -/
structure Ticcmd where
  forwardMove : Int8 := 0
  sideMove : Int8 := 0
  angleTurn : Int16 := 0
  buttons : UInt8 := 0
  deriving BEq, Repr, Inhabited

structure MovementKeys where
  forward : Bool := false
  backward : Bool := false
  left : Bool := false
  right : Bool := false
  strafeLeft : Bool := false
  strafeRight : Bool := false
  strafe : Bool := false
  speed : Bool := false
  attack : Bool := false
  use : Bool := false
  deriving Inhabited

structure KeyboardState where
  turnHeld : Int32 := 0
  deriving BEq, Repr, Inhabited

/-- Keyboard movement/fire/use with normal full-resolution turning. No mouse,
joystick, weapon selection, special buttons, or demo-recording turn quantization.
Keep turnHeld even in strafe mode and when opposing turn keys cancel. -/
def KeyboardState.build (state : KeyboardState) (keys : MovementKeys)
    (ticdup : Int32 := 1) : Ticcmd × KeyboardState := Id.run do
  let held := if keys.left || keys.right then state.turnHeld + ticdup else 0
  let turn : Int := if held < 6 then 320 else if keys.speed then 1280 else 640
  let forward : Int := if keys.speed then 50 else 25
  let side : Int := if keys.speed then 40 else 24
  let signed (positive negative : Bool) (amount : Int) :=
    (if positive then amount else 0) - (if negative then amount else 0)
  let sideways := signed keys.strafeRight keys.strafeLeft side +
    (if keys.strafe then signed keys.right keys.left side else 0)
  return ({
    forwardMove := Int8.ofInt (signed keys.forward keys.backward forward)
    sideMove := Int8.ofInt (max (-50) (min 50 sideways))
    angleTurn := Int16.ofInt (if keys.strafe then 0 else signed keys.left keys.right turn)
    buttons := (if keys.attack then 1 else 0) ||| (if keys.use then 2 else 0)
  }, ⟨held⟩)

end Doom
