/-
Player branches of P_ZMovement and P_CalcHeight, Chocolate Doom 3.1.1,
commit 410d96855b5df5410ff591a90efeafa889119224.
Derived from id Software (1993-1996), Simon Howard (2005-2014).
SPDX-License-Identifier: GPL-2.0-or-later. See COPYING.md.
-/
import Doom.Motion

namespace Doom

structure ViewState where
  height : Fixed := Fixed.ofInt 41
  delta : Fixed := ⟨0⟩
  z : Fixed := ⟨0⟩
  bob : Fixed := ⟨0⟩
  deriving BEq, Repr, Inhabited

/-- Integer division in FINEANGLES/20 is intentional: the increment is 409,
not a fractional twentieth of a revolution. Wrapping precedes the index mask. -/
def ViewState.bobIndex (levelTime : Int32) : Fin 8192 :=
  ⟨(levelTime * 409).toUInt32.toNat % 8192, Nat.mod_lt _ (by decide)⟩

/-- Original bob amplitude: square each component in fixed point, wrap their
sum, then round down when quartering and apply the upper cap. -/
def ViewState.bobAmplitude (momx momy : Fixed) : Fixed :=
  let momentumSquared := momx * momx + momy * momy
  ⟨min 0x100000 (Int32.ofInt (momentumSquared.raw.toInt / 4))⟩

/-- The signed half rounds toward zero, unlike the amplitude's quarter. -/
def ViewState.bobOffset (bob : Fixed) (levelTime : Int32) : Fixed :=
  let index := bobIndex levelTime
  let sine : Fixed := ⟨Tables.fineSine.get ⟨index.val, by have h := index.isLt; omega⟩⟩
  (⟨Int32.ofInt (bob.raw.toInt.tdiv 2)⟩ : Fixed) * sine

/-- Live-player view-height recovery, including wrapping delta and the original
one-unit sentinel that prevents recovery from stopping at exactly zero. -/
def ViewState.recoverHeight (view : ViewState) : ViewState :=
  let sum := view.height + view.delta
  let height := if sum.raw ≤ 2686976 then sum else Fixed.ofInt 41
  let delta := if sum.raw ≤ 2686976 then view.delta else ⟨0⟩
  let delta := if height.raw < 1343488 then
    (if 0 < delta.raw then delta else ⟨1⟩) else delta
  let height := if height.raw < 1343488 then ⟨1343488⟩ else height
  let delta := if delta.raw == 0 then delta else
    let next := delta + ⟨16384⟩
    if next.raw == 0 then ⟨1⟩ else next
  { view with height, delta }

/-- Final grounded view clamp. Additions and the ceiling subtraction wrap before
the signed comparison, just as in the original instruction sequence. -/
def ViewState.clampZ (body : Motion) (height offset : Fixed) : Fixed :=
  ⟨min (body.z + height + offset).raw (body.ceilingz - Fixed.ofInt 4).raw⟩

/-- P_CalcHeight. onGround is the caller's captured grounding state, not a new
collision query. The live flag controls only height recovery; death thinking is
outside this function. The airborne/no-momentum branch deliberately has no final
ceiling clamp: upstream overwrites the result of its first clamp. -/
def ViewState.calcHeight (view : ViewState) (body : Motion)
    (levelTime : Int32) (onGround : Bool) (live : Bool := true) : ViewState := Id.run do
  let bob := bobAmplitude body.momx body.momy
  let mut view := { view with bob }
  if body.noMomentum || !onGround then
    return { view with z := body.z + view.height }
  let offset := bobOffset bob levelTime
  if live then
    view := view.recoverHeight
  return { view with z := clampZ body view.height offset }

/-- Player-only P_ZMovement. The Boolean is the emitted landing `oof` event;
sound playback belongs to the platform/audio path. Floor clipping precedes ceiling
clipping, even in a space too short to contain the body. -/
def Motion.moveZ (body : Motion) (view : ViewState) : Motion × ViewState × Bool := Id.run do
  let mut body := body
  let mut view := view
  let mut landing := false
  if body.z.raw < body.floorz.raw then
    let height := view.height - (body.floorz - body.z)
    view := { view with
      height := height
      delta := ⟨Int32.ofInt ((Fixed.ofInt 41 - height).raw.toInt / 8)⟩ }
  body := { body with z := body.z + body.momz }
  if body.z.raw ≤ body.floorz.raw then
    if body.momz.raw < 0 then
      if body.momz.raw < -524288 then
        view := { view with delta := ⟨Int32.ofInt (body.momz.raw.toInt / 8)⟩ }
        landing := true
      body := { body with momz := ⟨0⟩ }
    body := { body with z := body.floorz }
  else if !body.noGravity then
    body := { body with momz := if body.momz.raw == 0 then ⟨-131072⟩
                               else body.momz - Fixed.ofInt 1 }
  if (body.z + body.height).raw > body.ceilingz.raw then
    body := { body with z := body.ceilingz - body.height,
                        momz := if body.momz.raw > 0 then ⟨0⟩ else body.momz }
  return (body, view, landing)

structure PhysicsResult where
  body : Motion
  view : ViewState
  attempts : Array (Fixed × Fixed)
  landing : Bool

/-- Normal live-player movement sequence with no obstruction, reaction-time
delay, sector actions, weapons, or animation ticking. Captures the relative order
in P_PlayerThink and P_MobjThinker; it is not a complete DOOM tic. -/
def Motion.physicsUnobstructed (body : Motion) (view : ViewState)
    (cmd : Ticcmd) (levelTime : Int32) : PhysicsResult := Id.run do
  let onGround := body.z.raw ≤ body.floorz.raw
  let body := body.movePlayer cmd
  let view := view.calcHeight body levelTime onGround
  let (body, attempts) := body.advanceUnobstructed cmd
  if body.z != body.floorz || body.momz.raw != 0 then
    let (body, view, landing) := body.moveZ view
    return ⟨body, view, attempts, landing⟩
  return ⟨body, view, attempts, false⟩

end Doom
