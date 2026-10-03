/-
T_VerticalDoor from Chocolate Doom 3.1.1 p_doors.c,
commit 410d96855b5df5410ff591a90efeafa889119224.
Derived from id Software (1993-1996), Simon Howard (2005-2014).
SPDX-License-Identifier: GPL-2.0-or-later. See COPYING.md.
-/
import Doom.Plane

namespace Doom.VerticalDoor

inductive Kind where
  | normal | close30ThenOpen | close | open | raiseIn5Mins
  | blazeRaise | blazeOpen | blazeClose
  deriving BEq, Repr, Inhabited

inductive Sound where
  | close | open | blazeClose
  deriving BEq, Repr, Inhabited

structure State where
  kind : Kind := .normal
  top : Fixed := ⟨0⟩
  speed : Fixed := Fixed.ofInt 2
  direction : Int32 := 1
  topWait : Int32 := 150
  countdown : Int32 := 0
  deriving BEq, Repr, Inhabited

structure Step (σ : Type) where
  door : State
  heights : Plane.Heights
  state : σ
  removed : Bool := false
  sounds : Array Sound := #[]

/-- One original vertical-door thinker tick. Sound requests and removal are
explicit outputs; the host owns playback and thinker-list lifetime. -/
def State.tick (door : State) (heights : Plane.Heights) (state : σ)
    (change : Plane.Heights → Bool → σ → Bool × σ) : Step σ := Id.run do
  let mut out : Step σ := ⟨door,heights,state,false,#[]⟩
  if door.direction == 0 || door.direction == 2 then
    out := { out with door := { door with countdown := door.countdown - 1 } }
    if out.door.countdown != 0 then return out
    if door.direction == 2 then
      if door.kind == .raiseIn5Mins then
        out := { out with door := { out.door with direction := 1, kind := .normal }, sounds := #[.open] }
    else
      match door.kind with
      | .blazeRaise => out := { out with door := { out.door with direction := -1 }, sounds := #[.blazeClose] }
      | .normal => out := { out with door := { out.door with direction := -1 }, sounds := #[.close] }
      | .close30ThenOpen => out := { out with door := { out.door with direction := 1 }, sounds := #[.open] }
      | _ => pure ()
    return out
  if door.direction != -1 && door.direction != 1 then return out
  let result := Plane.move heights door.speed (if door.direction == -1 then heights.floor else door.top)
    false .ceiling door.direction state change
  out := { out with heights := result.heights, state := result.state }
  if door.direction == -1 then
    if result.result == .pastDestination then
      match door.kind with
      | .blazeRaise | .blazeClose => out := { out with removed := true, sounds := #[.blazeClose] }
      | .normal | .close => out := { out with removed := true }
      | .close30ThenOpen => out := { out with door := { door with direction := 0, countdown := 35*30 } }
      | _ => pure ()
    else if result.result == .crushed then
      match door.kind with
      | .blazeClose | .close => pure ()
      | _ => out := { out with door := { door with direction := 1 }, sounds := #[.open] }
  else if result.result == .pastDestination then
    match door.kind with
    | .blazeRaise | .normal => out := { out with door := { door with direction := 0, countdown := door.topWait } }
    | .close30ThenOpen | .blazeOpen | .open => out := { out with removed := true }
    | _ => pure ()
  return out

end Doom.VerticalDoor
