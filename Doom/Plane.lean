/-
T_MovePlane from Chocolate Doom 3.1.1 p_floor.c,
commit 410d96855b5df5410ff591a90efeafa889119224.
Derived from id Software (1993-1996), Simon Howard (2005-2014).
SPDX-License-Identifier: GPL-2.0-or-later. See COPYING.md.
-/
import Doom.Fixed

namespace Doom.Plane

inductive Kind where
  | floor | ceiling
  deriving BEq, Repr, Inhabited

inductive Result where
  | ok | crushed | pastDestination
  deriving BEq, Repr, Inhabited

structure Heights where
  floor : Fixed := ⟨0⟩
  ceiling : Fixed := ⟨0⟩
  deriving BEq, Repr, Inhabited

structure Step (σ : Type) where
  heights : Heights
  state : σ
  result : Result

/-- Original fixed-width plane movement. The callback stands for P_ChangeSector:
it observes each tentative/restored height and carries actor effects forward.
Rolling back a plane does not roll back callback effects. This routine itself
does not implement actor clipping, damage, or the sector blockbox traversal. -/
def move (heights : Heights) (speed destination : Fixed) (crush : Bool)
    (plane : Kind) (direction : Int32) (state : σ)
    (change : Heights → Bool → σ → Bool × σ) : Step σ := Id.run do
  if direction != -1 && direction != 1 then return ⟨heights,state,.ok⟩
  let old := if plane == .floor then heights.floor else heights.ceiling
  let proposed := if direction == -1 then old - speed else old + speed
  let past := if direction == -1 then proposed.raw < destination.raw else proposed.raw > destination.raw
  let height := if past then destination else proposed
  let next := if plane == .floor then { heights with floor := height } else { heights with ceiling := height }
  let (blocked,state) := change next crush state
  let ignoresBlock := plane == .ceiling && direction == 1
  let keepsCrushing := crush && ((plane == .floor && direction == 1) || (plane == .ceiling && direction == -1))
  if blocked && (past || (!ignoresBlock && !keepsCrushing)) then
    let (_,state) := change heights crush state
    return ⟨heights,state,if past then .pastDestination else .crushed⟩
  return ⟨next,state,if past then .pastDestination else if blocked && !ignoresBlock then .crushed else .ok⟩

end Doom.Plane
