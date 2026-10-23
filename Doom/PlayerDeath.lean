/- P_DeathThink view/turn branches, Chocolate Doom 3.1.1 p_user.c.
Derived from id Software / Simon Howard. SPDX-License-Identifier: GPL-2.0-or-later. -/
import Doom.PlayerPhysics

namespace Doom.PlayerDeath

/-- Original unsigned five-degree turn. Equality at either threshold takes a
turn step; damage flash only fades in the strict snap interval or without a killer. -/
def look (angle : UInt32) (attacker : Option UInt32) (damage : Int32) : UInt32 × Int32 :=
  let fade := if damage != 0 then damage-1 else damage
  match attacker with
  | none => (angle,fade)
  | some target =>
    let step : UInt32 := 0x40000000 / 18
    let delta := target-angle
    if delta < step || delta > 0-step then (target,fade)
    else if delta < 0x80000000 then (angle+step,damage)
    else (angle-step,damage)

/-- P_MovePsprites runs before this phase; mobj movement runs afterwards. -/
def view (state : ViewState) (body : Motion) (time : Int32) : ViewState :=
  let height := if state.height.raw > 6*65536 then state.height-Fixed.ofInt 1 else state.height
  let state := { state with height := ⟨max (6*65536) height.raw⟩, delta := ⟨0⟩ }
  state.calcHeight body time (body.z.raw ≤ body.floorz.raw) false

end Doom.PlayerDeath
