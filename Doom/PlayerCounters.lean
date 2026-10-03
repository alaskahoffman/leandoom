/-
Live-player counter/colormap stage of P_PlayerThink, Chocolate Doom 3.1.1,
commit 410d96855b5df5410ff591a90efeafa889119224, p_user.c.
Derived from id Software (1993-1996), Simon Howard (2005-2014).
SPDX-License-Identifier: GPL-2.0-or-later. See COPYING.md.
-/
import Doom.Pickup

namespace Doom.Pickup

/-- Runs after weapon sprites in PlayerThink, before the mobj movement thinker.
The dead-player branch returns before this stage. DeathThink is a separate port.
Nonzero signed counters retain C wrapping and bit tests, including negative values. -/
def State.tickCounters (initial : State) : State := Id.run do
  let mut s := initial
  if s.powers[1] != 0 then s := { s with powers := s.powers.set 1 (s.powers[1] + 1) }
  if s.powers[0] != 0 then s := { s with powers := s.powers.set 0 (s.powers[0] - 1) }
  if s.powers[2] != 0 then
    s := { s with powers := s.powers.set 2 (s.powers[2] - 1) }
    if s.powers[2] == 0 then s := { s with shadow := false }
  if s.powers[5] != 0 then s := { s with powers := s.powers.set 5 (s.powers[5] - 1) }
  if s.powers[3] != 0 then s := { s with powers := s.powers.set 3 (s.powers[3] - 1) }
  if s.damageCount != 0 then s := { s with damageCount := s.damageCount - 1 }
  if s.bonus != 0 then s := { s with bonus := s.bonus - 1 }
  let active (n : Int32) := n > 128 || n &&& 8 != 0
  let fixedColormap : Int32 :=
    if s.powers[0] != 0 then (if active s.powers[0] then 32 else 0)
    else if s.powers[5] != 0 then (if active s.powers[5] then 1 else 0)
    else 0
  return { s with fixedColormap }

end Doom.Pickup
