/- P_InitPicAnims / P_UpdateSpecials, Chocolate Doom 3.1.1.
Derived from id Software / Simon Howard. SPDX-License-Identifier: GPL-2.0-or-later. -/
namespace Doom.SurfaceAnimation

/-- The cycle includes every directory entry between these endpoints. -/
def definitions : Array (Bool × String × String) := #[
  (false,"NUKAGE1","NUKAGE3"),(false,"FWATER1","FWATER4"),
  (false,"SWATER1","SWATER4"),(false,"LAVA1","LAVA4"),(false,"BLOOD1","BLOOD3"),
  (false,"RROCK05","RROCK08"),(false,"SLIME01","SLIME04"),
  (false,"SLIME05","SLIME08"),(false,"SLIME09","SLIME12"),
  (true,"BLODGR1","BLODGR4"),(true,"SLADRIP1","SLADRIP3"),
  (true,"BLODRIP1","BLODRIP4"),(true,"FIREWALA","FIREWALL"),
  (true,"GSTFONT1","GSTFONT3"),(true,"FIRELAV3","FIRELAVA"),
  (true,"FIREMAG1","FIREMAG3"),(true,"FIREBLU1","FIREBLU2"),
  (true,"ROCKRED1","ROCKRED3"),(true,"BFALL1","BFALL4"),
  (true,"SFALL1","SFALL4"),(true,"WFALL1","WFALL4"),(true,"DBRAIN1","DBRAIN4")]

/-- Translation starts as identity. P_UpdateSpecials runs before leveltime++.
The phase uses the absolute resource index, not its offset within the cycle. -/
def frame (ticks base count index : Nat) : Nat :=
  if ticks == 0 || count == 0 then index else base + (((ticks-1)/8 + index) % count)

end Doom.SurfaceAnimation
