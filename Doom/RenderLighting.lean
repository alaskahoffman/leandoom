/-
Colormap selection from Chocolate Doom 3.1.1 r_main.c/r_plane.c/r_things.c,
commit 410d96855b5df5410ff591a90efeafa889119224.
Derived from id Software (1993-1996), Simon Howard (2005-2014).
SPDX-License-Identifier: GPL-2.0-or-later. See COPYING.md.
-/
namespace Doom.RenderLighting

/-- A nonzero fixed map overrides ordinary light/distance selection. -/
def surface (fixed ordinary : Nat) : Nat := if fixed != 0 then fixed else ordinary

/-- Original sky exception: always use COLORMAP row zero. -/
def sky : Nat := 0

/-- None selects the original fuzz drawer, which is a separate rendering path.
Fixed maps take priority over fullbright, but not over shadow. -/
def sprite (fixed ordinary : Nat) (fullbright shadow : Bool) : Option Nat :=
  if shadow then none
  else some (if fixed != 0 then fixed else if fullbright then 0 else ordinary)

def weapon (fixed ordinary : Nat) (fullbright : Bool) (invisibility : Int32) : Option Nat :=
  sprite fixed ordinary fullbright (invisibility > 128 || invisibility &&& 8 != 0)

end Doom.RenderLighting
