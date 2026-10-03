/- Autoaim arithmetic from Chocolate Doom 3.1.1 p_map.c,
commit 410d96855b5df5410ff591a90efeafa889119224.
SPDX-License-Identifier: GPL-2.0-or-later. See COPYING.md. -/
import Doom.Fixed

namespace Doom.AutoAim

/-- Original signed addition followed by division toward zero, not floor. -/
def center (bottom top : Int32) : Fixed :=
  ⟨Int32.ofInt ((top + bottom).toInt.tdiv 2)⟩

structure Portal where
  distance : Fixed
  bottom : Fixed
  top : Fixed
  line : Nat
  deriving Inhabited

/-- Captured at the selected actor, after all preceding portal clipping. -/
structure Window where
  portalBottom : Int32
  portalTop : Int32
  targetBottom : Int32
  targetTop : Int32
  distance : Fixed
  shootZ : Fixed
  target : Nat
  targetZ : Fixed
  targetHeight : Fixed
  portals : Array Portal := #[]
  deriving Inhabited

def Window.bottom (w : Window) : Int32 := max w.targetBottom w.portalBottom
def Window.top (w : Window) : Int32 := min w.targetTop w.portalTop

structure Selection where
  slope : Fixed := ⟨0⟩
  facing : Angle := ⟨0⟩
  offset : UInt32 := 0
  window : Option Window := none
  deriving Inhabited

end Doom.AutoAim
