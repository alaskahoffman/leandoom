/- R_InitTextureMapping and R_DrawPlanes sky mapping, Chocolate Doom 3.1.1.
Derived from id Software / Simon Howard. SPDX-License-Identifier: GPL-2.0-or-later.
Fixed 320-wide, high-detail profile. -/
import Doom.Fixed
import Doom.Tables

namespace Doom.RenderSky

/-- Original inverse screen-angle lookup before the viewangletox fencepost
cleanup. Use the shipped tangent table and integer rounding, not atan. -/
def angleColumnsUnclamped : Array Int32 := Id.run do
  let focal : Fixed := ⟨Int32.ofInt ((160 * 65536 * 65536 : Int) / Tables.fineTangent[3072]!.toInt)⟩
  let mut forward : Array Int32 := #[]
  for i in [:4096] do
    let tangent := Tables.fineTangent[i]!
    let x := if tangent > 131072 then -1 else if tangent < -131072 then 321 else
      max (-1 : Int32) (min 321 ((10485760 - ((⟨tangent⟩ : Fixed) * focal).raw + 65535) >>> 16))
    forward := forward.push x
  return forward

def angleColumns : Array Nat := angleColumnsUnclamped.map fun x => (max 0 (min 320 x)).toInt.toNat

def screenAngles : Array UInt32 := Id.run do
  let forward := angleColumnsUnclamped
  let mut inverse := #[]
  for x in [:321] do
    let index := (forward.findIdx? (· ≤ Int32.ofNat x)).getD 4095
    inverse := inverse.push ((UInt32.ofNat index <<< 19) - 0x40000000)
  return inverse

/-- ANGLETOSKYSHIFT: 1024 source columns per turn, independent of texture width. -/
def column (viewAngle : UInt32) (x : Nat) : Nat :=
  ((viewAngle + screenAngles[min x 320]!) >>> 22).toNat

/-- At full width pspriteiscale is FRACUNIT. R_DrawColumn wraps at 128 rows;
the sky midpoint stays at 100 even in the 168-pixel status-bar view. -/
def row (viewHeight y : Nat) : Nat :=
  (100 + Int.ofNat y - Int.ofNat (viewHeight / 2)).toInt32.toUInt32.toNat % 128

end Doom.RenderSky
