/- R_ProjectSprite / R_DrawMaskedColumn, Chocolate Doom 3.1.1.
Derived from id Software / Simon Howard. SPDX-License-Identifier: GPL-2.0-or-later. -/
import Doom.RenderProjection

namespace Doom.RenderSprite
open RenderProjection

structure Projection where
  depth : Int32
  scale : Int32
  first : Nat
  stop : Nat
  frac : Int32
  step : Int32
  texturemid : Int32
  deriving Inhabited, Repr

/-- Original rotated-patch selection, including the half-octant bias. -/
def direction (dx dy : Fixed) (facing : UInt32) : Nat :=
  (((Angle.fromVector dx dy).raw - facing + 0x90000000) >>> 29).toNat

def project (view : UInt32) (dx dy z viewz : Int32) (width left top : Int) (flip : Bool) : Option Projection := do
  let depth := mul dx (cosine view) - (-mul dy (sine view))
  if depth < 262144 then none else do
    let scale := divide 10485760 depth
    let tx := -(mul dy (cosine view) + (-mul dx (sine view)))
    if Fixed.absWrap tx > (depth <<< 2) then none else do
      let tx := tx - (Fixed.ofInt left).raw
      let first := ((10485760 + mul tx scale) >>> 16).toInt
      let last := ((10485760 + mul (tx + (Fixed.ofInt width).raw) scale) >>> 16).toInt - 1
      if first > 320 || last < 0 then none else do
        let x1 := max 0 first
        let x2 := min 319 last
        if x1 > x2 then none else do
          let step := divide 65536 scale
          let step := if flip then -step else step
          let frac := (if flip then (Fixed.ofInt width).raw - 1 else 0) + step * Int32.ofInt (x1-first)
          return ⟨depth,scale,x1.toNat,x2.toNat+1,frac,step,z + (Fixed.ofInt top).raw - viewz⟩

/-- Inclusive bounds of a patch post, before portal clipping. -/
def postBounds (scale texturemid : Int32) (height top count : Nat) : Int × Int :=
  let origin := Int32.ofNat (height / 2 * 65536) - mul texturemid scale
  let first := origin + scale * Int32.ofNat top
  let stop := first + scale * Int32.ofNat count
  (((first + 65535) >>> 16).toInt, ((stop - 1) >>> 16).toInt)

end Doom.RenderSprite
