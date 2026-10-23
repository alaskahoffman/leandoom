/- Fixed 320-wide high-detail R_AddLine, R_PointToDist, R_StoreWallRange,
R_ScaleFromGlobalAngle and R_MapPlane arithmetic, Chocolate Doom 3.1.1.
Derived from id Software / Simon Howard. SPDX-License-Identifier: GPL-2.0-or-later. -/
import Doom.Angles
import Doom.RenderSky

namespace Doom.RenderProjection

def mul (a b : Int32) : Int32 := (Fixed.mul ⟨a⟩ ⟨b⟩).raw

def divide (a b : Int32) : Int32 :=
  match Fixed.divChecked ⟨a⟩ ⟨b⟩ with
  | .ok q => q.raw
  | .error _ => panic! "renderer fixed division fault"

def sine (a : UInt32) : Int32 := Tables.fineSine[(a >>> 19).toNat]!
def cosine (a : UInt32) : Int32 := Tables.fineSine[(a >>> 19).toNat + 2048]!
/-- Grazing wall projections can address beyond the 4096-entry tangent table.
DOOM 1.9 places finesine immediately after it: model those fixed bytes explicitly
rather than triggering a Lean bounds panic. A shifted UInt32 index is < 8192,
so the overrun reaches at most the first 4096 sine entries. The original file
layout and all reachable values are checked by test_original_render_tables.py. -/
def tangent (a : UInt32) : Int32 :=
  let i := (a >>> 19).toNat
  if i < 4096 then Tables.fineTangent[i]!
  else Tables.fineSine[i - 4096]!

/-- Half-open screen interval from the original unsigned angle clipping. -/
def bounds (view a b : UInt32) : Option (Nat × Nat) := Id.run do
  let span := a - b
  if span ≥ 0x80000000 then return none
  let clip := RenderSky.screenAngles[0]!
  let mut a := a - view
  let mut b := b - view
  let t := a + clip
  if t > 2 * clip then
    if t - 2 * clip ≥ span then return none
    a := clip
  let t := clip - b
  if t > 2 * clip then
    if t - 2 * clip ≥ span then return none
    b := 0 - clip
  let first := RenderSky.angleColumns[((a + 0x40000000) >>> 19).toNat]!
  let stop := RenderSky.angleColumns[((b + 0x40000000) >>> 19).toNat]!
  return if first < stop then some (first,stop) else none

def pointDistance (x y : Int32) : Int32 :=
  let dx := max (Fixed.absWrap x) (Fixed.absWrap y)
  let dy := min (Fixed.absWrap x) (Fixed.absWrap y)
  let frac := if dx == 0 then 0 else divide dy dx
  let a := Tables.tanToAngle[(frac >>> 5).toInt.toNat]! + 0x40000000
  divide dx (sine a)

def scale (view normal : UInt32) (distance : Int32) (x : Nat) : Int32 :=
  let vis := view + RenderSky.screenAngles[x]!
  let num := mul 10485760 (sine (0x40000000 + vis - normal))
  let den := mul distance (sine (0x40000000 + vis - view))
  if den > (num >>> 16) then max 256 (min 4194304 (divide num den)) else 4194304

structure Wall where
  normal : UInt32
  distance : Int32
  offset : Int32
  centerAngle : UInt32
  deriving Inhabited, Repr

def wall (view bearing segAngle : UInt32) (dx dy textureOffset : Int32) : Wall := Id.run do
  let normal := segAngle + 0x40000000
  let off := min 0x40000000 (Fixed.absWrap (normal - bearing).toInt32).toUInt32
  let hyp := pointDistance dx dy
  let distance := mul hyp (sine (0x40000000 - off))
  let mut off := normal - bearing
  if off > 0x80000000 then off := 0 - off
  off := min off 0x40000000
  let offset := mul hyp (sine off)
  let offset := if normal - bearing < 0x80000000 then -offset else offset
  return ⟨normal,distance,offset + textureOffset,0x40000000 + view - normal⟩

def Wall.column (wall : Wall) (x : Nat) : Int32 :=
  (wall.offset - mul (tangent (wall.centerAngle + RenderSky.screenAngles[x]!)) wall.distance) >>> 16

/-- 20.12 screen-edge accumulator and its per-column step. -/
def edge (height scale step : Int32) (viewHeight : Nat) : Int32 × Int32 :=
  let height := height >>> 4
  (Int32.ofNat (viewHeight / 2 * 4096) - mul height scale, -mul step height)

structure PlaneSpan where
  distance : Int32
  xfrac : Int32
  yfrac : Int32
  xstep : Int32
  ystep : Int32
  deriving Inhabited, Repr

/-- R_DrawSpan's packed 6.10 coordinates. The low half's carry deliberately
reaches the high half; two independent 16.16 accumulators are not equivalent. -/
def packed (x y : Int32) : UInt32 :=
  ((x.toUInt32 <<< 10) &&& (0xffff0000 : UInt32)) ||| ((y.toUInt32 >>> 6) &&& (0xffff : UInt32))

def flatSpot (position : UInt32) : Nat :=
  ((position >>> 26) ||| ((position >>> 4) &&& 0xfc0)).toNat

def planeSpan (view : UInt32) (viewX viewY planeHeight : Int32) (viewHeight y x : Nat) : PlaneSpan :=
  let dy := Fixed.absWrap (Int32.ofNat (y * 65536) - Int32.ofNat (viewHeight / 2 * 65536) + 32768)
  let distance := mul planeHeight (divide 10485760 dy)
  let a := view - 0x40000000
  let xs := mul distance (divide (cosine a) 10485760)
  let ys := mul distance (-divide (sine a) 10485760)
  let length := mul distance (divide 65536 (Fixed.absWrap (cosine RenderSky.screenAngles[x]!)))
  let angle := view + RenderSky.screenAngles[x]!
  ⟨distance, viewX + mul (cosine angle) length, -viewY - mul (sine angle) length,xs,ys⟩

end Doom.RenderProjection
