/-
R_PointToAngle and SlopeDiv ported from Chocolate Doom 3.1.1,
commit 410d96855b5df5410ff591a90efeafa889119224.
Derived from id Software (1993-1996), Simon Howard (2005-2014).
SPDX-License-Identifier: GPL-2.0-or-later. See COPYING.md.
-/
import Doom.Fixed
import Doom.Tables
import Init.Data.UInt.Lemmas
import Init.Omega

namespace Doom

/-- SlopeDiv deliberately wraps its unsigned numerator before dividing. -/
def slopeDiv (num den : UInt32) : Fin 2049 :=
  if den < 512 then ⟨2048, by decide⟩ else
    let answer := ((num <<< 3) / (den >>> 8)).toNat
    ⟨min answer 2048, by omega⟩

private def slopeAngle (num den : Int32) : UInt32 :=
  Tables.tanToAngle.get (slopeDiv num.toUInt32 den.toUInt32)

/-- R_PointToAngle, including octant-specific one-unit angle offsets and
signed 32-bit negation. Unlike atan2, axes/diagonals keep the original asymmetry. -/
def Angle.fromVector (dx dy : Fixed) : Angle := Id.run do
  let mut x := dx.raw
  let mut y := dy.raw
  if x == 0 && y == 0 then return ⟨0⟩
  if x ≥ 0 then
    if y ≥ 0 then
      if x > y then return ⟨slopeAngle y x⟩
      else return ⟨0x40000000 - 1 - slopeAngle x y⟩
    else
      y := -y
      if x > y then return ⟨0 - slopeAngle y x⟩
      else return ⟨0xc0000000 + slopeAngle x y⟩
  else
    x := -x
    if y ≥ 0 then
      if x > y then return ⟨0x80000000 - 1 - slopeAngle y x⟩
      else return ⟨0x40000000 + slopeAngle x y⟩
    else
      y := -y
      if x > y then return ⟨0x80000000 + slopeAngle y x⟩
      else return ⟨0xc0000000 - 1 - slopeAngle x y⟩

def Angle.between (originX originY x y : Fixed) : Angle :=
  Angle.fromVector (x - originX) (y - originY)

/-- Quantize a binary angle to DOOM's 8192-entry fine-angle range. -/
def Angle.fineIndex (angle : Angle) : Fin 8192 :=
  ⟨angle.raw.toNat / 524288, by have h := angle.raw.toNat_lt; omega⟩

def Angle.fineSine (angle : Angle) : Fixed :=
  ⟨Tables.fineSine.get ⟨angle.fineIndex.val, by have h := angle.fineIndex.isLt; omega⟩⟩

/-- finecosine points 2048 entries into the 10240-element sine table. -/
def Angle.fineCosine (angle : Angle) : Fixed :=
  ⟨Tables.fineSine.get ⟨angle.fineIndex.val + 2048, by have h := angle.fineIndex.isLt; omega⟩⟩

end Doom
