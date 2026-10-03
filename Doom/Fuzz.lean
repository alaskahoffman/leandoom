/-
R_DrawFuzzColumn, Chocolate Doom 3.1.1 r_draw.c,
commit 410d96855b5df5410ff591a90efeafa889119224.
Derived from id Software (1993-1996), Simon Howard (2005-2014).
SPDX-License-Identifier: GPL-2.0-or-later. See COPYING.md.
-/
import Init.Data.Vector.Basic

namespace Doom.Fuzz

abbrev Phase := Fin 50

/-- The original offsets are positive/negative SCREENWIDTH: rows above/below, despite the
original comment calling them left/right. This port uses the 320-pixel stride. -/
def below : Vector Bool 50 := #v[
  true,false,true,false,true,true,false,true,true,false,true,true,true,false,
  true,true,true,false,false,false,false,true,false,false,true,true,true,true,false,
  true,false,true,true,false,false,true,true,false,false,false,false,true,true,
  true,true,false,true,true,false,true]

structure Result where
  pixels : ByteArray
  phase : Phase
  low : Int
  high : Int

/-- Valid-column kernel. Callers supply a full 320x200 indexed buffer, at least
seven colormap rows, x<320, height in 3..200 and already clipped screen bounds.
Bounds are inclusive. The mutable read intentionally observes earlier writes.
The phase belongs to the renderer and persists across posts, sprites and frames. -/
def column (pixels colormaps : ByteArray) (phase : Phase)
    (x : Nat) (low high : Int) (height : Nat := 200) : Result := Id.run do
  let low := if low == 0 then 1 else low
  let high := if high == Int.ofNat height - 1 then Int.ofNat height - 2 else high
  let mut pixels := pixels
  let mut phase := phase
  if high < low then return ⟨pixels, phase, low, high⟩
  for y in [low.toNat:high.toNat+1] do
    let dest := y * 320 + x
    let source := if below.get phase then dest + 320 else dest - 320
    pixels := pixels.set! dest colormaps[6*256 + pixels[source]!.toNat]!
    phase := ⟨(phase.val + 1) % 50, Nat.mod_lt _ (by decide)⟩
  return ⟨pixels, phase, low, high⟩

def checkedColumn (pixels colormaps : ByteArray) (phase : Phase)
    (x : Nat) (low high : Int) (height : Nat := 200) : Except String Result := do
  if pixels.size != 320*200 || colormaps.size < 7*256 then throw "fuzz: invalid buffers"
  if x ≥ 320 || height < 3 || height > 200 || low < 0 || low > height ||
      high < -1 || high ≥ height then throw "fuzz: column outside supported viewport"
  return column pixels colormaps phase x low high height

end Doom.Fuzz
