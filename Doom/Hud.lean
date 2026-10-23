/- Single-player HUlib_drawTextLine, Chocolate Doom 3.1.1 hu_lib.c.
Derived from id Software / Simon Howard. SPDX-License-Identifier: GPL-2.0-or-later. -/
import Doom.StatusBar

namespace Doom.Hud

/-- Original one-line pickup message at (0,0), uppercase WAD font, four-pixel
spaces and unsupported characters, patch offsets, and right-edge termination.
Message pixels bypass COLORMAP but still receive the current PLAYPAL palette. -/
def draw (pixels : ByteArray) (font : Std.HashMap String Patch)
    (message : String) : ByteArray := Id.run do
  let mut pixels := pixels
  let mut x := 0
  for char in message.toList.take 80 do
    let code := char.toUpper.toNat
    if code ≥ 33 && code ≤ 95 then
      let some patch := font[s!"STCFN0{code}"]? | continue
      if x + patch.image.width > 320 then break
      pixels := Status.drawPatch pixels patch (Int.ofNat x) 0
      x := x + patch.image.width
    else
      x := x + 4
      if x ≥ 320 then break
  return pixels

end Doom.Hud
