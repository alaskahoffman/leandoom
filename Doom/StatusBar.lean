/- Single-player ST_drawWidgets layout and incremental widget refresh, Chocolate Doom 3.1.1.
SPDX-License-Identifier: GPL-2.0-or-later. See Doom/Status.lean and COPYING.md. -/
import Doom.Render

namespace Doom.Status

/-- V_DrawPatch offsets and opaque posts, without COLORMAP lighting. Clipping
keeps malformed/custom patch extents inside our framebuffer. -/
def drawPatch (pixels : ByteArray) (patch : Patch) (x y : Int) : ByteArray := Id.run do
  let mut pixels := pixels
  for px in [:patch.image.width] do
    let sx := x-patch.leftOffset+Int.ofNat px
    if sx < 0 || sx ≥ 320 then continue
    for py in [:patch.image.height] do
      let sy := y-patch.topOffset+Int.ofNat py
      if sy < 0 || sy ≥ 200 then continue
      if let some index := patch.image.sample px py then
        pixels := pixels.set! (sy.toNat*320+sx.toNat) index
  return pixels

private def named (pixels : ByteArray) (patches : Std.HashMap String Patch)
    (label : String) (x y : Int) : ByteArray :=
  match patches[label]? with
  | some patch => drawPatch pixels patch x y
  | none => pixels -- optional minus; all other names validated by Assets.load

private def number (pixels backing : ByteArray) (patches : Std.HashMap String Patch)
    (labelPrefix : String) (value : Int32) (right y : Int) : ByteArray := Id.run do
  let some zero := patches[labelPrefix ++ "0"]? | return pixels
  let mut pixels := pixels
  -- STlib_drawNum clears even the 1994 sentinel. Use the immutable bar backing,
  -- not the previous frame (which could retain a fourth digit or old key).
  for dx in [:3*zero.image.width] do
    let x := right-Int.ofNat (3*zero.image.width)+Int.ofNat dx
    for dy in [:zero.image.height] do
      let sy := y+Int.ofNat dy
      if x ≥ 0 && x < 320 && sy ≥ 0 && sy < 200 then
        let pos := sy.toNat*320+x.toNat
        pixels := pixels.set! pos backing[pos]!
  for digit in digits value.toInt 3 zero.image.width right do
    pixels := named pixels patches (if digit.digit == 10 then "STTMINUS" else s!"{labelPrefix}{digit.digit}") digit.x y
  return pixels

/-- STlib restores an old icon's rectangle from STBAR, including transparent
pixels, before drawing the new patch. STARMS is a separate widget, not backing. -/
private def icon (pixels backing : ByteArray) (patches : Std.HashMap String Patch)
    (old : Option String) (label : String) (x y : Int) (refresh : Bool) : ByteArray := Id.run do
  if !refresh && old == some label then return pixels
  let mut pixels := pixels
  if let some old := old then
    if let some patch := patches[old]? then
      for dx in [:patch.image.width] do
        for dy in [:patch.image.height] do
          let sx := x-patch.leftOffset+Int.ofNat dx
          let sy := y-patch.topOffset+Int.ofNat dy
          if sx >= 0 && sx < 320 && sy >= 168 && sy < 200 then
            let pos := sy.toNat*320+sx.toNat
            pixels := pixels.set! pos backing[pos]!
  return named pixels patches label x y

/-- Vanilla single-player widgets, in ST_drawWidgets order. Numbers redraw on
all presentations; percents and STARMS only on full refresh; multi-icons restore
and redraw when their index changes. Multiplayer/frags remain unsupported. -/
def drawWithHistory (pixels : ByteArray) (patches : Std.HashMap String Patch)
    (player : Pickup.State) (face : Face) (previous : Option Widgets := none)
    : ByteArray × Widgets := Id.run do
  let refresh := previous.isNone
  let mut widgets := previous.getD {}
  let backing := named pixels patches "STBAR" 0 168
  let mut pixels := if refresh then backing else pixels
  pixels := number pixels backing patches "STTNUM" (readyAmmo player) 44 171
  for i in [:4] do
    let y := (#[173,179,191,185] : Array Int)[i]!
    pixels := number pixels backing patches "STYSNUM" player.ammo[i]! 288 y
    pixels := number pixels backing patches "STYSNUM" player.maxAmmo[i]! 314 y
  if refresh then pixels := named pixels patches "STTPRCNT" 90 171
  pixels := number pixels backing patches "STTNUM" player.health 90 171
  if refresh then pixels := named pixels patches "STTPRCNT" 221 171
  pixels := number pixels backing patches "STTNUM" player.armor 221 171
  if refresh then pixels := named pixels patches "STARMS" 104 168
  for i in [:6] do
    let label := if player.weapons[i+1]! then s!"STYSNUM{i+2}" else s!"STGNUM{i+2}"
    pixels := icon pixels backing patches widgets.arms[i]! label
      (111+Int.ofNat (i%3*12)) (172+Int.ofNat (i/3*10)) refresh
    widgets := { widgets with arms := widgets.arms.set! i (some label) }
  let label := faceName face.index
  pixels := icon pixels backing patches widgets.face label 143 168 refresh
  widgets := { widgets with face := some label }
  for i in [:3] do
    if h : i < 3 then
      if let some index := key player ⟨i,h⟩ then
        let label := s!"STKEYS{index}"
        pixels := icon pixels backing patches widgets.keys[i]! label 239 (171+Int.ofNat (i*10)) refresh
        widgets := { widgets with keys := widgets.keys.set! i (some label) }
  return (pixels,widgets)

/-- Fresh-screen convenience used by offline exporters. -/
def draw (pixels : ByteArray) (patches : Std.HashMap String Patch)
    (player : Pickup.State) (face : Face) : ByteArray :=
  (drawWithHistory pixels patches player face).1

def toRgb (art : Art) (pixels : ByteArray) (palette : Nat) : ByteArray := Id.run do
  let mut rgb := ByteArray.emptyWithCapacity (pixels.size*3)
  for index in pixels do
    let color := art.paletteColor index palette
    rgb := rgb.push color.r |>.push color.g |>.push color.b
  return rgb

end Doom.Status
