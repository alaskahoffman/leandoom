import Doom.Bsp
import Doom.Assets
import Doom.RenderLighting
import Doom.Fuzz

namespace Doom

structure Camera where
  x : Fixed
  y : Fixed
  z : Fixed
  angle : Angle
  deriving Inhabited, Repr

def Camera.spawn (m : Map) : Except String Camera := do
  let some start := m.things.find? (fun t => t.kind == 1)
    | throw "map has no player 1 start"
  let x := Fixed.ofInt start.position.x
  let y := Fixed.ofInt start.position.y
  let sector ← m.sectorAt x y
  return ⟨x, y, Fixed.ofInt (m.sectors[sector]!.floor + 41), Angle.ofDegrees start.angle⟩

def frameWidth : Nat := 320
def frameHeight : Nat := 200

/-- RGB24 framebuffer shared by the file exporter and SDL adapter. -/
def emptyFrame : ByteArray := ⟨Array.replicate (frameWidth * frameHeight * 3) 0⟩

structure IndexedFrame where
  rgb : ByteArray := emptyFrame
  indices : ByteArray := ⟨Array.replicate (frameWidth * frameHeight) 0⟩
  phase : Fuzz.Phase := 0
  viewHeight : Nat := 200
  depth : FloatArray := ⟨Array.replicate (frameWidth * frameHeight) 1000000000.0⟩

private def putPixel (pixels : IndexedFrame) (x y : Nat) (c : Color) (depth : Float) : IndexedFrame :=
  let p := y * frameWidth + x
  if depth > pixels.depth[p]! then pixels else
    let i := p * 3
    { pixels with
      rgb := pixels.rgb.set! i c.r |>.set! (i+1) c.g |>.set! (i+2) c.b
      depth := pixels.depth.set! p depth }

/-- Retain the lit palette index as well as RGB; fuzz reads this buffer directly. -/
def IndexedFrame.putIndex (pixels : IndexedFrame) (art : Art) (x y : Nat)
    (index : UInt8) (depth : Float := 0) : IndexedFrame :=
  let p := y * frameWidth + x
  if depth > pixels.depth[p]! then pixels else
    { (putPixel pixels x y (art.paletteColor index) depth) with
      indices := pixels.indices.set! p index }

/-- Draw a visible opaque post through the original high-detail fuzz kernel.
Callers clip posts to viewHeight (168 or 200) before calling this adapter. -/
def IndexedFrame.fuzzPost (pixels : IndexedFrame) (art : Art) (x start stop : Nat)
    (depth : Float := 0) : IndexedFrame := Id.run do
  if start ≥ stop then return pixels
  let fuzz := Fuzz.column pixels.indices art.colormaps pixels.phase x start (Int.ofNat stop - 1) pixels.viewHeight
  let mut pixels := { pixels with indices := fuzz.pixels, phase := fuzz.phase }
  if fuzz.high < fuzz.low then return pixels
  for y in [fuzz.low.toNat:fuzz.high.toNat+1] do
    pixels := putPixel pixels x y (art.paletteColor fuzz.pixels[y*frameWidth+x]!) depth
  return pixels

private def span (pixels : IndexedFrame) (x start stop : Nat) (color : Color) : IndexedFrame := Id.run do
  let mut pixels := pixels
  for y in [min start pixels.viewHeight:min stop pixels.viewHeight] do
    pixels := putPixel pixels x y color 0
  return pixels

private def row (height : Nat) (y : Float) : Nat :=
  ((max 0.0 (min height.toUInt64.toFloat (y - 0.5).ceil)).toUInt32).toNat

private def column (x : Float) : Nat :=
  ((max 0.0 (min 320.0 (x - 0.5).ceil)).toUInt32).toNat

private def intFloat (n : Int) : Float := n.toInt64.toFloat

private def surfaceColor (texture : String) (light : Int) (depth : Float)
    (kind : Nat) (horizontal : Bool := false) : Color := Id.run do
  let mut hash : Nat := 0
  for c in texture.toList do hash := (hash * 31 + c.toNat) % 65521
  let brightness := max 0.16 (min 1.0 (intFloat light / 255.0))
  let distance := 1.0 / (1.0 + depth / 1600.0)
  let shade := brightness * distance * (if horizontal then 0.82 else 1.0)
  let base := if kind == 0 then 95 else if kind == 1 then 70 else 115
  let channel := fun offset => ((base + (hash / offset) % 75).toUInt64.toFloat * shade).toUInt8
  return ⟨channel 1, channel 7, channel 43⟩

private def texel (n : Float) : Int := n.floor.toInt64.toInt

/-- Use the WAD's real light tables; distance-to-table selection is approximate. -/
private def lightTable (light : Int) (depth : Float) (horizontal : Bool := false) : Nat :=
  min 31 ((max 0 (255 - light)).toNat / 8 + (depth / 128.0).toUInt32.toNat +
    if horizontal then 1 else 0)

private def wallSpan (pixels : IndexedFrame) (assets : Assets) (texture : Texture)
    (camera : Camera) (x start stop : Nat) (u anchor depth : Float) (light : Nat)
    (masked : Bool := false) : IndexedFrame := Id.run do
  let mut pixels := pixels
  let column := texel u
  for y in [min start pixels.viewHeight:min stop pixels.viewHeight] do
    let worldZ := camera.z.toFloat + ((pixels.viewHeight.toUInt64.toFloat / 2) - (y.toUInt64.toFloat + 0.5)) * depth / 160.0
    let v := texel (anchor - worldZ)
    if masked && (v < 0 || v ≥ Int.ofNat texture.height) then continue
    if let some index := texture.sample column v then
      pixels := pixels.putIndex assets.art x y (assets.art.mapIndex index light) depth
  return pixels

private def planeSpan (pixels : IndexedFrame) (assets : Assets) (label : String)
    (height light : Int) (camera : Camera) (sin cos : Float) (x start stop : Nat) (fixed : Nat) : IndexedFrame := Id.run do
  let mut pixels := pixels
  let screenX := (x.toUInt64.toFloat + 0.5 - 160.0) / 160.0
  if label == "F_SKY1" then
    if let some sky := assets.sky then
      let u := texel ((camera.angle.radians - screenX.atan) * (sky.width.toUInt64.toFloat * 4.0 / 6.283185307179586))
      for y in [min start pixels.viewHeight:min stop pixels.viewHeight] do
        let v := max 0 (min (Int.ofNat sky.height - 1) (texel (100.0 + (y.toUInt64.toFloat - pixels.viewHeight.toUInt64.toFloat / 2) * 0.5)))
        if let some index := sky.sample u v then pixels := pixels.putIndex assets.art x y (assets.art.mapIndex index RenderLighting.sky) 999999999.0
  else if let some flat := assets.flats[label]? then
    let rayX := cos + screenX * sin
    let rayY := sin - screenX * cos
    for y in [min start pixels.viewHeight:min stop pixels.viewHeight] do
      let depth := (intFloat height - camera.z.toFloat) * 160.0 / (pixels.viewHeight.toUInt64.toFloat / 2 - y.toUInt64.toFloat - 0.5)
      if depth ≤ 0 then continue
      let wx := camera.x.toFloat + depth * rayX
      let wy := camera.y.toFloat + depth * rayY
      if let some index := flat.sample (texel wx) (texel (-wy)) then
        pixels := pixels.putIndex assets.art x y (assets.art.mapIndex index (RenderLighting.surface fixed (lightTable light depth))) depth
  return pixels

structure MaskedColumn where
  texture : Texture
  x : Nat
  start : Nat
  stop : Nat
  u : Float
  anchor : Float
  depth : Float
  light : Nat
  deriving Inhabited

private structure RenderState where
  pixels : IndexedFrame := {}
  top : Array Nat := Array.replicate frameWidth 0
  bottom : Array Nat := Array.replicate frameWidth frameHeight
  masked : Array MaskedColumn := #[]

private def drawSeg (m : Map) (camera : Camera) (sin cos : Float) (assets : Option Assets)
    (seg : Seg) (state : RenderState) (fixed : Nat) : RenderState := Id.run do
  let a := m.vertices[seg.v1]!
  let b := m.vertices[seg.v2]!
  let ax := intFloat a.x - camera.x.toFloat
  let ay := intFloat a.y - camera.y.toFloat
  let bx := intFloat b.x - camera.x.toFloat
  let bY := intFloat b.y - camera.y.toFloat
  -- Only the right/front side of a directed seg faces the camera.
  if ax * bY - ay * bx ≥ 0 then return state
  let mut az := ax * cos + ay * sin
  let mut bz := bx * cos + bY * sin
  let mut ar := ax * sin - ay * cos
  let mut br := bx * sin - bY * cos
  let line := m.lines[seg.linedef]!
  let side := m.sides[if seg.side == 0 then line.front else line.back]!
  let mut au := intFloat side.xOffset + seg.offset.toUInt64.toFloat
  let mut bu := au + ((bx - ax) * (bx - ax) + (bY - ay) * (bY - ay)).sqrt
  let near := 0.25
  if az < near && bz < near then return state
  if az < near then
    let fraction := (near - az) / (bz - az)
    ar := ar + (br - ar) * fraction
    au := au + (bu - au) * fraction
    az := near
  if bz < near then
    let fraction := (near - bz) / (az - bz)
    br := br + (ar - br) * fraction
    bu := bu + (au - bu) * fraction
    bz := near
  let left := 160.0 + 160.0 * ar / az
  let right := 160.0 + 160.0 * br / bz
  if right ≤ left || right ≤ 0 || left ≥ 320 then return state
  let front := m.sectors[side.sector]!
  let other := if seg.side == 0 then line.back else line.front
  let back := if line.flags / 4 % 2 != 0 then m.sides[other]?.map (fun s => m.sectors[s.sector]!) else none
  let mut pixels := state.pixels
  let mut tops := state.top
  let mut bottoms := state.bottom
  let mut masked := state.masked
  let wall := fun label => assets.bind (fun a => a.walls[label]?)
  let midTexture := wall side.middle
  let upperTexture := wall side.upper
  let lowerTexture := wall side.lower
  let lowerUnpegged := line.flags / 16 % 2 != 0
  let upperUnpegged := line.flags / 8 % 2 != 0
  let bothSky := front.ceilingTexture == "F_SKY1" && (back.map (·.ceilingTexture) == some "F_SKY1")
  for x in [column left:column right] do
    let top := tops[x]!
    let bottom := bottoms[x]!
    if top ≥ bottom then continue
    let t := (x.toUInt64.toFloat + 0.5 - left) / (right - left)
    let depth := 1.0 / ((1.0 - t) / az + t / bz)
    let u := ((1.0 - t) * au / az + t * bu / bz) * depth
    let project := fun height => row pixels.viewHeight (pixels.viewHeight.toUInt64.toFloat / 2 - (intFloat height - camera.z.toFloat) * 160.0 / depth)
    let ceiling := project (if bothSky then (back.getD front).ceiling else front.ceiling)
    let floor := project front.floor
    let ceilColor := if front.ceilingTexture == "F_SKY1" then ⟨74, 100, 127⟩
      else surfaceColor front.ceilingTexture front.light depth 0
    match assets with
    | none =>
      pixels := span pixels x top (min bottom ceiling) ceilColor
      pixels := span pixels x (max top floor) bottom (surfaceColor front.floorTexture front.light depth 1)
    | some art =>
      pixels := planeSpan pixels art front.ceilingTexture front.ceiling front.light camera sin cos x top (min bottom ceiling) fixed
      pixels := planeSpan pixels art front.floorTexture front.floor front.light camera sin cos x (max top floor) bottom fixed
    let wallColor := fun texture => surfaceColor texture front.light depth 2 (a.y == b.y)
    let drawWall := fun pixels first last label texture anchor =>
      match assets, texture with
      | some art, some tex => wallSpan pixels art tex camera x first last u (intFloat (anchor + side.yOffset)) depth
          (RenderLighting.surface fixed (lightTable front.light depth (a.y == b.y)))
      | none, _ => span pixels x first last (wallColor label)
      | _, _ => pixels
    match back with
    | none =>
      let anchor := if lowerUnpegged then front.floor + Int.ofNat ((midTexture.map (·.height)).getD 0) else front.ceiling
      pixels := drawWall pixels (max top ceiling) (min bottom floor) side.middle midTexture anchor
      tops := tops.set! x bottom
    | some back =>
      let openingTop := if bothSky then ceiling else project (min front.ceiling back.ceiling)
      let openingBottom := project (max front.floor back.floor)
      let upperAnchor := if upperUnpegged then front.ceiling else back.ceiling + Int.ofNat ((upperTexture.map (·.height)).getD 0)
      let lowerAnchor := if lowerUnpegged then (if bothSky then back.ceiling else front.ceiling) else back.floor
      if !bothSky then
        pixels := drawWall pixels (max top ceiling) (min bottom (min floor openingTop)) side.upper upperTexture upperAnchor
      pixels := drawWall pixels (max top (max ceiling openingBottom)) (min bottom floor) side.lower lowerTexture lowerAnchor
      if let some texture := midTexture then
        let start := max top openingTop
        let stop := min bottom openingBottom
        if start < stop then
          let anchor := if lowerUnpegged then max front.floor back.floor + Int.ofNat texture.height
            else min front.ceiling back.ceiling
          masked := masked.push ⟨texture, x, start, stop, u, intFloat (anchor + side.yOffset), depth,
            RenderLighting.surface fixed (lightTable front.light depth (a.y == b.y))⟩
      tops := tops.set! x (max top openingTop)
      bottoms := bottoms.set! x (min bottom openingBottom)
  return ⟨pixels, tops, bottoms, masked⟩

/-- Camera-to-actor bearing is reversed to select the actor-facing view (1..8). -/
def spriteDirection (dx dy : Float) (angle : Nat) : Nat :=
  let bearing := Float.atan2 (-dy) (-dx) - (Angle.ofDegrees angle).radians
  let octant := ((bearing + 0.39269908169872414) / 0.7853981633974483).floor.toInt64.toInt
  (octant % 8).toNat

private def drawThings (m : Map) (camera : Camera) (assets : Assets) (pixels : IndexedFrame) (tick : Nat) (poses : Std.HashMap Nat ThingPose) (fixed : Nat) (positions : Std.HashMap Nat (Fixed × Fixed × Fixed)) : IndexedFrame := Id.run do
  let mut pixels := pixels
  let sin := camera.angle.radians.sin
  let cos := camera.angle.radians.cos
  -- Background sprites must be present before a nearer fuzz sprite samples them.
  -- Projection/sector visitation are still the prototype renderer; deterministic
  -- equal-depth ordering retains map order rather than claiming vanilla BSP ties.
  let location := fun i => (positions[i]?).getD (Fixed.ofInt m.things[i]!.position.x,Fixed.ofInt m.things[i]!.position.y,⟨0⟩)
  let depthAt := fun i =>
    let (x,y,_) := location i
    (x.toFloat - camera.x.toFloat) * cos + (y.toFloat - camera.y.toFloat) * sin
  let order := (Array.range m.things.size).qsort (fun a b =>
    depthAt a > depthAt b || (depthAt a == depthAt b && a < b))
  for thingIndex in order do
    let thing := m.things[thingIndex]!
    if !thing.active then continue
    let some defn := thingDef thing.kind | continue
    let some pose := poses[thingIndex]? <|> thingPose thing.kind tick | continue
    let some views := assets.sprites[pose.frame]? | continue
    let (sx,sy,sz) := location thingIndex
    let dx := sx.toFloat - camera.x.toFloat
    let dy := sy.toFloat - camera.y.toFloat
    let depth := dx * cos + dy * sin
    if depth < 0.25 then continue
    let view := views[spriteDirection dx dy thing.angle]!
    let patch := view.patch
    let texture := patch.image
    let .ok sectorIndex := m.sectorAt (Fixed.ofInt thing.position.x) (Fixed.ofInt thing.position.y) | continue
    let sector := m.sectors[sectorIndex]!
    let base := if positions.contains thingIndex then sz.toFloat else intFloat (if defn.ceiling then sector.ceiling - Int.ofNat defn.height else sector.floor)
    let scale := 160.0 / depth
    let origin := if view.flipped then Int.ofNat texture.width - patch.leftOffset else patch.leftOffset
    let left := 160.0 + (dx * sin - dy * cos) * scale - intFloat origin * scale
    let top := pixels.viewHeight.toUInt64.toFloat / 2 - ((base + intFloat patch.topOffset) - camera.z.toFloat) * scale
    let right := left + texture.width.toUInt64.toFloat * scale
    let bottom := top + texture.height.toUInt64.toFloat * scale
    -- MT_SHADOWS (editor 58) has MF_SHADOW in the pinned info.c.
    let light := RenderLighting.sprite fixed (lightTable sector.light depth) pose.fullbright (thing.kind == 58)
    for x in [column left:column right] do
      let sourceX := texel ((x.toUInt64.toFloat + 0.5 - left) / scale)
      let u := if view.flipped then Int.ofNat texture.width - 1 - sourceX else sourceX
      let mut run : Option Nat := none
      for y in [row pixels.viewHeight top:row pixels.viewHeight bottom] do
        let v := texel ((y.toUInt64.toFloat + 0.5 - top) / scale)
        let index := if u < 0 || v < 0 || u ≥ Int.ofNat texture.width || v ≥ Int.ofNat texture.height
          then none else texture.sample u v
        if let some index := index then
          if depth ≤ pixels.depth[y*frameWidth+x]! then
            if let some light := light then
              pixels := pixels.putIndex assets.art x y (assets.art.mapIndex index light) depth
            else if run.isNone then run := some y
            continue
        if let some start := run then
          pixels := pixels.fuzzPost assets.art x start y depth
          run := none
      if let some start := run then pixels := pixels.fuzzPost assets.art x start (row pixels.viewHeight bottom) depth
  return pixels

/-- Textured when assets are supplied; `none` retains the diagnostic geometry view. -/
def renderFrame (m : Map) (camera : Camera) (assets : Option Assets := none) (tick : Nat := 0) (poses : Std.HashMap Nat ThingPose := {}) (fixed : Nat := 0) (phase : Fuzz.Phase := 0) (viewHeight : Nat := 200) (positions : Std.HashMap Nat (Fixed × Fixed × Fixed) := {}) : IndexedFrame := Id.run do
  let sin := camera.angle.radians.sin
  let cos := camera.angle.radians.cos
  let viewHeight := max 3 (min 200 viewHeight)
  let mut state : RenderState := { pixels := { phase, viewHeight }, bottom := Array.replicate frameWidth viewHeight }
  for index in m.frontToBack camera.x camera.y do
    let sub := m.subsectors[index]!
    for i in [sub.first:sub.first + sub.count] do
      state := drawSeg m camera sin cos assets m.segs[i]! state fixed
  let mut pixels := state.pixels
  if let some art := assets then
    -- Composite transparent midtextures far-to-near over the completed opaque scene.
    for i in [:state.masked.size] do
      let s := state.masked[state.masked.size - 1 - i]!
      pixels := wallSpan pixels art s.texture camera s.x s.start s.stop s.u s.anchor s.depth s.light true
    pixels := drawThings m camera art pixels tick poses fixed positions
  return pixels

def render (m : Map) (camera : Camera) (assets : Option Assets := none) (tick : Nat := 0)
    (poses : Std.HashMap Nat ThingPose := {}) (fixed : Nat := 0) : ByteArray :=
  (renderFrame m camera assets tick poses fixed).rgb

def ppm (pixels : ByteArray) : ByteArray :=
  s!"P6\n{frameWidth} {frameHeight}\n255\n".toUTF8 ++ pixels

end Doom
