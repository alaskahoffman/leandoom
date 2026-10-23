import Doom.Bsp
import Doom.Assets
import Doom.RenderLighting
import Doom.RenderProjection
import Doom.RenderSprite
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
  dosHeap : Option DosHeap.Heap := none
  dosError : Option String := none
  statusWidgets : Option Status.Widgets := none
  rgb : ByteArray := emptyFrame
  indices : ByteArray := ⟨Array.replicate (frameWidth * frameHeight) 0⟩
  phase : Fuzz.Phase := 0
  viewHeight : Nat := 200
  depth : FloatArray := ⟨Array.replicate (frameWidth * frameHeight) 1000000000.0⟩

/-- DOS resource requests occur at draw time, in renderer traversal order. -/
def IndexedFrame.acquireDos (pixels : IndexedFrame) (resource : Option DosHeap.Resource)
    (value : Int32 := 101) : IndexedFrame × Option UInt32 :=
  match pixels.dosHeap,resource with
  | some heap,some resource =>
    let action := match resource with
      | .lump i => DosHeap.load i value
      | .composite _ => DosHeap.acquire resource
    match action.run heap with
    | .ok (address,heap) => ({ pixels with dosHeap := some heap },some address)
    | .error error => ({ pixels with dosError := some error },none)
  | _,_ => (pixels,none)

private def bindColumn (pixels : IndexedFrame) (source : Option ColumnSource)
    : IndexedFrame × Option ColumnSource :=
  match source with
  | none => (pixels,none)
  | some source =>
    let (pixels,address) := pixels.acquireDos source.resource
    (pixels,some { source with address := address.or source.address })

private def sampleColumn (pixels : IndexedFrame) (art : Art) (source : ColumnSource) (row : Nat)
    : Option UInt8 :=
  source.sample row ((pixels.dosHeap.map (·.cache.zone.memory)).or art.dosMemory)

private def putPixel (pixels : IndexedFrame) (x y : Nat) (c : Color) (depth : Float) : IndexedFrame :=
  let p := y * frameWidth + x
  let i := p * 3
  { pixels with
    rgb := pixels.rgb.set! i c.r |>.set! (i+1) c.g |>.set! (i+2) c.b
    depth := pixels.depth.set! p depth }

/-- Retain the lit palette index as well as RGB; fuzz reads this buffer directly. -/
def IndexedFrame.putIndex (pixels : IndexedFrame) (art : Art) (x y : Nat)
    (index : UInt8) (depth : Float := 0) : IndexedFrame :=
  let p := y * frameWidth + x
  let i := p * 3
  let c := art.paletteColor index
  -- Consume the frame once. Retaining it across putPixel forces copy-on-write
  -- of the entire RGB/depth buffers for every individual pixel.
  { pixels with
    rgb := pixels.rgb.set! i c.r |>.set! (i+1) c.g |>.set! (i+2) c.b
    indices := pixels.indices.set! p index
    depth := pixels.depth.set! p depth }

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

/-- Wall texels use the original unsigned reciprocal and signed 16.16 stepping.
Depth is diagnostic metadata; visibility is decided by clipping and draw order. -/
private def fixedWallSpan (pixels : IndexedFrame) (assets : Assets) (texture : Texture)
    (x : Nat) (first last : Int) (u texturemid scale : Int32) (light : Nat)
    (masked : Bool := false) (requestEmpty : Bool := false) : IndexedFrame := Id.run do
  let first := max 0 first
  let last := min (Int.ofNat pixels.viewHeight - 1) last
  if first > last && !requestEmpty then return pixels
  let column := (u.toInt % Int.ofNat texture.width).toNat
  let (pixels,source) := bindColumn pixels ((texture.columnSources[column]?).getD none)
  if first > last then return pixels
  let step := (0xffffffff / scale.toUInt32).toInt32
  let mut frac := texturemid + Int32.ofInt (first - Int.ofNat (pixels.viewHeight / 2)) * step
  let depth := 10485760.0 / scale.toInt64.toFloat
  let mut pixels := pixels
  for y in [first.toNat:last.toNat+1] do
    let v := if masked then (frac >>> 16).toInt else ((frac >>> 16) &&& 127).toInt
    if !masked || (v ≥ 0 && v < Int.ofNat texture.height) then
      let sample := match source with
        | some source => sampleColumn pixels assets.art source v.toNat
        | none => texture.wallSample u.toInt v assets.art.dosMemory
      if let some index := sample then
        pixels := pixels.putIndex assets.art x y (assets.art.mapIndex index light) depth
      else if source.any (·.address.isSome) then
        pixels := { pixels with dosError := some s!"DOS wall read of unmodeled memory at {x},{y}" }
    frac := frac + step
  return pixels

structure MaskedColumn where
  texture : Texture
  x : Nat
  first : Int
  last : Int
  u : Int32
  texturemid : Int32
  scale : Int32
  light : Nat
  deriving Inhabited

/-- A visplane records one visible interval per column. Overlapping intervals
split into a second plane, preserving the original span starting points. -/
private structure Visplane where
  texture : String
  height : Int
  light : Int
  first : Nat := 320
  stop : Nat := 0
  top : Array Nat := Array.replicate 320 255
  bottom : Array Nat := Array.replicate 320 0
  deriving Inhabited

private structure DrawSeg where
  seg : Seg
  first : Nat
  stop : Nat
  scale1 : Int32
  scale2 : Int32
  topSil : Bool
  bottomSil : Bool
  topHeight : Int32
  bottomHeight : Int32
  top : Array Int
  bottom : Array Int
  maskFirst : Nat
  maskStop : Nat
  deriving Inhabited

private structure RenderState where
  pixels : IndexedFrame := {}
  top : Array Int := Array.replicate frameWidth (-1)
  bottom : Array Int := Array.replicate frameWidth frameHeight
  solid : Array Bool := Array.replicate frameWidth false
  masked : Array MaskedColumn := #[]
  planes : Array Visplane := #[]
  drawsegs : Array DrawSeg := #[]
  sectorOrder : Array Nat := #[]
  floorPlane : Nat := 0
  ceilingPlane : Nat := 0

private def findPlane (state : RenderState) (texture : String) (height light : Int) : RenderState × Nat :=
  let height := if texture == "F_SKY1" then 0 else height
  let light := if texture == "F_SKY1" then 0 else light
  match state.planes.findIdx? (fun p => p.texture == texture && p.height == height && p.light == light) with
  | some i => (state,i)
  | none => ({ state with planes := state.planes.push { texture,height,light } },state.planes.size)

private def checkPlane (state : RenderState) (id first stop : Nat) : RenderState × Nat := Id.run do
  let p := state.planes[id]!
  for x in [max first p.first:min stop p.stop] do
    if p.top[x]! != 255 then
      return ({ state with planes := state.planes.push { texture := p.texture, height := p.height, light := p.light, first,stop } },state.planes.size)
  return ({ state with planes := state.planes.set! id { p with first := min first p.first, stop := max stop p.stop } },id)

private def markPlane (state : RenderState) (id x : Nat) (first last : Int) : RenderState :=
  if first > last then state else
    let p := state.planes[id]!
    { state with planes := state.planes.set! id { p with top := p.top.set! x first.toNat, bottom := p.bottom.set! x last.toNat } }

private def drawPlanes (state : RenderState) (camera : Camera) (assets : Option Assets) (fixed : Nat) (extra : Int) : IndexedFrame := Id.run do
  let mut pixels := state.pixels
  for p in state.planes do
    if p.first ≥ p.stop then continue
    if p.texture == "F_SKY1" then
      for x in [p.first:p.stop] do
        if p.top[x]! == 255 then continue
        if let some sky := assets.bind (·.sky) then
          let u := RenderSky.column camera.angle.raw x % sky.width
          pixels := (bindColumn pixels ((sky.columnSources[u]?).getD none)).1
        for y in [p.top[x]!:p.bottom[x]!+1] do
          match assets with
          | some art =>
            if let some sky := art.sky then
              if let some index := sky.sample (Int.ofNat (RenderSky.column camera.angle.raw x)) (Int.ofNat (RenderSky.row pixels.viewHeight y)) then
                pixels := pixels.putIndex art.art x y (art.art.mapIndex index RenderLighting.sky) 999999999.0
          | none => pixels := putPixel pixels x y ⟨74,100,127⟩ 999999999.0
    else
      if let some flat := assets.bind (fun a => a.flats[p.texture]?) then
        pixels := (pixels.acquireDos flat.resource 1).1
      -- Enumerating maximal row runs produces the same spans as R_MakeSpans.
      -- Each run gets rounded coordinates, then uses the packed R_DrawSpan step.
      for y in [:pixels.viewHeight] do
        let mut start : Option Nat := none
        for x in [p.first:p.stop+1] do
          let inside := x < p.stop && p.top[x]! ≤ y && y ≤ p.bottom[x]!
          if inside then
            if start.isNone then start := some x
          else if let some x1 := start then
            let h := Fixed.absWrap ((Fixed.ofInt p.height).raw - camera.z.raw)
            let s := RenderProjection.planeSpan camera.angle.raw camera.x.raw camera.y.raw h pixels.viewHeight y x1
            let mut position := RenderProjection.packed s.xfrac s.yfrac
            let step := RenderProjection.packed s.xstep s.ystep
            let depth := s.distance.toInt64.toFloat / 65536.0
            for column in [x1:x] do
              match assets with
              | some art =>
                if let some flat := art.flats[p.texture]? then
                  let spot := RenderProjection.flatSpot position
                  if let some index := flat.sample (Int.ofNat (spot % 64)) (Int.ofNat (spot / 64)) then
                    let light := RenderLighting.surface fixed (RenderLighting.planeMap (RenderLighting.level p.light extra) s.distance.toUInt32.toNat)
                    pixels := pixels.putIndex art.art column y (art.art.mapIndex index light) depth
              | none => pixels := putPixel pixels column y (surfaceColor p.texture p.light depth (if p.height < camera.z.raw.toInt / 65536 then 1 else 0)) depth
              position := position + step
            start := none
      if let some flat := assets.bind (fun a => a.flats[p.texture]?) then
        pixels := (pixels.acquireDos flat.resource 101).1
  return pixels

private def drawSeg (m : Map) (camera : Camera) (assets : Option Assets)
    (seg : Seg) (state : RenderState) (fixed : Nat) (extra : Int) : RenderState := Id.run do
  let a := m.vertices[seg.v1]!
  let b := m.vertices[seg.v2]!
  let ax := (Fixed.ofInt a.x).raw - camera.x.raw
  let ay := (Fixed.ofInt a.y).raw - camera.y.raw
  let bearing := (Angle.fromVector ⟨ax⟩ ⟨ay⟩).raw
  let bearing2 := (Angle.between camera.x camera.y (Fixed.ofInt b.x) (Fixed.ofInt b.y)).raw
  let some (first,stop) := RenderProjection.bounds camera.angle.raw bearing bearing2 | return state
  let line := m.lines[seg.linedef]!
  let side := m.sides[if seg.side == 0 then line.front else line.back]!
  let front := m.sectors[side.sector]!
  let other := if seg.side == 0 then line.back else line.front
  let back := if line.flags / 4 % 2 != 0 then m.sides[other]?.map (fun s => m.sectors[s.sector]!) else none
  if let some back := back then
    if front.ceiling == back.ceiling && front.floor == back.floor &&
        front.ceilingTexture == back.ceilingTexture && front.floorTexture == back.floorTexture &&
        front.light == back.light && side.middle == "-" then return state
  let wall := fun label => assets.bind (fun a => a.walls[label]?)
  let midTexture := wall side.middle
  let upperTexture := wall side.upper
  let lowerTexture := wall side.lower
  let lowerUnpegged := line.flags / 16 % 2 != 0
  let upperUnpegged := line.flags / 8 % 2 != 0
  let bothSky := front.ceilingTexture == "F_SKY1" && (back.map (·.ceilingTexture) == some "F_SKY1")
  let solid := back.isNone || (back.any fun b => b.ceiling ≤ front.floor || b.floor ≥ front.ceiling)
  let worldtop := (Fixed.ofInt (if bothSky then (back.getD front).ceiling else front.ceiling)).raw - camera.z.raw
  let worldbottom := (Fixed.ofInt front.floor).raw - camera.z.raw
  let worldhigh := (Fixed.ofInt (back.getD front).ceiling).raw - camera.z.raw
  let worldlow := (Fixed.ofInt (back.getD front).floor).raw - camera.z.raw
  let markfloor := (solid || back.any (fun b => front.floor != b.floor || front.floorTexture != b.floorTexture || front.light != b.light)) && (Fixed.ofInt front.floor).raw < camera.z.raw
  let markceiling := (solid || back.any (fun b => worldtop != worldhigh || front.ceilingTexture != b.ceilingTexture || front.light != b.light)) && ((Fixed.ofInt front.ceiling).raw > camera.z.raw || front.ceilingTexture == "F_SKY1")
  let geom := RenderProjection.wall camera.angle.raw bearing (UInt32.ofNat seg.angle <<< 16) ax ay (Fixed.ofInt (side.xOffset + seg.offset)).raw
  let mut state := state
  -- Match solid-segment clipping: rounding is restarted for each visible fragment.
  let mut run : Option Nat := none
  for endx in [first:stop+1] do
    if endx < stop && !state.solid[endx]! then
      if run.isNone then run := some endx
      continue
    let some start := run | continue
    run := none
    let maskFirst := state.masked.size
    let last := endx - 1
    let scale1 := RenderProjection.scale camera.angle.raw geom.normal geom.distance start
    let scale2 := RenderProjection.scale camera.angle.raw geom.normal geom.distance last
    let step := if last > start then (scale2 - scale1) / Int32.ofNat (last-start) else 0
    let (topfrac,topstep) := RenderProjection.edge worldtop scale1 step state.pixels.viewHeight
    let (bottomfrac,bottomstep) := RenderProjection.edge worldbottom scale1 step state.pixels.viewHeight
    let (highfrac,highstep) := RenderProjection.edge worldhigh scale1 step state.pixels.viewHeight
    let (lowfrac,lowstep) := RenderProjection.edge worldlow scale1 step state.pixels.viewHeight
    let mut tf := topfrac
    let mut bf := bottomfrac
    let mut hf := highfrac
    let mut lf := lowfrac
    let mut scale := scale1
    if markceiling then
      let (s,id) := checkPlane state state.ceilingPlane start endx
      state := { s with ceilingPlane := id }
    if markfloor then
      let (s,id) := checkPlane state state.floorPlane start endx
      state := { s with floorPlane := id }
    for x in [start:endx] do
      let ct := state.top[x]!
      let cb := state.bottom[x]!
      let yl := max (((tf + 4095) >>> 12).toInt) (ct + 1)
      let yh := min ((bf >>> 12).toInt) (cb - 1)
      if markceiling then state := markPlane state state.ceilingPlane x (ct+1) (min (yl-1) (cb-1))
      if markfloor then state := markPlane state state.floorPlane x (max (yh+1) (ct+1)) (cb-1)
      -- Untextured portal columns need no tangent lookup. The original only
      -- calculates texture coordinates for textured segs.
      let depth := 10485760.0 / scale.toInt64.toFloat
      let light := RenderLighting.surface fixed (RenderLighting.scaleMap (RenderLighting.level front.light extra (if a.y == b.y then -1 else if a.x == b.x then 1 else 0)) (min 47 (scale >>> 12).toInt.toNat))
      let drawWall := fun pixels low high label texture anchor =>
        match assets,texture with
        | some art,some tex => fixedWallSpan pixels art tex x low high (geom.column x) ((Fixed.ofInt (anchor + side.yOffset)).raw - camera.z.raw) scale light false back.isNone
        | none,_ => span pixels x (max 0 low).toNat (max 0 (high+1)).toNat (surfaceColor label front.light depth 2 (a.y == b.y))
        | _,_ => pixels
      match back with
      | none =>
        let anchor := if lowerUnpegged then front.floor + Int.ofNat ((midTexture.map (·.height)).getD 0) else front.ceiling
        let pixels := drawWall state.pixels yl yh side.middle midTexture anchor
        state := { state with pixels, top := state.top.set! x state.pixels.viewHeight, bottom := state.bottom.set! x (-1) }
      | some back =>
        if worldhigh < worldtop && (upperTexture.isSome || assets.isNone) then
          let mid := min ((hf >>> 12).toInt) (cb-1)
          let anchor := if upperUnpegged then front.ceiling else back.ceiling + Int.ofNat ((upperTexture.map (·.height)).getD 0)
          let pixels := drawWall state.pixels yl mid side.upper upperTexture anchor
          state := { state with pixels, top := state.top.set! x (if mid ≥ yl then mid else yl-1) }
        else if markceiling then state := { state with top := state.top.set! x (yl-1) }
        if worldlow > worldbottom && (lowerTexture.isSome || assets.isNone) then
          let mid := max (((lf + 4095) >>> 12).toInt) (state.top[x]! + 1)
          let anchor := if lowerUnpegged then (if bothSky then back.ceiling else front.ceiling) else back.floor
          let pixels := drawWall state.pixels mid yh side.lower lowerTexture anchor
          state := { state with pixels, bottom := state.bottom.set! x (if mid ≤ yh then mid else yh+1) }
        else if markfloor then state := { state with bottom := state.bottom.set! x (yh+1) }
        if let some texture := midTexture then
          let anchor := if lowerUnpegged then max front.floor back.floor + Int.ofNat texture.height else min front.ceiling back.ceiling
          state := { state with masked := state.masked.push ⟨texture,x,state.top[x]!+1,state.bottom[x]!-1,geom.column x,(Fixed.ofInt (anchor+side.yOffset)).raw-camera.z.raw,scale,light⟩ }
      if solid then state := { state with solid := state.solid.set! x true }
      scale := scale + step
      tf := tf + topstep
      bf := bf + bottomstep
      hf := hf + highstep
      lf := lf + lowstep
    let maskStop := state.masked.size
    let mut topSil := back.isNone
    let mut bottomSil := back.isNone
    let mut topHeight : Int32 := -2147483648
    let mut bottomHeight : Int32 := 2147483647
    let mut topClip := state.top
    let mut bottomClip := state.bottom
    if let some b := back then
      if front.floor > b.floor then
        bottomSil := true
        bottomHeight := (Fixed.ofInt front.floor).raw
      else if (Fixed.ofInt b.floor).raw > camera.z.raw then bottomSil := true
      if front.ceiling < b.ceiling then
        topSil := true
        topHeight := (Fixed.ofInt front.ceiling).raw
      else if (Fixed.ofInt b.ceiling).raw < camera.z.raw then topSil := true
      if b.ceiling ≤ front.floor then
        bottomClip := Array.replicate 320 (-1)
        bottomSil := true
        bottomHeight := 2147483647
      if b.floor ≥ front.ceiling then
        topClip := Array.replicate 320 state.pixels.viewHeight
        topSil := true
        topHeight := -2147483648
      if maskStop > maskFirst then
        if !topSil then
          topSil := true
          topHeight := -2147483648
        if !bottomSil then
          bottomSil := true
          bottomHeight := 2147483647
    state := { state with drawsegs := state.drawsegs.push ⟨seg,start,endx,scale1,scale2,topSil,bottomSil,topHeight,bottomHeight,topClip,bottomClip,maskFirst,maskStop⟩ }
  return state

/-- Post boundaries are retained from WAD patches; composites use opaque runs. -/
private def texturePosts (texture : Texture) (u : Nat) : Array (Nat × Nat) := Id.run do
  if let some posts := texture.posts[u]? then return posts
  let mut posts := #[]
  let mut start : Option Nat := none
  for y in [:texture.height+1] do
    if y < texture.height && texture.coverage[y*texture.width+u]! != 0 then
      if start.isNone then start := some y
    else if let some first := start then
      posts := posts.push (first,y-first)
      start := none
  return posts

def drawPatchColumn (pixels : IndexedFrame) (art : Art) (texture : Texture)
    (x u : Nat) (scale texturemid iscale : Int32) (cliptop clipbottom : Int)
    (light : Option Nat) : IndexedFrame := Id.run do
  if u ≥ texture.width then return pixels
  let (pixels,bound) := bindColumn pixels ((texture.columnSources[u]?).getD none)
  let mut pixels := pixels
  let mut source := bound
  for (top,count) in texturePosts texture u do
    let postSource := source
    source := source.map fun s => { s with offset := s.offset + count + 4 }
    let (first,last) := RenderSprite.postBounds scale texturemid pixels.viewHeight top count
    let first := max 0 (max first (cliptop+1))
    let last := min (Int.ofNat pixels.viewHeight-1) (min last (clipbottom-1))
    if first > last then continue
    if let some light := light then
      let mut frac := texturemid - Int32.ofNat (top*65536) + Int32.ofInt (first-Int.ofNat (pixels.viewHeight/2))*iscale
      for y in [first.toNat:last.toNat+1] do
        let row := ((frac >>> 16) &&& 127).toInt.toNat
        -- R_DrawMaskedColumn points directly at the post data. Rounding can
        -- include its trailing padding; decoded coverage would omit that pixel.
        let sample := match postSource with
          | some s => if s.patch then sampleColumn pixels art s row
                      else texture.sample (Int.ofNat u) (Int.ofNat (top+row))
          | none => texture.sample (Int.ofNat u) (Int.ofNat (top+row))
        if let some index := sample then
          pixels := pixels.putIndex art x y (art.mapIndex index light) 0
        else if postSource.any (·.address.isSome) then
          pixels := { pixels with dosError := some s!"DOS sprite read of unmodeled memory at {x},{y}" }
        frac := frac + iscale
    else pixels := pixels.fuzzPost art x first.toNat (last.toNat+1) 0
  return pixels

private def drawMasked (pixels : IndexedFrame) (art : Art) (columns : Array MaskedColumn)
    (done : Array Bool) (first stop : Nat) : IndexedFrame × Array Bool := Id.run do
  let mut pixels := pixels
  let mut done := done
  for i in [first:stop] do
    if done[i]! then continue
    let c := columns[i]!
    let u := (c.u.toInt % Int.ofNat c.texture.width).toNat
    pixels := drawPatchColumn pixels art c.texture c.x u c.scale c.texturemid
      (0xffffffff / c.scale.toUInt32).toInt32 (c.first-1) (c.last+1) (some c.light)
    done := done.set! i true
  return (pixels,done)

private structure VisibleSprite where
  thing : Nat
  projection : RenderSprite.Projection
  patch : Patch
  light : Option Nat
  x : Fixed
  y : Fixed
  z : Int32
  top : Int32
  deriving Inhabited

private def drawThings (m : Map) (camera : Camera) (assets : Assets) (state : RenderState)
    (pixels : IndexedFrame) (tick : Nat) (poses : Std.HashMap Nat ThingPose) (fixed : Nat)
    (positions : Std.HashMap Nat (Fixed × Fixed × Fixed)) (extra : Int)
    (angles : Std.HashMap Nat Angle) (sectorLinks : Array (Array Nat)) : IndexedFrame := Id.run do
  let mut visible : Array VisibleSprite := #[]
  let mut locations : Array (Fixed × Fixed × Fixed × Nat) := #[]
  let mut lists := Array.replicate m.sectors.size (#[] : Array Nat)
  for i in [:m.things.size] do
    let t := m.things[i]!
    let defn := (thingDef t.kind).getD default
    let (x,y,z) := (positions[i]?).getD (Fixed.ofInt t.position.x,Fixed.ofInt t.position.y,⟨0⟩)
    let sec := (m.sectorAt x y).toOption.getD 0
    let z := if positions.contains i then z else Fixed.ofInt (if defn.ceiling then m.sectors[sec]!.ceiling - Int.ofNat defn.height else m.sectors[sec]!.floor)
    locations := locations.push (x,y,z,sec)
    lists := lists.set! sec (#[i] ++ lists[sec]!)
  if sectorLinks.size == lists.size then
    for sec in [:lists.size] do
      -- Render-only effects absent from the collision list retain spawn order.
      let extras := lists[sec]!.filter (fun id => !sectorLinks.any (·.contains id))
      lists := lists.set! sec (extras ++ sectorLinks[sec]!)
  for sector in state.sectorOrder do
    for i in lists[sector]! do
      let some thing := m.things[i]? | continue
      if !thing.active then continue
      let some _ := thingDef thing.kind | continue
      let some pose := poses[i]? <|> thingPose thing.kind tick | continue
      let some views := assets.sprites[pose.frame]? | continue
      let (x,y,z,sec) := locations[i]!
      let facing := (angles[i]?).getD (Angle.ofDegrees thing.angle)
      let view := views[RenderSprite.direction (x-camera.x) (y-camera.y) facing.raw]!
      let patch := view.patch
      let some projection := RenderSprite.project camera.angle.raw (x-camera.x).raw (y-camera.y).raw z.raw camera.z.raw (Int.ofNat patch.image.width) patch.leftOffset patch.topOffset view.flipped | continue
      let light := RenderLighting.sprite fixed (RenderLighting.scaleMap (RenderLighting.level m.sectors[sec]!.light extra) (min 47 (projection.scale >>> 12).toInt.toNat)) pose.fullbright (thing.kind == 58)
      if visible.size < 128 then
        visible := visible.push ⟨i,projection,patch,light,x,y,z.raw,z.raw+(Fixed.ofInt patch.topOffset).raw⟩
  -- Original selection-sort ordering is stable for equal scales.
  let order := (Array.range visible.size).qsort (fun a b =>
    visible[a]!.projection.scale < visible[b]!.projection.scale ||
    (visible[a]!.projection.scale == visible[b]!.projection.scale && a < b))
  let mut pixels := pixels
  let mut done := Array.replicate state.masked.size false
  for id in order do
    let v := visible[id]!
    let p := v.projection
    let mut top := Array.replicate 320 (-2 : Int)
    let mut bottom := Array.replicate 320 (-2 : Int)
    for i in [:state.drawsegs.size] do
      let ds := state.drawsegs[state.drawsegs.size-1-i]!
      let first := max p.first ds.first
      let stop := min p.stop ds.stop
      if first ≥ stop then continue
      let a := m.vertices[ds.seg.v1]!
      let b := m.vertices[ds.seg.v2]!
      let behind := max ds.scale1 ds.scale2 < p.scale ||
        (min ds.scale1 ds.scale2 < p.scale && !pointOnSide v.x v.y (Fixed.ofInt a.x) (Fixed.ofInt a.y) (Fixed.ofInt (b.x-a.x)) (Fixed.ofInt (b.y-a.y)))
      if behind then
        if ds.maskStop > ds.maskFirst then
          let (next,flags) := drawMasked pixels assets.art state.masked done (ds.maskFirst + first-ds.first) (ds.maskFirst + stop-ds.first)
          pixels := next
          done := flags
        continue
      for x in [first:stop] do
        if ds.bottomSil && v.z < ds.bottomHeight && bottom[x]! == -2 then bottom := bottom.set! x ds.bottom[x]!
        if ds.topSil && v.top > ds.topHeight && top[x]! == -2 then top := top.set! x ds.top[x]!
    let mut frac := p.frac
    for x in [p.first:p.stop] do
      let u := (frac >>> 16).toInt
      if u ≥ 0 && u < Int.ofNat v.patch.image.width then
        pixels := drawPatchColumn pixels assets.art v.patch.image x u.toNat p.scale p.texturemid
          (Fixed.absWrap p.step) (if top[x]! == -2 then -1 else top[x]!)
          (if bottom[x]! == -2 then pixels.viewHeight else bottom[x]!) v.light
      frac := frac + p.step
  for i in [:state.drawsegs.size] do
    let ds := state.drawsegs[state.drawsegs.size-1-i]!
    let (next,flags) := drawMasked pixels assets.art state.masked done ds.maskFirst ds.maskStop
    pixels := next
    done := flags
  return pixels

/-- R_CheckBBox: test the back child's angular extent against solid columns. -/
private def boxVisible (box : Bounds) (camera : Camera) (solid : Array Bool) : Bool := Id.run do
  let coords := #[Fixed.ofInt box.top,Fixed.ofInt box.bottom,Fixed.ofInt box.left,Fixed.ofInt box.right]
  let bx := if camera.x.raw ≤ coords[2]!.raw then 0 else if camera.x.raw < coords[3]!.raw then 1 else 2
  let byPos := if camera.y.raw ≥ coords[0]!.raw then 0 else if camera.y.raw > coords[1]!.raw then 1 else 2
  let pos := byPos*4+bx
  if pos == 5 then return true
  let corners : Array (Nat × Nat × Nat × Nat) := #[(3,0,2,1),(3,0,2,0),(3,1,2,0),(0,0,0,0),(2,0,2,1),(0,0,0,0),(3,1,3,0),(0,0,0,0),(2,0,3,1),(2,1,3,1),(2,1,3,0)]
  let (x1,y1,x2,y2) := corners[pos]!
  let a := (Angle.between camera.x camera.y coords[x1]! coords[y1]!).raw
  let b := (Angle.between camera.x camera.y coords[x2]! coords[y2]!).raw
  if a-b ≥ 0x80000000 then return true
  let some (first,stop) := RenderProjection.bounds camera.angle.raw a b | return false
  return (solid.extract first stop).any (!·)

/-- Textured when assets are supplied; `none` retains the diagnostic geometry view. -/
def renderFrame (m : Map) (camera : Camera) (assets : Option Assets := none) (tick : Nat := 0) (poses : Std.HashMap Nat ThingPose := {}) (fixed : Nat := 0) (phase : Fuzz.Phase := 0) (viewHeight : Nat := 200) (positions : Std.HashMap Nat (Fixed × Fixed × Fixed) := {}) (extra : Int := 0) (angles : Std.HashMap Nat Angle := {}) (sectorLinks : Array (Array Nat) := #[]) (previous : Option IndexedFrame := none) : IndexedFrame := Id.run do
  let assets := assets.map (·.atTick tick)
  let viewHeight := max 3 (min 200 viewHeight)
  -- R_RenderPlayerView does not clear the screen. Unpainted gaps retain the
  -- previous presentation's palette indices; depth/visibility start afresh.
  let pixels : IndexedFrame := match previous with
    | none => { phase, viewHeight }
    | some old => { rgb := old.rgb, indices := old.indices, phase, viewHeight, dosHeap := old.dosHeap, dosError := old.dosError }
  let mut state : RenderState := { pixels, bottom := Array.replicate frameWidth (Int.ofNat viewHeight) }
  let mut stack : List (Child × Option Bounds) := [(if m.nodes.isEmpty then .subsector 0 else .node (m.nodes.size-1),none)]
  let mut seenNodes := Array.replicate m.nodes.size false
  let mut seenSubs := Array.replicate m.subsectors.size false
  for _ in [:m.nodes.size*2+1] do
    let (child,box) :: rest := stack | break
    stack := rest
    if box.any (fun b => !boxVisible b camera state.solid) then continue
    let index ← match child with
      | .node i =>
        if !seenNodes[i]! then
          seenNodes := seenNodes.set! i true
          let n := m.nodes[i]!
          stack := if n.onLeft camera.x camera.y then (n.left,none) :: (n.right,some n.rightBounds) :: stack
            else (n.right,none) :: (n.left,some n.leftBounds) :: stack
        continue
      | .subsector i => pure i
    if seenSubs[index]! then continue
    seenSubs := seenSubs.set! index true
    let sub := m.subsectors[index]!
    let seg := m.segs[sub.first]!
    let line := m.lines[seg.linedef]!
    let side := m.sides[if seg.side == 0 then line.front else line.back]!
    let sector := m.sectors[side.sector]!
    if !state.sectorOrder.contains side.sector then state := { state with sectorOrder := state.sectorOrder.push side.sector }
    let (s,floorId) := findPlane state sector.floorTexture sector.floor sector.light
    let (s,ceilingId) := findPlane s sector.ceilingTexture sector.ceiling sector.light
    state := { s with floorPlane := floorId, ceilingPlane := ceilingId }
    for i in [sub.first:sub.first + sub.count] do
      state := drawSeg m camera assets m.segs[i]! state fixed extra
  let mut pixels := drawPlanes state camera assets fixed extra
  if let some art := assets then
    pixels := drawThings m camera art state pixels tick poses fixed positions extra angles sectorLinks
  return pixels

def render (m : Map) (camera : Camera) (assets : Option Assets := none) (tick : Nat := 0)
    (poses : Std.HashMap Nat ThingPose := {}) (fixed : Nat := 0) : ByteArray :=
  (renderFrame m camera assets tick poses fixed).rgb

def ppm (pixels : ByteArray) : ByteArray :=
  s!"P6\n{frameWidth} {frameHeight}\n255\n".toUTF8 ++ pixels

end Doom
