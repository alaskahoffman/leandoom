import Doom.Map
import Doom.Actors
import Doom.ImpactData
import Doom.SurfaceAnimation
import Doom.Status
import Doom.DosHeap
import Std.Data.HashMap

namespace Doom
open Binary

structure Color where
  r : UInt8
  g : UInt8
  b : UInt8
  deriving Inhabited, BEq, Repr

structure ColumnSource where
  bytes : ByteArray
  offset : Nat
  /-- Patch posts have headers and padding; composite columns are packed pixels. -/
  patch : Bool := true
  /-- Address of the backing buffer in a modeled DOS heap, when explicitly bound.
  This is a guest address, not a native pointer. -/
  address : Option UInt32 := none
  resource : Option DosHeap.Resource := none
  deriving Inhabited

/-- Once bound, the guest heap is authoritative, even for in-buffer samples.
Missing guest memory remains absent; it never falls back to a stale WAD copy. -/
def ColumnSource.sample (source : ColumnSource) (row : Nat)
    (memory : Option DosMemory.Memory := none) : Option UInt8 :=
  match source.address with
  | none => source.bytes[source.offset+row]?
  | some base => memory >>= fun m => m.read8 (base + source.offset.toUInt32 + row.toUInt32)

structure Texture where
  width : Nat
  height : Nat
  pixels : ByteArray
  coverage : ByteArray
  posts : Array (Array (Nat × Nat)) := #[]
  /-- R_GetColumn points into a patch lump or the packed composite-column cache.
  Retain the whole backing buffer so wall sampling can read beyond one column. -/
  columnSources : Array (Option ColumnSource) := #[]
  resource : Option DosHeap.Resource := none
  deriving Inhabited

def Texture.empty (width height : Nat) : Texture :=
  ⟨width, height, ⟨Array.replicate (width * height) 0⟩, ⟨Array.replicate (width * height) 0⟩, #[], #[], none⟩

def Texture.sample (t : Texture) (x y : Int) : Option UInt8 := do
  if t.width == 0 || t.height == 0 then none else do
    let i := (y % Int.ofNat t.height).toNat * t.width + (x % Int.ofNat t.width).toNat
    if t.coverage[i]! == 0 then none else some t.pixels[i]!

/-- Opaque walls read from R_GetColumn's data pointer, without wrapping at the
declared height. This includes patch padding and the next cached column.
Unbound buffers remain bounded; explicitly bound buffers can read adjacent
modeled DOS bytes while staying inside safe Lean memory. -/
def Texture.wallSample (t : Texture) (x y : Int)
    (memory : Option DosMemory.Memory := none) : Option UInt8 := do
  if t.width == 0 then none else do
    let column := (x % Int.ofNat t.width).toNat
    if let some source := (t.columnSources[column]?).getD none then
      if y < 0 then none else source.sample y.toNat memory
    else t.sample x y

structure Patch where
  image : Texture
  leftOffset : Int
  topOffset : Int
  deriving Inhabited

def Patch.withDosResource (p : Patch) (resource : DosHeap.Resource) : Patch :=
  { p with image := { p.image with
    resource := some resource
    columnSources := p.image.columnSources.map (Option.map fun s => { s with resource := some resource }) } }

/-- Bind a decoded patch to its complete cached lump. Pass the current memory
snapshot through Art.dosMemory when drawing; offsets remain lump-relative. -/
def Patch.atDosAddress (patch : Patch) (address : UInt32) : Patch :=
  { patch with image := { patch.image with
    columnSources := patch.image.columnSources.map (Option.map fun s => { s with address := some address }) } }

/-- Bind only packed composite columns; single-patch columns have distinct WAD
allocations and must retain their separate bindings. -/
def Texture.withDosComposite (texture : Texture) (address : UInt32) : Texture :=
  { texture with columnSources := texture.columnSources.map (Option.map fun s =>
      if s.patch then s else { s with address := some address }) }

private def dimensions (width height : Nat) : Parse Unit :=
  require (width > 0 && height > 0 && width ≤ 2048 && height ≤ 2048)
    "image dimensions must be in 1..2048"

/-- Decode vanilla column posts. Palette index 255 is opaque; only a post's topdelta 255 terminates. -/
def Patch.decode (b : ByteArray) : Parse Patch := do
  let width ← u16 b 0
  let height ← u16 b 2
  dimensions width height
  let left ← i16 b 4
  let top ← i16 b 6
  checkRange b 8 (width * 4)
  let mut image := Texture.empty width height
  let mut columns := #[]
  let mut sources := #[]
  for x in [:width] do
    let mut posts := #[]
    let mut pos ← u32 b (8 + x * 4)
    require (pos ≥ 8 + width * 4) "patch column overlaps header"
    sources := sources.push (some (⟨b,pos+3,true,none,none⟩ : ColumnSource))
    let mut terminated := false
    -- Every nonterminal post advances at least four bytes.
    for _ in [:b.size / 4 + 1] do
      checkRange b pos 1
      let y := b[pos]!.toNat
      if y == 255 then
        terminated := true
        break
      checkRange b pos 3
      let count := b[pos + 1]!.toNat
      checkRange b pos (count + 4)
      posts := posts.push (y,count)
      require (y + count ≤ height) "patch post exceeds image height (extended tall patches unsupported)"
      for j in [:count] do
        let i := (y + j) * width + x
        image := { image with pixels := image.pixels.set! i b[pos+3+j]!, coverage := image.coverage.set! i 1 }
      pos := pos + count + 4
    require terminated "patch column has no terminator"
    columns := columns.push posts
  return ⟨{ image with posts := columns, columnSources := sources }, left, top⟩

structure PatchPlacement where
  x : Int
  y : Int
  patch : Nat
  deriving Inhabited

structure TextureDef where
  name : String
  width : Nat
  height : Nat
  patches : Array PatchPlacement
  deriving Inhabited

def decodePnames (b : ByteArray) : Parse (Array String) := do
  let count ← u32 b 0
  checkRange b 4 (count * 8)
  let mut result := #[]
  for i in [:count] do result := result.push (← name b (4 + i*8) 8)
  return result

def decodeTextureDefs (b : ByteArray) (patchCount : Nat) : Parse (Array TextureDef) := do
  let count ← u32 b 0
  checkRange b 4 (count * 4)
  let mut result := #[]
  for i in [:count] do
    let offset ← u32 b (4 + i*4)
    require (offset ≥ 4 + count*4) "texture definition overlaps directory"
    checkRange b offset 22
    let label ← name b offset 8
    let width ← u16 b (offset+12)
    let height ← u16 b (offset+14)
    dimensions width height
    let n ← u16 b (offset+20)
    require (n > 0 && n < 32768) s!"texture {label}: invalid patch count"
    checkRange b (offset+22) (n*10)
    let mut patches := #[]
    for j in [:n] do
      let p := offset + 22 + j*10
      let index ← u16 b (p+4)
      require (index < patchCount) s!"texture {label}: bad PNAMES index {index}"
      patches := patches.push ⟨← i16 b p, ← i16 b (p+2), index⟩
    result := result.push ⟨label, width, height, patches⟩
  return result

structure Art where
  palettes : ByteArray
  colormaps : ByteArray
  lumps : Array Lump
  pnames : Array String
  definitions : Std.HashMap String TextureDef
  textureNames : Array String := #[]
  /-- Optional independently maintained DOS address space. Ordinary rendering
  keeps bounded source buffers until its allocation lifecycle is modeled. -/
  dosMemory : Option DosMemory.Memory := none

def lumpBytes (lumps : Array Lump) (label : String) : Parse ByteArray := do
  let some i := findLump lumps label | throw s!"missing resource {label}"
  return lumps[i]!.bytes

def Art.load (lumps : Array Lump) : Parse Art := do
  let palettes ← lumpBytes lumps "PLAYPAL"
  require (palettes.size ≥ 768 && palettes.size % 768 == 0) "PLAYPAL: expected whole 768-byte palettes"
  let colormaps ← lumpBytes lumps "COLORMAP"
  require (colormaps.size ≥ 32*256 && colormaps.size % 256 == 0) "COLORMAP: expected at least 32 whole 256-byte maps"
  let pnames ← (decodePnames (← lumpBytes lumps "PNAMES")).mapError ("PNAMES: " ++ ·)
  let mut definitions := {}
  let mut textureNames := #[]
  for label in #["TEXTURE1", "TEXTURE2"] do
    if label == "TEXTURE2" && (findLump lumps label).isNone then continue
    let defs ← (decodeTextureDefs (← lumpBytes lumps label) pnames.size).mapError (s!"{label}: " ++ ·)
    -- Vanilla searches TEXTURE1 followed by TEXTURE2 from the beginning.
    for d in defs do
      textureNames := textureNames.push d.name
      if !definitions.contains d.name then definitions := definitions.insert d.name d
  return ⟨palettes, colormaps, lumps, pnames, definitions, textureNames, none⟩

def Art.mapIndex (art : Art) (index : UInt8) (lightMap : Nat := 0) : UInt8 :=
  art.colormaps[lightMap * 256 + index.toNat]!

/-- Convert an already-lit palette index; fuzz must not apply a colormap twice. -/
def Art.paletteColor (art : Art) (index : UInt8) (palette : Nat := 0) : Color :=
  let offset := (min (art.palettes.size / 768 - 1) palette) * 768 + index.toNat * 3
  ⟨art.palettes[offset]!, art.palettes[offset+1]!, art.palettes[offset+2]!⟩

def Art.color (art : Art) (index : UInt8) (lightMap : Nat := 0) (palette : Nat := 0) : Color :=
  art.paletteColor (art.mapIndex index lightMap) palette

def Art.patch (art : Art) (label : String) : Parse Patch := do
  let some i := findLump art.lumps label | throw s!"missing patch {label}"
  let p ← (Patch.decode art.lumps[i]!.bytes).mapError (s!"patch {label}: " ++ ·)
  return p.withDosResource (.lump i)

def Art.texture (art : Art) (label : String)
    (cache : Std.HashMap String Patch := {}) : Parse (Texture × Std.HashMap String Patch) := do
  let some d := art.definitions[label.toUpper]? | throw s!"missing texture {label}"
  let mut result := Texture.empty d.width d.height
  let mut cache := cache
  let mut sources : Array (Array (Patch × Nat)) := Array.replicate d.width #[]
  for placement in d.patches do
    let patchName := art.pnames[placement.patch]!
    let patch ← match cache[patchName]? with
      | some p => pure p
      | none => art.patch patchName
    cache := cache.insert patchName patch
    for x in [:patch.image.width] do
      let destX := placement.x + Int.ofNat x
      if destX ≥ 0 && destX < Int.ofNat d.width then
        sources := sources.set! destX.toNat (sources[destX.toNat]!.push (patch,x))
    -- R_DrawColumnInCache clips negative destinations by shortening the copy,
    -- but deliberately does not advance its source pointer (TEKWALL1).
    for x in [:patch.image.width] do
      let destX := placement.x + Int.ofNat x
      if destX < 0 || destX ≥ Int.ofNat d.width then continue
      let some source := (patch.image.columnSources[x]?).getD none | continue
      let bytes := source.bytes
      let mut offset := source.offset
      for (top,count) in patch.image.posts[x]! do
        let position := placement.y + Int.ofNat top
        let start := max 0 position
        let length := min (Int.ofNat count + min 0 position) (Int.ofNat d.height - start)
        for j in [:length.toNat] do
          let dest := (start.toNat+j)*d.width+destX.toNat
          result := { result with pixels := result.pixels.set! dest bytes[offset+j]!, coverage := result.coverage.set! dest 1 }
        offset := offset + count + 4
  -- R_GenerateLookup bypasses the composite for columns with one patch.
  -- That fast path ignores the placement's Y origin (SKY1 uses -8 in DOOM1).
  let mut posts := Array.replicate d.width (#[] : Array (Nat × Nat))
  let mut columnSources := Array.replicate d.width none
  for x in [:d.width] do
    if sources[x]!.size == 1 then
      let (patch,u) := sources[x]![0]!
      posts := posts.set! x (patch.image.posts[u]?.getD #[])
      columnSources := columnSources.set! x ((patch.image.columnSources[u]?).getD none)
      for y in [:d.height] do
        let dest := y*d.width+x
        let index := if y < patch.image.height then patch.image.sample (Int.ofNat u) (Int.ofNat y) else none
        result := { result with pixels := result.pixels.set! dest (index.getD 0), coverage := result.coverage.set! dest (if index.isSome then 1 else 0) }
    else
      let mut runs := #[]
      let mut first : Option Nat := none
      for y in [:d.height+1] do
        if y < d.height && result.coverage[y*d.width+x]! != 0 then
          if first.isNone then first := some y
        else if let some start := first then
          runs := runs.push (start,y-start)
          first := none
      posts := posts.set! x runs
  -- R_GenerateLookup reserves height bytes only for columns covered by multiple
  -- patches, in X order. R_DrawColumn may sample the following cached column
  -- at a short texture's lower edge (e.g. STEP4); height wrapping is different.
  let mut composite := ByteArray.empty
  let mut offsets : Array (Option Nat) := Array.replicate d.width none
  for x in [:d.width] do
    if sources[x]!.size > 1 then
      offsets := offsets.set! x (some composite.size)
      for y in [:d.height] do
        composite := composite.push result.pixels[y*d.width+x]!
  for x in [:d.width] do
    if let some offset := offsets[x]! then
      columnSources := columnSources.set! x (some ⟨composite,offset,false,none,art.textureNames.findIdx? (· == d.name) |>.map DosHeap.Resource.composite⟩)
  return ({ result with posts, columnSources }, cache)

def Art.flat (art : Art) (label : String) : Parse Texture := do
  let b ← lumpBytes art.lumps label
  require (b.size == 4096) s!"flat {label}: expected 4096 bytes, got {b.size}"
  return ⟨64, 64, b, ⟨Array.replicate 4096 1⟩, #[], #[], (findLump art.lumps label).map DosHeap.Resource.lump⟩

def skyForMap (label : String) : String :=
  if label.startsWith "MAP" then
    let n := (label.drop 3).toString.toNat?.getD 1
    if n ≤ 11 then "SKY1" else if n ≤ 20 then "SKY2" else "SKY3"
  else if label.startsWith "E2" then "SKY2"
  else if label.startsWith "E3" then "SKY3"
  else if label.startsWith "E4" then "SKY4"
  else "SKY1"

structure SpriteView where
  patch : Patch
  flipped : Bool
  deriving Inhabited

/-- Eight view directions. A rotation-zero lump supplies all eight views. -/
def Art.sprite (art : Art) (frame : String) : Parse (Array SpriteView) := do
  let mut views : Array (Option SpriteView) := Array.replicate 8 none
  let mut namespaced : Std.HashMap Nat Bool := {}
  for lump in art.lumps do
    if lump.name == "S_START" || lump.name == "SS_START" then
      namespaced := namespaced.insert lump.archive true
  let mut archive := 0
  let mut inside := false
  for index in [:art.lumps.size] do
    let lump := art.lumps[index]!
    if lump.archive != archive then
      archive := lump.archive
      inside := false
    if lump.name == "S_START" || lump.name == "SS_START" then
      inside := true
      continue
    if lump.name == "S_END" || lump.name == "SS_END" then
      inside := false
      continue
    if namespaced.contains lump.archive && !inside then continue
    let chars := lump.name.toList.toArray
    if chars.size != 6 && chars.size != 8 then continue
    if (String.ofList (chars.toList.take 4)) != (frame.take 4).toString then continue
    for pair in [:if chars.size == 8 then 2 else 1] do
      let offset := 4 + pair * 2
      if chars[offset]! != frame.toList.toArray[4]! then continue
      let r := chars[offset+1]!.toNat
      -- Unnamespaced patches may also contain unrelated names such as BOSSBACK.
      if !namespaced.contains lump.archive && (r < 48 || r > 56) then continue
      require (r ≥ 48 && r ≤ 56) s!"sprite {lump.name}: invalid rotation"
      let patch ← (Patch.decode lump.bytes).mapError (s!"sprite {lump.name}: " ++ ·)
      let patch := patch.withDosResource (.lump index)
      let view : SpriteView := ⟨patch, pair == 1⟩
      if r == 48 then views := Array.replicate 8 (some view)
      else views := views.set! (r - 49) (some view)
  require (views.all Option.isSome) s!"sprite {frame}: missing view directions"
  return views.map (·.getD default)

structure SurfaceCycle where
  wall : Bool
  base : Nat
  names : Array String
  frames : Array Texture

structure Assets where
  art : Art
  walls : Std.HashMap String Texture
  flats : Std.HashMap String Texture
  sky : Option Texture
  sprites : Std.HashMap String (Array SpriteView) := {}
  weapons : Std.HashMap String Patch := {}
  status : Std.HashMap String Patch := {}
  hudFont : Std.HashMap String Patch := {}
  surfaceCycles : Array SurfaceCycle := #[]

def Assets.load (lumps : Array Lump) (map : Map) (animated : Bool := false) (combat : Bool := false) : Parse Assets := do
  let art ← Art.load lumps
  let mut walls := {}
  let mut flats := {}
  let mut cache := {}
  for side in map.sides do
    for label in #[side.upper, side.middle, side.lower] do
      if label.startsWith "-" || walls.contains label then continue
      let (texture, next) ← art.texture label cache
      cache := next
      walls := walls.insert label texture
      if animated then
        if let some alternate := switchPartner label then
          if !walls.contains alternate then
            let (texture, next) ← art.texture alternate cache
            cache := next
            walls := walls.insert alternate texture
  let mut sky := none
  for sector in map.sectors do
    for label in #[sector.floorTexture, sector.ceilingTexture] do
      if label == "F_SKY1" then
        if sky.isNone then
          let (texture, next) ← art.texture (skyForMap map.name) cache
          cache := next
          sky := some texture
      else if !flats.contains label then
        flats := flats.insert label (← art.flat label)
  let mut sprites := {}
  for thing in map.things do
    if !thing.active then continue
    if let some defn := thingDef thing.kind then
      let mut poses := if animated then thingPoses thing.kind else #[⟨defn.frame, defn.fullbright, 0⟩]
      if combat then
        if let some spec := enemySpec thing.kind then
          poses := poses.push ⟨"POL5A", false, 0⟩
          poses := poses ++ deathPoses thing.kind
          if thing.kind == 3001 then
            poses := poses ++ ImpData.frames.map (fun f =>
              ⟨f.sprite ++ String.singleton (Char.ofNat (65+f.frame%32768)), f.frame ≥ 32768, f.tics.toInt.toNat⟩)
          for mode in #[ActorMode.chase, .attack, .pain, .dying] do
            poses := poses ++ actorPoses thing.kind mode
          if spec.drop > 0 then poses := poses ++ thingPoses spec.drop
      for pose in poses do
        if !sprites.contains pose.frame then
          sprites := sprites.insert pose.frame (← art.sprite pose.frame)
  let mut weapons := {}
  if combat then
    for frame in ImpactData.frames do
      let pose := frame.sprite ++ String.singleton (Char.ofNat (65+frame.frame%32768))
      sprites := sprites.insert pose (← art.sprite pose)
    for label in #["PISGA0", "PISGB0", "PISGC0", "PISFA0"] do
      weapons := weapons.insert label (← art.patch label)
    -- Optional for diagnostic WADs without these weapons; the renderer reports
    -- missing artwork if a selected weapon actually needs it.
    for label in #["PUNGA0","PUNGB0","PUNGC0","PUNGD0","SHTGA0","SHTGB0","SHTGC0","SHTGD0","SHTFA0","SHTFB0"] do
      if (findLump lumps label).isSome then weapons := weapons.insert label (← art.patch label)
  let mut status := {}
  -- Tiny render fixtures may omit the entire UI; a present STBAR requires the
  -- complete single-player artwork. Individual missing patches are errors.
  if combat && (findLump lumps "STBAR").isSome then
    for label in Status.patchNames do status := status.insert label (← art.patch label)
    if (findLump lumps "STTMINUS").isSome then
      status := status.insert "STTMINUS" (← art.patch "STTMINUS")
    require (art.palettes.size ≥ 14*768) "PLAYPAL: status effects require 14 palettes"
  let mut hudFont := {}
  -- Fixtures may omit the font, but a present font must be complete.
  if combat && (findLump lumps "STCFN033").isSome then
    for code in [33:96] do
      let label := s!"STCFN0{code}"
      hudFont := hudFont.insert label (← art.patch label)
  let mut cycles := #[]
  let flatStart := ((findLump lumps "F_START").getD lumps.size) + 1
  let flatStop := (findLump lumps "F_END").getD flatStart
  let flatNames := (lumps.extract flatStart flatStop).map (·.name)
  for (isWall,first,last) in SurfaceAnimation.definitions do
    let names := if isWall then art.textureNames else flatNames
    let start := if isWall then names.findIdx? (· == first) else (findLump lumps first).map (· - flatStart)
    let some base := start | continue
    let stop := if isWall then names.findIdx? (· == last) else (findLump lumps last).map (· - flatStart)
    let some final := stop | throw s!"animation {first}: missing endpoint {last}"
    require (base < final && final < names.size) s!"animation {first}: invalid directory range"
    let labels := names.extract base (final+1)
    let mut frames := #[]
    for label in labels do
      if isWall then
        let (tex,next) ← art.texture label cache
        cache := next
        frames := frames.push tex
      else frames := frames.push (← art.flat label)
    cycles := cycles.push ⟨isWall,base,labels,frames⟩
  return ⟨art, walls, flats, sky, sprites, weapons, status, hudFont, cycles⟩

/-- Apply resource translation without changing the map's original texture IDs. -/
def Assets.atTick (assets : Assets) (ticks : Nat) : Assets := Id.run do
  let mut walls := assets.walls
  let mut flats := assets.flats
  for cycle in assets.surfaceCycles do
    for i in [:cycle.names.size] do
      let target := SurfaceAnimation.frame ticks cycle.base cycle.names.size (cycle.base+i) - cycle.base
      if cycle.wall then walls := walls.insert cycle.names[i]! cycle.frames[target]!
      else flats := flats.insert cycle.names[i]! cycle.frames[target]!
  return { assets with walls,flats }

/-- Standalone asset preview; transparent texels are shown in magenta. -/
def Art.texturePpm (art : Art) (texture : Texture) : ByteArray := Id.run do
  let mut bytes := s!"P6\n{texture.width} {texture.height}\n255\n".toUTF8
  for i in [:texture.width * texture.height] do
    let c := if texture.coverage[i]! == 0 then (⟨255, 0, 255⟩ : Color) else art.color texture.pixels[i]!
    bytes := bytes.push c.r |>.push c.g |>.push c.b
  return bytes

end Doom
