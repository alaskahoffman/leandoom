import Doom.Map
import Doom.Actors
import Doom.Status
import Std.Data.HashMap

namespace Doom
open Binary

structure Color where
  r : UInt8
  g : UInt8
  b : UInt8
  deriving Inhabited, BEq, Repr

structure Texture where
  width : Nat
  height : Nat
  pixels : ByteArray
  coverage : ByteArray
  deriving Inhabited

def Texture.empty (width height : Nat) : Texture :=
  ⟨width, height, ⟨Array.replicate (width * height) 0⟩, ⟨Array.replicate (width * height) 0⟩⟩

def Texture.sample (t : Texture) (x y : Int) : Option UInt8 := do
  if t.width == 0 || t.height == 0 then none else do
    let i := (y % Int.ofNat t.height).toNat * t.width + (x % Int.ofNat t.width).toNat
    if t.coverage[i]! == 0 then none else some t.pixels[i]!

structure Patch where
  image : Texture
  leftOffset : Int
  topOffset : Int
  deriving Inhabited

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
  for x in [:width] do
    let mut pos ← u32 b (8 + x * 4)
    require (pos ≥ 8 + width * 4) "patch column overlaps header"
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
      require (y + count ≤ height) "patch post exceeds image height (extended tall patches unsupported)"
      for j in [:count] do
        let i := (y + j) * width + x
        image := { image with pixels := image.pixels.set! i b[pos+3+j]!, coverage := image.coverage.set! i 1 }
      pos := pos + count + 4
    require terminated "patch column has no terminator"
  return ⟨image, left, top⟩

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
  for label in #["TEXTURE1", "TEXTURE2"] do
    if label == "TEXTURE2" && (findLump lumps label).isNone then continue
    let defs ← (decodeTextureDefs (← lumpBytes lumps label) pnames.size).mapError (s!"{label}: " ++ ·)
    -- Vanilla searches TEXTURE1 followed by TEXTURE2 from the beginning.
    for d in defs do
      if !definitions.contains d.name then definitions := definitions.insert d.name d
  return ⟨palettes, colormaps, lumps, pnames, definitions⟩

def Art.mapIndex (art : Art) (index : UInt8) (lightMap : Nat := 0) : UInt8 :=
  art.colormaps[lightMap * 256 + index.toNat]!

/-- Convert an already-lit palette index; fuzz must not apply a colormap twice. -/
def Art.paletteColor (art : Art) (index : UInt8) (palette : Nat := 0) : Color :=
  let offset := (min (art.palettes.size / 768 - 1) palette) * 768 + index.toNat * 3
  ⟨art.palettes[offset]!, art.palettes[offset+1]!, art.palettes[offset+2]!⟩

def Art.color (art : Art) (index : UInt8) (lightMap : Nat := 0) (palette : Nat := 0) : Color :=
  art.paletteColor (art.mapIndex index lightMap) palette

def Art.patch (art : Art) (label : String) : Parse Patch := do
  (Patch.decode (← lumpBytes art.lumps label)).mapError (s!"patch {label}: " ++ ·)

def Art.texture (art : Art) (label : String)
    (cache : Std.HashMap String Patch := {}) : Parse (Texture × Std.HashMap String Patch) := do
  let some d := art.definitions[label.toUpper]? | throw s!"missing texture {label}"
  let mut result := Texture.empty d.width d.height
  let mut cache := cache
  for placement in d.patches do
    let patchName := art.pnames[placement.patch]!
    let patch ← match cache[patchName]? with
      | some p => pure p
      | none => art.patch patchName
    cache := cache.insert patchName patch
    -- Texture placement origins replace (not add to) a patch's sprite offsets.
    for y in [:patch.image.height] do
      let destY := placement.y + Int.ofNat y
      if destY < 0 || destY ≥ Int.ofNat d.height then continue
      for x in [:patch.image.width] do
        let destX := placement.x + Int.ofNat x
        if destX < 0 || destX ≥ Int.ofNat d.width then continue
        let source := y * patch.image.width + x
        if patch.image.coverage[source]! == 0 then continue
        let dest := destY.toNat * d.width + destX.toNat
        let pixels := result.pixels.set! dest patch.image.pixels[source]!
        let coverage := result.coverage.set! dest 1
        result := { result with pixels, coverage }
  return (result, cache)

def Art.flat (art : Art) (label : String) : Parse Texture := do
  let b ← lumpBytes art.lumps label
  require (b.size == 4096) s!"flat {label}: expected 4096 bytes, got {b.size}"
  return ⟨64, 64, b, ⟨Array.replicate 4096 1⟩⟩

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
  for lump in art.lumps do
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
      let view : SpriteView := ⟨patch, pair == 1⟩
      if r == 48 then views := Array.replicate 8 (some view)
      else views := views.set! (r - 49) (some view)
  require (views.all Option.isSome) s!"sprite {frame}: missing view directions"
  return views.map (·.getD default)

structure Assets where
  art : Art
  walls : Std.HashMap String Texture
  flats : Std.HashMap String Texture
  sky : Option Texture
  sprites : Std.HashMap String (Array SpriteView) := {}
  weapons : Std.HashMap String Patch := {}
  status : Std.HashMap String Patch := {}

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
  return ⟨art, walls, flats, sky, sprites, weapons, status⟩

/-- Standalone asset preview; transparent texels are shown in magenta. -/
def Art.texturePpm (art : Art) (texture : Texture) : ByteArray := Id.run do
  let mut bytes := s!"P6\n{texture.width} {texture.height}\n255\n".toUTF8
  for i in [:texture.width * texture.height] do
    let c := if texture.coverage[i]! == 0 then (⟨255, 0, 255⟩ : Color) else art.color texture.pixels[i]!
    bytes := bytes.push c.r |>.push c.g |>.push c.b
  return bytes

end Doom
