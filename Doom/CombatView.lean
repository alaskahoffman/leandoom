import Doom.Combat
import Doom.StatusBar

namespace Doom

private def overlay (pixels : IndexedFrame) (art : Art) (patch : Patch)
    (colormap : Option Nat) (position : Weapon.Sprite) : IndexedFrame := Id.run do
  let mut pixels := pixels
  -- Original posts draw columns left-to-right, top-to-bottom, sharing fuzzpos.
  for x in [:patch.image.width] do
    let sx := (position.x.raw.toInt >>> 16) - patch.leftOffset + Int.ofNat x
    if sx < 0 || sx ≥ Int.ofNat frameWidth then continue
    let mut run : Option Nat := none
    let mut stop := 0
    for y in [:patch.image.height] do
      let sy := ((position.y.raw.toInt >>> 16)-Int.ofNat ((200-pixels.viewHeight)/2))-patch.topOffset + Int.ofNat y
      if sy < 0 then continue
      if sy ≥ Int.ofNat pixels.viewHeight then break
      stop := sy.toNat + 1
      if let some index := patch.image.sample x y then
        if let some map := colormap then
          pixels := pixels.putIndex art sx.toNat sy.toNat (art.mapIndex index map)
        else if run.isNone then run := some sy.toNat
      else if let some start := run then
        pixels := pixels.fuzzPost art sx.toNat start sy.toNat
        run := none
    if let some start := run then pixels := pixels.fuzzPost art sx.toNat start stop
  return pixels

def Simulation.drawFrame (s : Simulation) (assets : Assets) (camera : Option Camera := none)
    (phase : Fuzz.Phase := 0) : Except String (ByteArray × Fuzz.Phase) := do
  -- Inspection flight is an independent camera, without player view effects.
  let selected := if camera.isSome then 0 else s.inventory.pickupState.fixedColormap
  if selected != 0 && selected != 1 && selected != 32 then
    throw "render: unsupported player fixed colormap"
  let fixed := selected.toInt.toNat
  if assets.art.colormaps.size < (fixed + 1) * 256 then
    throw s!"COLORMAP: missing player effect row {fixed}"
  let mut poses := {}
  for actor in s.actors do
    if !s.gibbed.contains actor.thing then poses := poses.insert actor.thing actor.pose
  let mut map := s.map
  let mut positions := {}
  if let some scene := s.player.scene then
    for actor in s.actors do
      if actor.imp.isSome then
        let body := scene.things[actor.thing+1]!
        positions := positions.insert actor.thing (body.x,body.y,body.z)
  for p in s.projectiles do
    if p.removed then continue
    let some frame := ImpData.frames.find? (·.id == p.frame) | throw "render: missing projectile state"
    let index := map.things.size
    -- Render-only proxy: gameplay missiles have no BLOCKMAP link (MF_NOBLOCKMAP).
    map := { map with things := map.things.push ⟨⟨p.motion.x.raw.toInt/65536,p.motion.y.raw.toInt/65536⟩,0,3001,7⟩ }
    poses := poses.insert index ⟨frame.sprite ++ String.singleton (Char.ofNat (65+frame.frame%32768)), true, frame.tics.toInt.toNat⟩
    positions := positions.insert index (p.motion.x,p.motion.y,p.motion.z)
  let statusOn := s.combatEnabled && camera.isNone && assets.status.contains "STBAR"
  let mut frame := renderFrame map (camera.getD s.player.camera) (some assets) s.ticks poses fixed phase (if statusOn then 168 else 200) positions
  if !s.combatEnabled || camera.isSome then return (frame.rgb, frame.phase)
  if s.inventory.health > 0 then
    let weaponMap := (RenderLighting.weapon fixed 0 false s.inventory.pickupState.powers[2])
    let flashMap := (RenderLighting.weapon fixed 0 true s.inventory.pickupState.powers[2])
    if let some label := Weapon.label s.weapon.weapon then
      let some patch := assets.weapons[label]? | throw s!"weapon: missing {label}"
      frame := overlay frame assets.art patch weaponMap s.weapon.weapon
    if let some label := Weapon.label s.weapon.flash then
      let some patch := assets.weapons[label]? | throw s!"weapon: missing {label}"
      frame := overlay frame assets.art patch flashMap s.weapon.flash
  if statusOn then
    let indices := Status.draw frame.indices assets.status s.inventory.toPickup s.statusFace
    return (Status.toRgb assets.art indices (Status.palette s.inventory.toPickup), frame.phase)
  return (frame.rgb, frame.phase)

/-- Single-frame export starts at fuzz phase zero; the interactive renderer owns
its phase across presentations, independently of simulation tics and restarts. -/
def Simulation.frame (s : Simulation) (assets : Assets) (camera : Option Camera := none) : Except String ByteArray :=
  (·.1) <$> s.drawFrame assets camera

end Doom
