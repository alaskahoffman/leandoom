import Doom.Combat
import Doom.StatusBar
import Doom.Hud

namespace Doom

private def overlay (pixels : IndexedFrame) (art : Art) (patch : Patch)
    (colormap : Option Nat) (position : Weapon.Sprite) : IndexedFrame := Id.run do
  let mut pixels := pixels
  -- R_DrawPSprite retains the half-unit texture midpoint until post projection.
  let texturemid := 6586368 - position.y.raw + (Fixed.ofInt patch.topOffset).raw
  for x in [:patch.image.width] do
    let sx := (position.x.raw >>> 16).toInt - patch.leftOffset + Int.ofNat x
    if sx < 0 || sx ≥ Int.ofNat frameWidth then continue
    pixels := drawPatchColumn pixels art patch.image sx.toNat x 65536 texturemid 65536 (-1) pixels.viewHeight colormap
  return pixels

/-- A presentation owns the indexed screen independently of game state. Vanilla
leaves unpainted pixels intact, including narrow gaps exposed by BSP rounding. -/
def Simulation.drawIndexedFrame (s : Simulation) (assets : Assets) (camera : Option Camera := none)
    (phase : Fuzz.Phase := 0) (previous : Option IndexedFrame := none) : Except String IndexedFrame := do
  -- Inspection flight is an independent camera, without player view effects.
  let selected := if camera.isSome then 0 else s.inventory.pickupState.fixedColormap
  if selected != 0 && selected != 1 && selected != 32 then
    throw "render: unsupported player fixed colormap"
  let fixed := selected.toInt.toNat
  if assets.art.colormaps.size < (fixed + 1) * 256 then
    throw s!"COLORMAP: missing player effect row {fixed}"
  let mut poses := {}
  let mut map := s.map
  for i in [:s.spawnStates.size] do
    let some spawn := s.spawnStates[i]! | continue
    let thing := map.things[i]!
    if let some pose := thingSpawnPose thing.kind s.ticks spawn.tics then
      poses := poses.insert i pose
    else if thing.kind == 23 then
      -- This decoration's state chain terminates rather than looping.
      map := { map with things := map.things.set! i { thing with flags := thing.flags &&& 65533 } }
  for actor in s.actors do
    -- A living barrel keeps P_SpawnMapThing's randomized initial countdown.
    -- Its death states still take over immediately when it explodes.
    if !s.gibbed.contains actor.thing && !(actor.kind == 2035 && actor.death.isNone) then
      poses := poses.insert actor.thing actor.pose
  let mut positions := {}
  let mut angles := {}
  let mut sectorLinks := #[]
  if s.player.scene.isSome then
    let scene ← s.player.syncScene s.map
    sectorLinks := scene.sectorLinks.map (fun ids => (ids.filter (· > 0)).map (· - 1))
    for actor in s.actors do
      if let some brain := actor.imp then
        angles := angles.insert actor.thing brain.angle
      -- Thrust and corpse motion also move barrels and actors without an AI
      -- brain. Their integer THINGS proxies are not render coordinates.
      let body := scene.things[actor.thing+1]!
      positions := positions.insert actor.thing (body.x,body.y,body.z)
    for index in s.dropped do
      let body := scene.things[index+1]!
      positions := positions.insert index (body.x,body.y,body.z)
  for p in s.projectiles do
    if p.removed then continue
    let some frame := ImpData.frames.find? (·.id == p.frame) | throw "render: missing projectile state"
    let index := map.things.size
    -- Render-only proxy: gameplay missiles have no BLOCKMAP link (MF_NOBLOCKMAP).
    map := { map with things := map.things.push ⟨⟨p.motion.x.raw.toInt/65536,p.motion.y.raw.toInt/65536⟩,0,3001,7⟩ }
    poses := poses.insert index ⟨frame.sprite ++ String.singleton (Char.ofNat (65+frame.frame%32768)), true, frame.tics.toInt.toNat⟩
    positions := positions.insert index (p.motion.x,p.motion.y,p.motion.z)
  let statusOn := s.combatEnabled && camera.isNone && assets.status.contains "STBAR"
  for p in s.impacts do
    let some frame := ImpactData.frames.find? (·.id == p.frame) | throw "render: missing impact state"
    let index := map.things.size
    -- Nonblocking render proxy, with exact fixed-point position and state light.
    map := { map with things := map.things.push ⟨⟨0,0⟩,0,3001,7⟩ }
    poses := poses.insert index ⟨frame.sprite ++ String.singleton (Char.ofNat (65+frame.frame%32768)), frame.frame ≥ 32768, frame.tics.toInt.toNat⟩
    positions := positions.insert index (p.motion.x,p.motion.y,p.motion.z)
  let extra := if camera.isSome then 0 else s.weapon.extraLight.toInt
  let mut frame := renderFrame map (camera.getD s.player.camera) (some assets) s.ticks poses fixed phase (if statusOn then 168 else 200) positions extra angles sectorLinks previous
  if let some error := frame.dosError then throw error
  if !s.combatEnabled || camera.isSome then
    return { frame with rgb := Status.toRgb assets.art frame.indices 0 }
  let sector ← s.map.sectorAt s.player.body.x s.player.body.y
  let ordinary := RenderLighting.scaleMap (RenderLighting.level s.map.sectors[sector]!.light extra) 47
  let weaponMap := (RenderLighting.weapon fixed ordinary false s.inventory.pickupState.powers[2])
  let flashMap := (RenderLighting.weapon fixed ordinary true s.inventory.pickupState.powers[2])
  if let some label := Weapon.label s.weapon.weapon then
    let some patch := assets.weapons[label]? | throw s!"weapon: missing {label}"
    frame := overlay frame assets.art patch weaponMap s.weapon.weapon
  if let some label := Weapon.label s.weapon.flash then
    let some patch := assets.weapons[label]? | throw s!"weapon: missing {label}"
    frame := overlay frame assets.art patch flashMap s.weapon.flash
  if let some error := frame.dosError then throw error
  let mut indices := frame.indices
  if statusOn then
    let (drawn,widgets) := Status.drawWithHistory indices assets.status s.inventory.toPickup s.statusFace
      (previous.bind (·.statusWidgets))
    indices := drawn
    frame := { frame with statusWidgets := some widgets }
  if s.hudMessageTicks > 0 then indices := Hud.draw indices assets.hudFont s.hudMessage
  return { frame with indices, rgb := Status.toRgb assets.art indices (if statusOn then Status.palette s.inventory.toPickup else 0) }

/-- RGB convenience for a fresh screen. Continuous presenters carry the result
of drawIndexedFrame instead, so unwritten pixels survive between frames. -/
def Simulation.drawFrame (s : Simulation) (assets : Assets) (camera : Option Camera := none)
    (phase : Fuzz.Phase := 0) : Except String (ByteArray × Fuzz.Phase) := do
  let frame ← s.drawIndexedFrame assets camera phase
  return (frame.rgb,frame.phase)

/-- Single-frame export starts at fuzz phase zero; the interactive renderer owns
its phase across presentations, independently of simulation tics and restarts. -/
def Simulation.frame (s : Simulation) (assets : Assets) (camera : Option Camera := none) : Except String ByteArray :=
  (·.1) <$> s.drawFrame assets camera

end Doom
