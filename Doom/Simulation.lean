import Doom.Audio.Sfx
import Doom.Player
import Doom.Inventory
import Doom.SectorLights
import Doom.VerticalDoor
import Doom.SectorChange
import Doom.Use
import Doom.UseButton
import Doom.Scrolling
import Doom.LevelSpecials
import Doom.Hitscan
import Doom.Projectile
import Doom.Weapon
import Doom.MapSpawn
import Doom.Impact

namespace Doom

structure Door where
  sector : Nat
  thinkerSerial : Nat := 0
  state : VerticalDoor.State := {}
  deriving Inhabited

structure Button where
  side : Nat
  slot : Nat
  texture : String
  remaining : Nat := 35
  deriving Inhabited

structure Simulation where
  /-- Guest memory is present only in the pinned DOS comparison profile. -/
  dosHeap : Option DosHeap.Heap := none
  dosDeferred : Array (Nat × String) := #[]
  map : Map
  original : Map
  audio : Option Audio.Sfx.State := none
  audioEvents : Array Audio.Sfx.Event := #[]
  combatEnabled : Bool := false
  actors : Array Actor := #[]
  /-- Spawn-time metadata in THINGS order, retained for actor adapters. -/
  spawnStates : Array (Option MapSpawn.State) := #[]
  projectiles : Array Projectile.Body := #[]
  impacts : Array Impact.Body := #[]
  projectileEvents : Array (Nat × Projectile.Event) := #[]
  impEvents : Array (Nat × Imp.Event) := #[]
  soundTargets : Array (Option Nat) := #[]
  playerDeath : Option Death.Body := none
  deathStats : Vector Death.Stats 4 := Vector.replicate 4 {}
  deathEvents : Array (Nat × Death.Event) := #[]
  blastEvents : Array (Nat × Nat × Int32) := #[]
  rng : DoomRandom := {}
  weapon : Weapon.State := {}
  weaponAge : Nat := 100
  refire : Bool := false
  attackDown : Bool := true -- G_PlayerReborn; updated at the weapon-ready stage.
  shotEvents : Array (Nat × Collision.ShotEvent) := #[]
  shotSlope : Fixed := ⟨0⟩
  lastFire : Option Fire.Sample := none
  shots : Nat := 0
  lastShot : Nat := 0
  kills : Nat := 0
  statusFace : Status.Face := {}
  attacker : Option Nat := none
  restartHeld : Bool := false
  dropped : Array Nat := #[]
  gibbed : Array Nat := #[]
  crushedDrops : Array Nat := #[]
  player : Player
  physicsError : Option String := none
  inventory : Inventory := {}
  /-- Allocation order shared by dynamic doors and missiles. -/
  nextDynamicSerial : Nat := 1
  doors : Array Door := #[]
  doorSounds : Array (Nat × VerticalDoor.Sound) := #[]
  buttons : Array Button := #[]
  lights : Array SectorLights.Thinker := #[]
  scrollers : Array Nat := #[]
  movers : Array FloorMover.Thinker := #[]
  moverSounds : Array (Nat × FloorMover.Sound) := #[]
  secrets : Int32 := 0
  totalSecrets : Int32 := 0
  switchEpisode : Nat := 1
  exitRequested : Bool := false
  exitSwitchSound : Bool := false
  ticks : Nat := 0
  useHeld : Bool := false
  collected : Array Nat := #[]
  message : String := "Space: use doors and switches"
  messageTicks : Nat := 175
  hudMessage : String := ""
  hudMessageTicks : Nat := 0

def Simulation.dosAction (s : Simulation) (action : DosHeap.Action Unit) : Simulation :=
  match s.dosHeap with
  | none => s
  | some heap => match action.run heap with
    | .ok (_,heap) => { s with dosHeap := some heap }
    | .error error => { s with physicsError := some error }

def Simulation.dosSpawn (s : Simulation) (key : String) (size : Nat) (tag : Int32 := 50) : Simulation :=
  s.dosAction do
    let address ← DosHeap.allocate size tag
    DosHeap.forget address size
    if (← get).objects.contains key then throw s!"DOS duplicate object {key}"
    modify fun h => { h with objects := h.objects.insert key address }

def Simulation.dosRemove (s : Simulation) (key : String) : Simulation :=
  s.dosAction do
    if (← get).objects.contains key then DosHeap.remove key

/-- P_RemoveThinker marks a node; P_RunThinkers frees it on its next visit. -/
def Simulation.dosDefer (s : Simulation) (serial : Nat) (key : String) : Simulation :=
  if s.dosHeap.isNone then s else { s with dosDeferred := s.dosDeferred.push (serial,key) }

def Simulation.spawn (map : Map) (combat : Bool := false) (switchEpisode : Nat := 1) : Except String Simulation := do
  let mut actors : Array Actor := #[]
  let mut rng : DoomRandom := {}
  let mut spawnStates := #[]
  for index in [:map.things.size] do
    let thing := map.things[index]!
    let (spawn,next) ← MapSpawn.thing thing rng
    rng := next
    spawnStates := spawnStates.push spawn
    if !combat then continue
    let some initial := spawn | continue
    if let some spec := enemySpec thing.kind then
      let mut imp : Option Imp.State := none
      if thing.kind == 3001 || thing.kind == 3004 then
        let degrees := if thing.angle >= 32768 then Int.ofNat thing.angle - 65536 else Int.ofNat thing.angle
        imp := some {
          id := index+1, kind := thing.kind, frame := initial.frame, lastlook := initial.lastlook, tics := initial.tics,
          angle := ⟨(Int32.ofInt (degrees.tdiv 45)).toUInt32 * 0x20000000⟩, ambush := thing.flags &&& 8 != 0 }
      actors := actors.push { thing := index, kind := thing.kind, health := spec.health, imp }
  let original := map
  let (map, lights, lightingRng) := SectorLights.spawnMap map rng
  return {
    map, original, combatEnabled := combat, actors, spawnStates, lights, rng := lightingRng, switchEpisode,
    weapon := (Weapon.setup {}).state,
    soundTargets := Array.replicate map.sectors.size none
    totalSecrets := LevelSpecials.totalSecrets (original.sectors.map (·.special))
    scrollers := ← Scrolling.spawn (map.lines.map (·.special)), player := ← Player.spawn map }

def Simulation.restart (s : Simulation) : Simulation :=
  let next := (Simulation.spawn s.original s.combatEnabled s.switchEpisode).toOption.getD s
  { next with
    statusFace := s.statusFace.start next.inventory.toPickup,
    audio := s.audio.map (fun a => { a with channels := Array.replicate 8 none }) }

def Simulation.soundPosition (s : Simulation) (origin : Audio.Sfx.Origin) : Option Audio.Sfx.Position := do
  match origin with
  | .actor 0 => return ⟨s.player.body.x,s.player.body.y⟩
  | .actor id =>
    if let some thing := s.player.scene.bind (fun scene => scene.things[id]?) then return ⟨thing.x,thing.y⟩
    let thing ← s.map.things[id-1]?
    return ⟨Fixed.ofInt thing.position.x,Fixed.ofInt thing.position.y⟩
  | .missile id =>
    let p ← s.projectiles[id]?
    return ⟨p.motion.x,p.motion.y⟩
  | .sector id =>
    let mut left := 32767; let mut right := -32768
    let mut bottom := 32767; let mut top := -32768
    let mut found := false
    for line in s.map.lines do
      if s.map.sides[line.front]!.sector != id && !(s.map.sides[line.back]?.any (·.sector == id)) then continue
      for index in #[line.v1,line.v2] do
        let p := s.map.vertices[index]!
        left := min left p.x; right := max right p.x
        bottom := min bottom p.y; top := max top p.y
        found := true
    unless found do failure
    let x := (Fixed.ofInt left + Fixed.ofInt right).raw
    let y := (Fixed.ofInt bottom + Fixed.ofInt top).raw
    return ⟨⟨Int32.ofInt (x.toInt.tdiv 2)⟩,⟨Int32.ofInt (y.toInt.tdiv 2)⟩⟩

def Simulation.soundListener (s : Simulation) : Audio.Sfx.Listener :=
  ⟨⟨s.player.body.x,s.player.body.y⟩,s.player.body.angle⟩

/-- Start logical sound effects at their emission site even without PCM output,
so audible M_Random pitch draws precede later status-face draws. -/
def Simulation.soundAt (s : Simulation) (name : String) (origin : Option Audio.Sfx.Origin)
    (position : Audio.Sfx.Position) : Simulation :=
  let event : Audio.Sfx.Event := ⟨name,origin,position⟩
  let s := { s with audioEvents := s.audioEvents.push event }
  match s.audio with
  | none =>
    let silent : Audio.Sfx.State := { bank := #[], map8 := s.map.name.endsWith "8" }
    match silent.prepare s.soundListener event s.rng with
    | .ok (some (_,_,rng)) => ({ s with rng }).dosAction do
      let _ ← DosHeap.named ("DP" ++ name.toUpper) 3
    | .ok none => s
    | .error e => { s with physicsError := some e }
  | some audio =>
    match audio.start s.soundListener event s.rng with
    | .ok (audio,rng) => { s with audio := some audio, rng }
    | .error e => { s with physicsError := some e }

def Simulation.stopSound (s : Simulation) (origin : Audio.Sfx.Origin) : Simulation :=
  { s with audio := s.audio.map (·.stop (some origin)) }

def Simulation.sound (s : Simulation) (name : String) (origin : Audio.Sfx.Origin := .actor 0) : Simulation :=
  s.soundAt name (some origin) ((s.soundPosition origin).getD ⟨s.player.body.x,s.player.body.y⟩)

private def Simulation.say (s : Simulation) (message : String) : Simulation :=
  { s with message, messageTicks := 105 }

private def setTexture (side : Sidedef) (slot : Nat) (label : String) : Sidedef :=
  match slot with
  | 0 => { side with upper := label }
  | 1 => { side with middle := label }
  | _ => { side with lower := label }

private def Simulation.updateButtons (s : Simulation) : Simulation := Id.run do
  let mut s := s
  let mut buttons := #[]
  for button in s.buttons do
    if button.remaining ≤ 1 then
      let side := setTexture s.map.sides[button.side]! button.slot button.texture
      s := { s with map := { s.map with sides := s.map.sides.set! button.side side } }
      s := s.sound "swtchn" (.sector side.sector)
    else buttons := buttons.push { button with remaining := button.remaining - 1 }
  return { s with buttons }

private def Simulation.flipSwitch (s : Simulation) (lineIndex : Nat) (repeatable : Bool) : Simulation := Id.run do
  let line := s.map.lines[lineIndex]!
  let some side := s.map.sides[line.front]? | return s
  let mut s := s
  if !repeatable then
    s := { s with map := { s.map with lines := s.map.lines.set! lineIndex { line with special := 0 } } }
  if s.buttons.any (fun b => b.side == line.front) then return s
  let textures := #[side.upper, side.middle, side.lower]
  for slot in [:3] do
    if let some alternate := switchPartner textures[slot]! then
      s := { s with map := { s.map with sides := s.map.sides.set! line.front (setTexture side slot alternate) } }
      s := s.sound "swtchn" (.sector side.sector)
      if repeatable then s := { s with buttons := s.buttons.push ⟨line.front, slot, textures[slot]!, 35⟩ }
      break
  return s

private def doorTop (map : Map) (sector : Nat) : Option Int := Id.run do
  let mut top : Option Int := none
  for line in map.lines do
    if line.flags / 4 % 2 == 0 then continue
    let some a := map.sides[line.front]? | continue
    let some b := map.sides[line.back]? | continue
    if a.sector == b.sector then continue
    let neighbor := if a.sector == sector then some b.sector else if b.sector == sector then some a.sector else none
    if let some index := neighbor then
      let height := map.sectors[index]!.ceiling - 4
      top := some (min (top.getD height) height)
  return top

private def manualDoor (special : Nat) : Bool :=
  #[1, 26, 27, 28, 31, 32, 33, 34, 117, 118].contains special

private def doorSwitch (special : Nat) : Bool :=
  #[29, 50, 103, 111, 112, 113, 42, 61, 63, 114, 115, 116, 99, 133, 134, 135, 136, 137].contains special

private def requiredKey (special : Nat) : Nat :=
  if #[26, 32, 99, 133].contains special then 1
  else if #[28, 33, 134, 135].contains special then 2
  else if #[27, 34, 136, 137].contains special then 3
  else 0

private def Simulation.activate (s : Simulation) (index : Nat) : Simulation := Id.run do
  let line := s.map.lines[index]!
  let special := line.special
  if special == 11 then
    let side := s.map.sides[line.front]!
    let result := LevelSpecials.exitSwitch (LevelSpecials.switchList s.switchEpisode)
      (⟨side.upper,side.middle,side.lower⟩ : LevelSpecials.Textures String) special true false
    let s := if result.switchSound then s.sound "swtchn" (.sector side.sector) else s
    let side := { side with upper := result.textures.top, middle := result.textures.middle, lower := result.textures.bottom }
    return { s with
      map := { s.map with
        sides := s.map.sides.set! line.front side
        lines := s.map.lines.set! index { line with special := result.special } }
      exitRequested := result.completed, exitSwitchSound := result.switchSound
      message := "Exit requested — intermission is not implemented yet", messageTicks := 105 }
  if !manualDoor special && !doorSwitch special then
    return s.say s!"Linedef special {special} is not implemented yet"
  let key := requiredKey special
  if (key == 1 && !s.inventory.blue) || (key == 2 && !s.inventory.red) || (key == 3 && !s.inventory.yellow) then
    return (s.sound "oof").say (if key == 1 then "Need a blue key" else if key == 2 then "Need a red key" else "Need a yellow key")
  let manual := manualDoor special
  let repeatable := #[1, 26, 27, 28, 117, 42, 61, 63, 114, 115, 116, 99, 134, 136].contains special
  let staysOpen := #[31, 32, 33, 34, 118, 103, 61, 112, 115, 99, 133, 134, 135, 136, 137].contains special
  let closeOnly := #[50, 42, 113, 116].contains special
  let speed := if special ≥ 99 && special != 103 then 8 else 2
  let mut targets := #[]
  if manual then
    if let some side := s.map.sides[line.back]? then targets := #[side.sector]
  else if line.tag != 0 then
    for i in [:s.map.sectors.size] do
      if s.map.sectors[i]!.tag == line.tag then targets := targets.push i
  let mut s := s
  let mut changed := false
  for sector in targets do
    if s.movers.any (·.sector == sector) then
      if manual then return { s with physicsError := some "manual door use on an active floor/platform is not ported" }
      continue
    if let some existing := s.doors.findIdx? (fun d => d.sector == sector) then
      if manual && repeatable then
        let d := s.doors[existing]!
        let direction := if d.state.direction < 0 then 1 else -1
        s := { s with doors := s.doors.set! existing { d with state := { d.state with direction } } }
        changed := true
      continue
    let some top := doorTop s.map sector | continue
    if top ≤ s.map.sectors[sector]!.floor then continue
    if !closeOnly && s.map.sectors[sector]!.ceiling ≥ top then continue
    let kind : VerticalDoor.Kind :=
      if closeOnly then (if speed == 8 then .blazeClose else .close)
      else if staysOpen then (if speed == 8 then .blazeOpen else .open)
      else (if speed == 8 then .blazeRaise else .normal)
    let state : VerticalDoor.State := {
      kind, top := Fixed.ofInt top, speed := Fixed.ofInt speed,
      direction := if closeOnly then -1 else 1 }
    let door : Door := { sector, state, thinkerSerial := s.nextDynamicSerial }
    if manual then
      s := s.sound (if closeOnly then (if speed == 8 then "bdcls" else "dorcls") else (if speed == 8 then "bdopn" else "doropn")) (.sector sector)
    s := s.dosSpawn s!"door:{sector}" 40 51
    s := { s with doors := s.doors.push door, nextDynamicSerial := s.nextDynamicSerial+1 }
    if !manual then s := s.sound (if closeOnly then (if speed == 8 then "bdcls" else "dorcls") else (if speed == 8 then "bdopn" else "doropn")) (.sector sector)
    changed := true
  if changed then
    if !manual then s := s.flipSwitch index repeatable
    else if !repeatable then
      s := { s with map := { s.map with lines := s.map.lines.set! index { line with special := 0 } } }
    return s.say "Door activated"
  return s.say "Door is already active or has no target"

/-- Nonplayer P_UseSpecialLine gates. A monster may reopen a closing type-1
door, but cannot make an opening/waiting door close. Door allocation still
shares the existing runtime manual-door adapter. -/
def Simulation.monsterUse (s : Simulation) (index : Nat) : Simulation × Bool := Id.run do
  let line := s.map.lines[index]!
  if line.flags &&& 32 != 0 || !#[1,32,33,34].contains line.special then return (s,false)
  if line.special != 1 then return (s,true) -- EV_VerticalDoor rejects nonplayer keys.
  let some side := s.map.sides[line.back]? | return (s,true)
  if let some i := s.doors.findIdx? (·.sector == side.sector) then
    let door := s.doors[i]!
    if door.state.direction == -1 then
      return ({ s with doors := s.doors.set! i { door with state := { door.state with direction := 1 } } },true)
    return (s,true)
  return (s.activate index,true)

/-- Original BLOCKMAP use trace, followed by the existing action adapter.
Door spawning and general P_UseSpecialLine dispatch still need faithful ports. -/
def Simulation.use (s : Simulation) : Simulation :=
  match do
    let scene ← s.player.syncScene s.map
    scene.useLines s.player.body.x s.player.body.y s.player.body.angle
  with
  | .error error => { s with physicsError := some error }
  | .ok result => match result.action with
    | .nothing => s.say "Nothing in reach"
    | .blocked => (s.sound "noway").say "Cannot use through this wall"
    | .special index back =>
      if back then s.say "Cannot use this wall" else s.activate index

/-- Reflect already-committed collision effects in rendering and UI state. -/
private def Simulation.pickups (s : Simulation) : Simulation := Id.run do
  let mut s := s
  let some scene := s.player.scene | return s
  for event in scene.pickupEvents do
    if !event.removed || event.item == 0 then continue
    let index := event.item - 1
    let some thing := s.map.things[index]? | continue
    s := { s with
      collected := s.collected.push index,
      map := { s.map with things := s.map.things.set! index { thing with flags := 0 } } }
    if let some sound := event.sound then
      s := s.sound (match sound with | .item => "itemup" | .weapon => "wpnup" | .power => "getpow")
    s := s.say (Pickup.messageText event.message)
    s := { s with hudMessage := Pickup.messageText event.message, hudMessageTicks := 140 }
  return s

/-- Non-crushing sector changes use original block bounds, traversal and disposal.
Actor health/death state is still supplied by the prototype combat adapter. -/
private def Simulation.clipSectorActors (s : Simulation) (sector : Nat) (heights : Plane.Heights)
    : Except String (Bool × Simulation) := do
  let sec := s.map.sectors[sector]!
  let sec := { sec with floor := heights.floor.raw.toInt / 65536, ceiling := heights.ceiling.raw.toInt / 65536 }
  let map := { s.map with sectors := s.map.sectors.set! sector sec }
  let mut scene ← s.player.syncScene map
  let some collector := scene.pickupPlayer | throw "sector clipping: missing player"
  scene := { scene with pickupPlayer := some { collector with state := s.inventory.toPickup } }
  let playerActor := scene.things[collector.actor]!
  let playerActor := { playerActor with health := Int32.ofNat s.inventory.health, shootable := s.inventory.health > 0 }
  scene := { scene with things := scene.things.set! collector.actor playerActor }
  for actor in s.actors do
    let id := actor.thing+1
    let thing := scene.things[id]!
    let thing := { thing with health := Int32.ofNat actor.health, shootable := thing.shootable && actor.health > 0 }
    scene := { scene with things := scene.things.set! id thing }
  for index in s.gibbed do
    let thing := scene.things[index+1]!
    let thing := { thing with gibbed := true, solid := false, height := ⟨0⟩, radius := ⟨0⟩, health := 0 }
    scene := { scene with things := scene.things.set! (index+1) thing }
  for index in s.dropped do
    let some thing := scene.things[index+1]? | throw "sector clipping: invalid dropped item"
    if let some item := thing.pickup then
      scene := { scene with things := scene.things.set! (index+1) { thing with pickup := some { item with dropped := true } } }
  let changed ← scene.changeSectorNoCrush (← Collision.mapSectorBlocks map sector) map.sectorAt (some collector.actor)
  scene := changed.scene
  let mut map := map
  let mut gibbed := s.gibbed
  let mut actors := s.actors
  let mut crushedDrops := s.crushedDrops
  for event in changed.events do
    match event with
    | .gib id =>
      if id != collector.actor then
        let index := id-1
        if !gibbed.contains index then gibbed := gibbed.push index
        -- PIT_ChangeSector also enters S_GIBS. Keep the actual corpse state
        -- synchronized with its zero-sized collision body and render proxy.
        if let some slot := actors.findIdx? (·.thing == index) then
          let actor := actors[slot]!
          if let some body := actor.death then
            let (body,_) ← Death.setState Death.frames body {} 895
            let body := { body with height := ⟨0⟩, flags := body.flags &&& ~~~(2 : UInt32) }
            actors := actors.set! slot { actor with death := some body }
        map := { map with things := map.things.set! index { map.things[index]! with kind := 24 } }
    | .remove id =>
      let index := id-1
      crushedDrops := crushedDrops.push index
      map := { map with things := map.things.set! index { map.things[index]! with flags := 0 } }
  let some collector := scene.pickupPlayer | throw "sector clipping: lost player"
  let inventory := Inventory.fromPickup collector.state
  let body := scene.things[collector.actor]!.motion s.player.body
  let player := { s.player with
    scene := some scene, mapActors := map.things, inventory,
    body, feet := body.z.toFloat }
  return (changed.blocked,{ s with map, player, inventory, actors, gibbed, crushedDrops })

/-- Original plane/door kernels with effectful height clipping. Tentative and
rollback queries retain pickup/disposal and actor-height effects. The surrounding
general thinker interleaving and combat state remain partial ports. -/
def Simulation.moveDoors (s : Simulation) (onlySector : Option Nat := none) : Simulation := Id.run do
  let player := { s.player with scene := s.player.scene.map (fun scene => { scene with pickupEvents := #[] }) }
  let mut s := { s with doorSounds := if onlySector.isNone then #[] else s.doorSounds, player }
  let mut doors := #[]
  for door in s.doors do
    if onlySector.any (· != door.sector) then
      doors := doors.push door
      continue
    let sec := s.map.sectors[door.sector]!
    let heights : Plane.Heights := ⟨Fixed.ofInt sec.floor, Fixed.ofInt sec.ceiling⟩
    let result := door.state.tick heights (.ok s : Except String Simulation) (fun heights _ state =>
      match state with
      | .error error => (true,.error error)
      | .ok current => match current.clipSectorActors door.sector heights with
        | .error error => (true,.error error)
        | .ok (blocked,next) => (blocked,.ok next))
    match result.state with
    | .error error => return { s with physicsError := some error }
    | .ok next => s := next
    for sound in result.sounds do
      s := { s with doorSounds := s.doorSounds.push (door.sector,sound) }
      s := s.sound (match sound with | .close => "dorcls" | .open => "doropn" | .blazeClose => "bdcls") (.sector door.sector)
    if !result.removed then doors := doors.push { door with state := result.door }
    else s := s.dosDefer door.thinkerSerial s!"door:{door.sector}"
  return ({ s with doors }).pickups

/-- E1M1 floor/platform thinkers run after player/actor movement. A thinker
spawned by a crossing can therefore move this tic. Full interleaving with doors,
actors and lights still awaits the general vanilla thinker scheduler. -/
def Simulation.moveFloors (s : Simulation) : Simulation := Id.run do
  if s.movers.isEmpty then return s
  let player := { s.player with scene := s.player.scene.map (fun scene => { scene with pickupEvents := #[] }) }
  let mut s := { s with player }
  let mut movers := #[]
  for mover in s.movers do
    let sector := s.map.sectors[mover.sector]!
    let heights : Plane.Heights := ⟨Fixed.ofInt sector.floor, Fixed.ofInt sector.ceiling⟩
    let result := mover.tick heights (Int32.ofNat (s.ticks-1)) (.ok s : Except String Simulation)
      (fun heights _ state => match state with
        | .error error => (true,.error error)
        | .ok current => match current.clipSectorActors mover.sector heights with
          | .error error => (true,.error error)
          | .ok (blocked,next) => (blocked,.ok next))
    match result.state with
    | .error error => return { s with physicsError := some error }
    | .ok next => s := next
    for event in result.events do
      if let .sound sound := event then s := { s with moverSounds := s.moverSounds.push (mover.sector,sound) }
    if !result.removed then movers := movers.push result.thinker
    else s := s.dosDefer 0 s!"mover:{mover.sector}"
  return ({ s with movers }).pickups

/-- Original secret check precedes XY/Z actor movement. P_MovePlayer/CalcHeight
alter momentum/view but not position, so the pre-movement body is the correct
input. Door/other thinker interleaving is still the surrounding adapter. -/
def Simulation.discoverSecret (s : Simulation) : Except String Simulation := do
  let index ← s.map.sectorAt s.player.body.x s.player.body.y
  let sector := s.map.sectors[index]!
  let (special,secrets) := LevelSpecials.secret sector.special s.player.body.z (Fixed.ofInt sector.floor) s.secrets
  return { s with secrets, map := { s.map with sectors := s.map.sectors.set! index { sector with special } } }

/-- The ordinary floor request consumed by combat after player preparation.
Keep the decision separate from applying damage: the latter may consume more RNG. -/
def Simulation.floorDamageRequest (s : Simulation) : Except String (Nat × DoomRandom) := do
  let index ← s.map.sectorAt s.player.body.x s.player.body.y
  let sector := s.map.sectors[index]!
  return LevelSpecials.floorDamage sector.special s.player.body.z
    (Fixed.ofInt sector.floor) (s.inventory.suit > 0) (s.ticks-1) s.rng

/-- Install the decision's RNG before invoking damage, including no-damage
random draws. Lookup failure retains the incoming state and records its error. -/
def Simulation.applyFloorEffect (s : Simulation) (damage : Simulation → Nat → Simulation) : Simulation :=
  match s.floorDamageRequest with
  | .error error => { s with physicsError := some error }
  | .ok (amount,rng) =>
    let next := { s with rng }
    if amount == 0 then next else damage next amount

/-- Live PlayerThink preparation through secret-sector handling. Errors retain
exactly the state reached before the failed phase, including a prepared player
when sector lookup fails. Later sector effects and player actions follow this. -/
def Simulation.prepareSectorTick (s : Simulation) (keys : UInt32)
    (command : Option Ticcmd := none) : Except Simulation (Simulation × Ticcmd) :=
  let player := { s.player with inventory := s.inventory }
  match player.prepareTick s.map keys command with
  | .error error => .error { s with physicsError := some error }
  | .ok (player, cmd) =>
    let prepared := { s with player }
    match prepared.discoverSecret with
    | .error error => .error { prepared with physicsError := some error }
    | .ok next => .ok (next, cmd)

/-- Weapon selection belongs to the live-player branch before use and psprites.
A lethal floor hit earlier in this tic does not skip this phase. -/
def Simulation.selectWeapon (s : Simulation) (keys : UInt32) : Simulation :=
  let choice := if keyDown keys 16384 then some 0 else if keyDown keys 32768 then some 1
    else if keyDown keys 65536 then some 2 else none
  let c : Weapon.Context := { player := s.inventory.toPickup }
  { s with inventory := { s.inventory with pickupState := { s.inventory.pickupState with
      pendingWeapon := (c.select choice).player.pendingWeapon } } }

/-- One simulation tick, shared by the SDL viewer and scripted tests. -/
def Simulation.interactionTick (s : Simulation) (keys : UInt32) (walking : Bool := true)
    (command : Option Ticcmd := none) (playerActions : Simulation → Simulation := id)
    (sectorEffects : Simulation → Simulation := id) : Simulation := Id.run do
  if s.physicsError.isSome then return s
  let mut s := { s with
    ticks := s.ticks + 1, messageTicks := s.messageTicks - 1,
    hudMessageTicks := s.hudMessageTicks - 1,
    audioEvents := #[], moverSounds := #[], exitSwitchSound := false, shotEvents := #[], deathEvents := #[] }
  s := s.updateButtons
  if s.physicsError.isSome then return s
  if walking then
    let (next, cmd) ← match s.prepareSectorTick keys command with
      | .ok prepared => pure prepared
      | .error failed => return failed
    s := next
    s := sectorEffects s
    if s.physicsError.isSome then return s
    if s.combatEnabled then s := s.selectWeapon keys
    if UseButton.request s.useHeld (keyDown keys 4096) then s := s.use
    s := { s with useHeld := keyDown keys 4096 }
    s := playerActions s
    if s.physicsError.isSome then return s
    -- P_MovePsprites precedes power/damage counters; both precede item contact.
    s := { s with inventory := s.inventory.tick }
    let oldLandings := s.player.landingEvents
    let player := { s.player with inventory := s.inventory }
    let lighting : SectorLights.World := {
      map := s.map, thinkers := s.lights, rng := s.rng
      busy := s.doors.map (·.sector) ++ s.movers.map (·.sector)
      movers := s.movers, moverSounds := s.moverSounds }
    match player.moveTick s.map cmd s.dropped (some lighting) with
    | .ok player =>
      s := { s with player, inventory := player.inventory }
      if let some world := player.scene.bind (·.lighting) then
        for mover in world.movers do
          if !s.movers.any (·.sector == mover.sector) then
            s := s.dosSpawn s!"mover:{mover.sector}" (if mover.kind == .lift then 56 else 42) 51
        s := { s with map := world.map, lights := world.thinkers, rng := world.rng, movers := world.movers, moverSounds := world.moverSounds }
      -- Crossing actions happen during XY movement, before P_ZMovement's
      -- landing sound. Import their RNG first so it cannot erase the pitch draw.
      if player.landingEvents > oldLandings then s := s.sound "oof"
    | .error error => return { s with physicsError := some error }
    s := s.pickups
  return s

end Doom
