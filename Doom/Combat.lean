import Doom.ProjectileRuntime
import Doom.Radius
import Doom.PlayerDamage
import Doom.PlayerDeath

namespace Doom

private def number (n : Int) : Float := n.toInt64.toFloat

/-- Segment/line fraction. Shooting and sight share the same portal geometry. -/
private def fraction (map : Map) (line : Linedef) (x y tx ty : Float) : Option Float :=
  let a := map.vertices[line.v1]!
  let b := map.vertices[line.v2]!
  let dx := tx-x
  let dy := ty-y
  let ex := number (b.x-a.x)
  let ey := number (b.y-a.y)
  let ax := number a.x-x
  let ay := number a.y-y
  let denominator := dx*ey-dy*ex
  if denominator.abs < 0.0000001 then none else
    let t := (ax*ey-ay*ex)/denominator
    let u := (ax*dy-ay*dx)/denominator
    if t > 0.000001 && t ≤ 1 && u ≥ 0 && u ≤ 1 then some t else none

def Map.rayClear (map : Map) (x y z tx ty tz : Float) : Bool := Id.run do
  for line in map.lines do
    let some t := fraction map line x y tx ty | continue
    if line.flags / 4 % 2 == 0 then return false
    let some front := map.sides[line.front]? | return false
    let some back := map.sides[line.back]? | return false
    let a := map.sectors[front.sector]!
    let b := map.sectors[back.sector]!
    let height := z + t*(tz-z)
    if height ≤ number (max a.floor b.floor) || height ≥ number (min a.ceiling b.ceiling) then return false
  return true

private def floorAt (m : Map) (p : Vertex) : Int :=
  let index := (m.sectorAt (Fixed.ofInt p.x) (Fixed.ofInt p.y)).toOption.getD 0
  m.sectors[index]!.floor

private def Simulation.random (s : Simulation) : Nat × Simulation :=
  let (value, rng) := s.rng.nextPlay
  (value, { s with rng })

private def Simulation.notice (s : Simulation) (message : String) : Simulation :=
  { s with message, messageTicks := 70 }

private def sourceCredit (source : Option Nat) : Option (Option (Fin 4)) :=
  source.map fun id => if id == 0 then some 0 else none

private def Simulation.hurtPlayer (s : Simulation) (damage : Nat) (source : Option Nat)
    (inflictor : Option PlayerDamage.Inflictor := none) : Simulation := Id.run do
  let .ok scene := s.player.syncScene s.map | return { s with physicsError := some "damage: missing player scene" }
  let target := scene.things[0]!
  let inflictor := inflictor.orElse fun _ => source.bind fun id => scene.things[id]?.map fun t => ⟨t.x,t.y,t.z⟩
  let inventory := s.inventory
  let state : PlayerDamage.State := {
    x := target.x, y := target.y, z := target.z, momx := target.momx, momy := target.momy,
    momz := s.player.body.momz, health := Int32.ofNat inventory.health,
    playerHealth := Int32.ofNat inventory.health, armor := Int32.ofNat inventory.armor,
    armorType := Int32.ofNat inventory.armorType, damageCount := inventory.pickupState.damageCount,
    shootable := target.shootable, noClip := target.moveFlags.noClip,
    invulnerable := inventory.invulnerability > 0,
    sectorSpecial := Int32.ofInt s.map.sectors[target.sector]!.special }
  let result := PlayerDamage.apply state (Int32.ofNat damage) inflictor
    (source == some 0 && inventory.toPickup.readyWeapon == 7) false s.rng
  let body := { s.player.body with momx := result.state.momx, momy := result.state.momy, momz := result.state.momz }
  let target := { target with momx := body.momx, momy := body.momy, health := result.state.health }
  let player := { s.player with body, scene := some { scene with things := scene.things.set! 0 target } }
  let mut s := { s with player, rng := result.rng }
  if !result.applied then return s
  let inventory := Inventory.fromPickup { inventory.toPickup with
    health := result.state.playerHealth, bodyHealth := result.state.health,
    armor := result.state.armor, armorType := result.state.armorType, damageCount := result.state.damageCount }
  let lost := s.inventory.health-inventory.health
  s := { s with inventory, attacker := source.bind (fun id => if id == 0 then none else some (id-1)) }
  s := { s with player := { s.player with reactionTime := result.reactionTime s.player.reactionTime } }
  if result.killed then
    let weapon := (Weapon.drop { state := s.weapon, player := inventory.toPickup, dead := true }).state
    s := { s with weapon }
    match s.killPlayer result.state.health (sourceCredit source) with
    | .ok next => s := next
    | .error error => return { s with physicsError := some error }
  else if result.pain then
    s := { s with player := { s.player with animation := (PlayerAnim.enter 156).1 } }
  return s.notice (if inventory.health == 0 then "You died - R to restart" else s!"Hit for {lost}")

/-- P_PlayerInSpecialSector runs after view calculation but before use,
weapon actions, power counters, and XY/Z movement. A null source/inflictor
causes no thrust, but still runs normal armor, health and pain/death handling. -/
def Simulation.hurtFromFloor (s : Simulation) : Simulation :=
  s.applyFloorEffect (fun current amount => current.hurtPlayer amount none)

/-- The live combat callback uses the shared request exactly once and installs
its RNG before entering health/armor/pain/death handling. -/
theorem Simulation.hurtFromFloor_request (s : Simulation) :
    s.hurtFromFloor =
      match s.floorDamageRequest with
      | .error error => { s with physicsError := some error }
      | .ok (amount,rng) =>
        let next := { s with rng }
        if amount == 0 then next else next.hurtPlayer amount none := rfl

private def Simulation.hurtActor (s : Simulation) (index damage : Nat)
    (source : Option Nat) (inflictor : Option PlayerDamage.Inflictor := none) : Simulation := Id.run do
  let mut s := s
  let actor := s.actors[index]!
  let some spec := enemySpec actor.kind | return s
  if actor.health == 0 then return s
  let result := do
    let scene ← s.player.syncScene s.map
    let target := scene.things[actor.thing+1]!
    let inflictor : Option PlayerDamage.Inflictor := inflictor.orElse fun _ => source.bind fun id =>
      scene.things[id]?.map fun (t : Collision.SolidThing) => ⟨t.x,t.y,t.z⟩
    -- Original mass: demon 400; zombieman, shotgunner, imp and barrel 100.
    let mass : Int32 := if actor.kind == 3002 then 400 else 100
    let (mx,my,rng) := DamageThrust.apply ⟨target.x,target.y,target.z⟩ (Int32.ofNat actor.health)
      (Int32.ofNat damage) mass target.momx target.momy inflictor target.moveFlags.noClip
      (source == some 0 && s.inventory.toPickup.readyWeapon == 7) s.rng
    let scene := { scene with things := scene.things.set! (actor.thing+1) { target with momx := mx, momy := my } }
    return { s with rng, player := { s.player with scene := some scene } }
  match result with
  | .ok next => s := next
  | .error error => return { s with physicsError := some error }
  let health := Int32.ofNat actor.health - Int32.ofNat damage
  if health ≤ 0 then
    match s.killActor index health (sourceCredit source) with
    | .ok next => return next.notice "Enemy down"
    | .error error => return { s with physicsError := some error }
  let mut actor := { actor with health := health.toInt.toNat }
  -- P_DamageMobj returns on lethal damage before assigning target. Barrels
  -- retain the first surviving hit's source: their threshold never chases down.
  if actor.damageTarget.isNone && source != some (actor.thing+1) then
    actor := { actor with damageTarget := source }
  let (roll,next) := s.random
  s := next
  if let some imp := actor.imp then
    let pain := roll < spec.painChance
    let imp := { imp with reaction := 0, justHit := imp.justHit || pain }
    let imp := if imp.threshold == 0 && source.isSome && source != some imp.id then
        { imp with target := source, threshold := 100 } else imp
    let entry := if pain then some imp.painFrame
      else if imp.frame == imp.spawnFrame && imp.target.isSome then some imp.chaseFrame else none
    actor := { actor with imp := some imp }
    s := { s with actors := s.actors.set! index actor }
    if let some frame := entry then
      match s.impRun index (some frame) with
      | .ok next => s := next
      | .error error => return { s with physicsError := some error }
    return s.notice s!"Hit - enemy health {health}"
  if roll < spec.painChance then
    actor := { actor with mode := .pain, age := 0 }
    s := s.sound (if actor.kind == 3002 then "dmpain" else "popain") (.actor (actor.thing+1))
  else if actor.mode == .idle && actor.kind != 2035 && actor.kind != 3001 then actor := { actor with mode := .chase, age := 0 }
  return { (s.notice s!"Hit - enemy health {health}") with actors := s.actors.set! index actor }

private def Simulation.applyCombatDamage (s : Simulation) (target damage : Nat) (source : Option Nat)
    (inflictor : Option PlayerDamage.Inflictor := none) : Simulation :=
  if target == 0 then s.hurtPlayer damage source inflictor
  else match s.actors.findIdx? (·.thing == target-1) with
    | some index => s.hurtActor index damage source inflictor
    | none => s

private def Simulation.alertImps (s : Simulation) : Simulation :=
  match s.noiseAlert with
  | .ok next => next
  | .error e => { s with physicsError := some e }

/-- Reuse live block links and exact clipped actor heights. Prototype actor
movement still mirrors map positions into this scene at the combat boundary. -/
private def Simulation.combatScene (s : Simulation) : Except String Collision.Scene :=
  s.player.syncScene s.map

/-- Consume ordered hit requests: puff/blood spawning precedes damage and its
pain/death draws. Full P_DamageMobj remains pending.
E1M1 has no shoot-activated specials; unsupported active cases fail explicitly. -/
private def Simulation.shoot (s : Simulation) (shooter : Nat) (angle : Angle)
    (slope : Fixed) (damage : Nat) (distance : Fixed := Fixed.ofInt 2048) : Simulation := Id.run do
  let result := do
    let scene ← s.combatScene
    scene.lineAttack shooter angle distance slope (Int32.ofNat damage)
      (fun id =>
        let line := s.map.lines[id]!
        let front := s.map.sectors[s.map.sides[line.front]!.sector]!.ceilingTexture == "F_SKY1"
        let back := (s.map.sides[line.back]?.bind fun side => s.map.sectors[side.sector]?).any (fun (sector : Sector) => sector.ceilingTexture == "F_SKY1")
        (front,back))
      (fun id => id > 0 && s.map.things[id-1]!.kind == 2035)
  let .ok result := result | return { s with physicsError := (match result with | .error error => some error | .ok _ => none) }
  let mut s := { s with shotSlope := slope }
  for event in result.events do
    s := { s with shotEvents := s.shotEvents.push (shooter,event) }
    match event with
    | .puff x y z | .blood x y z _ =>
      let .ok sector := s.map.sectorAt x y | return { s with physicsError := some "impact: invalid spawn sector" }
      let sec := s.map.sectors[sector]!
      let (blood,amount) := match event with | .blood _ _ _ n => (true,n) | _ => (false,0)
      let (impact,rng) := Impact.spawn blood amount (distance == Fixed.ofInt 64)
        x y z (Fixed.ofInt sec.floor) (Fixed.ofInt sec.ceiling) s.rng
      s := s.dosSpawn s!"impact:{s.nextDynamicSerial}" 154
      s := { s with
        rng, impacts := s.impacts.push { impact with thinkerSerial := s.nextDynamicSerial }
        nextDynamicSerial := s.nextDynamicSerial+1 }
    | .special id =>
      let special := s.map.lines[id]!.special
      if special == 46 || (shooter == 0 && (special == 24 || special == 47)) then
        return { s with physicsError := some s!"combat: shoot-activated special {special} is not ported" }
    | .damage target amount =>
      if target == 0 then s := s.hurtPlayer amount.toInt.toNat (some shooter)
      else if let some index := s.actors.findIdx? (fun (actor : Actor) => actor.thing == target-1) then
        s := s.hurtActor index amount.toInt.toNat (some shooter)
  return s

/-- A_FirePistol/A_FireShotgun share one autoaim slope. Each pellet consumes
its damage/spread draws immediately before tracing and applying its damage, so
pain/death RNG from earlier pellets interleaves with later pellet draws. -/
def Simulation.fireGun (s : Simulation) (shotgun accurate : Bool) : Simulation := Id.run do
  let mut s := (s.sound (if shotgun then "shotgn" else "pistol")).notice (if shotgun then "Shotgun fired" else "Pistol fired")
  let aiming := do
    let scene ← s.combatScene
    scene.bulletAim 0 s.player.body.angle
  let .ok aim := aiming | return { s with physicsError := (match aiming with | .error error => some error | .ok _ => none) }
  let slope := aim.slope
  s := { s with shots := s.shots+1, lastShot := s.ticks, lastFire := s.lastFire.map fun shot => { shot with aim := some aim } }
  let gun : Fire.Gun := if shotgun then .shotgun else .pistol
  for _ in [:gun.pellets] do
    let (roll,next) := s.random
    s := next
    let damage := 5*(roll%3+1)
    let mut angle := s.player.body.angle
    if !accurate then
      let (spread,rng) := s.rng.subPlay
      s := { s with rng }
      angle := ⟨angle.raw + (Int32.ofInt spread * 262144).toUInt32⟩
    s := s.shoot 0 angle slope damage
    if s.physicsError.isSome then return s
    s := { s with lastFire := s.lastFire.map fun shot => { shot with pelletsTraced := shot.pelletsTraced+1, pelletAngles := shot.pelletAngles.push angle.raw } }
  return s

private def Simulation.punch (s : Simulation) : Simulation := Id.run do
  let (roll,s) := s.random
  let (spread,rng) := s.rng.subPlay
  let mut s := { s with rng }
  let damage := 2*(roll%10+1)*(if s.inventory.berserk then 10 else 1)
  let angle : Angle := ⟨s.player.body.angle.raw + (Int32.ofInt spread * 262144).toUInt32⟩
  let result := do
    let scene ← s.combatScene
    scene.aimLineAttack 0 angle (Fixed.ofInt 64)
  let .ok aim := result | return { s with physicsError := (match result with | .error e => some e | .ok _ => none) }
  let before := s.shotEvents.size
  s := s.shoot 0 angle aim.slope damage (Fixed.ofInt 64)
  -- P_LineAttack's target, not merely autoaim, controls impact sound and facing.
  for (_,event) in s.shotEvents.extract before s.shotEvents.size do
    if let .damage target _ := event then
      s := s.sound "punch"
      if let some body := s.player.scene.bind (fun scene => scene.things[target]?) then
        let facing := Angle.fromVector (body.x-s.player.body.x) (body.y-s.player.body.y)
        s := { s with player := { s.player with body := { s.player.body with angle := facing }, camera := { s.player.camera with angle := facing } } }
  return s

/-- The actual runtime inputs to the weapon updater, shared with correspondence
proofs so attack state, player inventory and tic timing cannot drift. -/
def Simulation.weaponContext (s : Simulation) (keys : UInt32) : Weapon.Context :=
  { state := s.weapon, player := s.inventory.toPickup, body := s.player.animation,
    attack := keyDown keys 8192, dead := s.inventory.health == 0,
    bob := s.player.view.bob, time := Int32.ofNat (s.ticks-1) }

/-- Execute one weapon event at its actual emission site, including the fire
sample before hitscan/audio. Exposed for the production correspondence boundary. -/
def Simulation.weaponEvent (s : Simulation) (before : Vector Int32 4)
    (after : Pickup.State) (event : Weapon.Event) : Simulation := Id.run do
  let mut s := s
  let gun := match event with | .pistol _ => some Fire.Gun.pistol | .shotgun => some .shotgun | _ => none
  if let some gun := gun then
    s := { s with lastFire := some { gun, tic := s.ticks, ammoBefore := before[gun.ammoIndex], ammoAfter := after.ammo[gun.ammoIndex], pelletsExpected := gun.pellets } }
  s := match event with
  | .pistol accurate => s.fireGun false accurate
  | .shotgun => s.fireGun true false
  | .punch => s.punch
  | .noise => s.alertImps
  return s

/-- Apply the weapon update and execute its ordered gameplay events. -/
def Simulation.weaponTick (s : Simulation) (keys : UInt32) : Simulation := Id.run do
  let context := s.weaponContext keys
  let before := context.player.ammo
  let context := Weapon.tick context
  let mut age := 100
  let first := Weapon.attackState context.player.readyWeapon.val
  if context.state.weapon.frame ≥ first && context.state.weapon.frame < (if context.player.readyWeapon == 0 then 10 else if context.player.readyWeapon == 1 then 17 else 30) then
    age := 0
    for f in [first:context.state.weapon.frame] do age := age + WeaponData.frames[f]!.tics.toInt.toNat
    age := age + (WeaponData.frames[context.state.weapon.frame]!.tics-context.state.weapon.tics).toInt.toNat
  let mut s := { s with weapon := context.state, player := { s.player with animation := context.body }, inventory := Inventory.fromPickup context.player, weaponAge := age, attackDown := context.state.attackDown, refire := context.state.refire != 0 }
  for event in context.events do
    s := s.weaponEvent before context.player event
    if s.physicsError.isSome then return s
  return s

private def actorCanMove (s : Simulation) (actor : Actor) (position : Vertex) : Bool := Id.run do
  let some spec := thingDef actor.kind | return false
  let old := s.map.things[actor.thing]!.position
  let .ok sector := s.map.sectorAt (Fixed.ofInt position.x) (Fixed.ofInt position.y) | return false
  let sec := s.map.sectors[sector]!
  let feet := floorAt s.map old
  let mut floor := sec.floor
  let mut lowest := sec.floor
  let mut ceiling := sec.ceiling
  let x := number position.x
  let y := number position.y
  let radius := spec.radius.toUInt64.toFloat
  if position.x < -32767 || position.x > 32767 || position.y < -32767 || position.y > 32767 then return false
  for line in s.map.lines do
    if segmentDistanceSq x y s.map.vertices[line.v1]! s.map.vertices[line.v2]! ≥ radius*radius then continue
    if line.flags%4 != 0 || line.flags/4%2 == 0 then return false
    let some front := s.map.sides[line.front]? | return false
    let some back := s.map.sides[line.back]? | return false
    let a := s.map.sectors[front.sector]!
    let b := s.map.sectors[back.sector]!
    floor := max floor (max a.floor b.floor)
    lowest := min lowest (min a.floor b.floor)
    ceiling := min ceiling (min a.ceiling b.ceiling)
  if floor-feet > 24 || feet-lowest > 24 || ceiling-floor < Int.ofNat spec.height then return false
  let dx := x-s.player.camera.x.toFloat
  let dy := y-s.player.camera.y.toFloat
  if dx*dx+dy*dy < (radius+16)*(radius+16) && s.inventory.health > 0 then return false
  for index in [:s.map.things.size] do
    if index == actor.thing then continue
    let t := s.map.things[index]!
    if !t.active then continue
    let some d := thingDef t.kind | continue
    let corpse := (s.actors.find? (fun actor => actor.thing == index)).bind (·.death)
    if corpse.any (fun body => body.flags &&& 2 == 0) || !d.solid then continue
    let height := corpse.map (fun body => body.height.raw.toInt / 65536) |>.getD (Int.ofNat d.height)
    let z := floorAt s.map t.position
    if floor ≥ z + height || floor + Int.ofNat spec.height ≤ z then continue
    let dx := x-number t.position.x
    let dy := y-number t.position.y
    let separation := radius+d.radius.toUInt64.toFloat
    if dx*dx+dy*dy < separation*separation then return false
  return true

private def Simulation.moveActor (s : Simulation) (actor : Actor) : Simulation := Id.run do
  let some spec := enemySpec actor.kind | return s
  let old := s.map.things[actor.thing]!
  let dx := s.player.camera.x.toFloat-number old.position.x
  let dy := s.player.camera.y.toFloat-number old.position.y
  let length := (dx*dx+dy*dy).sqrt
  if length < 1 then return s
  let stepX := (dx / length * spec.speed.toUInt64.toFloat).round.toInt64.toInt
  let stepY := (dy / length * spec.speed.toUInt64.toFloat).round.toInt64.toInt
  let mut s := s
  -- Split each movement into <=2-unit increments before axis sliding.
  let pieces := max 1 ((max stepX.natAbs stepY.natAbs + 1) / 2)
  let mut position := old.position
  for j in [:pieces] do
    let sx := (stepX * Int.ofNat (j+1) / Int.ofNat pieces) - (stepX * Int.ofNat j / Int.ofNat pieces)
    let sy := (stepY * Int.ofNat (j+1) / Int.ofNat pieces) - (stepY * Int.ofNat j / Int.ofNat pieces)
    let candidates := #[⟨position.x+sx, position.y+sy⟩, ⟨position.x+sx, position.y⟩, ⟨position.x, position.y+sy⟩]
    for candidate in candidates do
      if actorCanMove s actor candidate then
        position := candidate
        break
    let thing := { old with position }
    s := { s with map := { s.map with things := s.map.things.set! actor.thing thing } }
  return s

private def actorSees (s : Simulation) (a : Actor) : Bool :=
  let thing := s.map.things[a.thing]!
  s.map.rayClear (number thing.position.x) (number thing.position.y) (number (floorAt s.map thing.position)+28)
    s.player.camera.x.toFloat s.player.camera.y.toFloat (s.player.feet+28)

private def Simulation.enemyAttack (s : Simulation) (a : Actor) : Simulation := Id.run do
  let some spec := enemySpec a.kind | return s
  if s.inventory.health == 0 || !actorSees s a then return s
  let thing := s.map.things[a.thing]!
  let x := number thing.position.x
  let y := number thing.position.y
  let dx := s.player.camera.x.toFloat-x
  let dy := s.player.camera.y.toFloat-y
  let distance := (dx*dx+dy*dy).sqrt
  let mut s := s
  if spec.melee then
    if distance ≥ 64 || (s.player.feet-number (floorAt s.map thing.position)).abs > 56 then return s
    let (roll, next) := s.random
    return (next.sound "sgtatk" (.actor (a.thing+1))).hurtPlayer (4*(roll%10+1)) (some (a.thing+1))
  let angle := Angle.fromVector (s.player.body.x - Fixed.ofInt thing.position.x)
    (s.player.body.y - Fixed.ofInt thing.position.y)
  let aiming := do
    let scene ← s.combatScene
    scene.aimLineAttack (a.thing+1) angle (Fixed.ofInt 2048)
  let .ok aiming := aiming | return { s with physicsError := (match aiming with | .error error => some error | .ok _ => none) }
  s := s.sound (if a.kind == 9 then "shotgn" else "pistol") (.actor (a.thing+1))
  for _ in [:spec.pellets] do
    let (spread,rng) := s.rng.subPlay
    s := { s with rng }
    let (damage,next) := s.random
    s := next
    let shotAngle : Angle := ⟨angle.raw + (Int32.ofInt spread * 1048576).toUInt32⟩
    s := s.shoot (a.thing+1) shotAngle aiming.slope (3*(damage%5+1))
    if s.physicsError.isSome then return s
  return s

/-- A_PosAttack after the shared brain has run A_FaceTarget. No extra sight or
range gate: the original attack uses the target retained by the state machine. -/
private def Simulation.zombieAttack (s : Simulation) (actor : Actor) : Simulation := Id.run do
  let some brain := actor.imp | return { s with physicsError := some "zombie: missing brain" }
  let aiming := do
    let scene ← s.combatScene
    scene.aimLineAttack (actor.thing+1) brain.angle (Fixed.ofInt 2048)
  let .ok aiming := aiming | return { s with physicsError := (match aiming with | .error error => some error | .ok _ => none) }
  let s := s.sound "pistol" (.actor (actor.thing+1))
  let (spread,rng) := s.rng.subPlay
  let (damage,rng) := rng.nextPlay
  let angle : Angle := ⟨brain.angle.raw + (Int32.ofInt spread <<< 20).toUInt32⟩
  return ({ s with rng } : Simulation).shoot (actor.thing+1) angle aiming.slope (3*(damage%5+1))

/-- A_Explode uses the barrel's existing target, not necessarily the lethal
attacker. Sight runs from each victim toward the already-quarter-height barrel. -/
private def Simulation.explodeBarrel (s : Simulation) (actor : Actor) : Simulation := Id.run do
  let result := do
    let scene ← s.combatScene
    let spot := scene.things[actor.thing+1]!
    let hits ← scene.radiusAttack spot 128
      (fun id => if id == 0 then 0 else s.map.things[id-1]!.kind) (Sight.check s.map)
    return (hits,spot)
  let .ok (hits,spot) := result | return { s with physicsError := (match result with | .error e => some e | _ => none) }
  let mut s := s
  for (target,amount) in hits do
    s := { s with blastEvents := s.blastEvents.push (actor.thing+1,target,amount) }
    if target == 0 then
      s := s.hurtPlayer amount.toInt.toNat actor.damageTarget (some ⟨spot.x,spot.y,spot.z⟩)
    else if let some index := s.actors.findIdx? (·.thing == target-1) then
      s := s.hurtActor index amount.toInt.toNat actor.damageTarget (some ⟨spot.x,spot.y,spot.z⟩)
    if s.physicsError.isSome then return s
  return s

private def Simulation.actorTick (s : Simulation) : Simulation := Id.run do
  let mut s := s
  let mut cursor := 0
  for index in [:s.actors.size] do
    for thing in [cursor:s.actors[index]!.thing+1] do
      if s.collected.contains thing || s.crushedDrops.contains thing ||
          s.actors.any (fun a => a.thing == thing && a.death.any (·.removed)) then
        s := s.dosRemove s!"thing:{thing}"
    cursor := s.actors[index]!.thing+1
    if s.physicsError.isSome then return s
    match s.moveActorMomentum index with
    | .ok next => s := next
    | .error error => return { s with physicsError := some error }
    if s.actors[index]!.death.isSome then
      let eventStart := s.deathEvents.size
      match s.tickCorpse index with
      | .ok next => s := next
      | .error error => return { s with physicsError := some error }
      for event in s.deathEvents[eventStart:].toArray do
        if let .explode := event.2 then s := s.explodeBarrel s.actors[index]!
      continue
    let mut a := s.actors[index]!
    let some spec := enemySpec a.kind | continue
    a := { a with age := a.age+1, cooldown := a.cooldown-1 }
    if a.imp.isSome then
      let first := s.impEvents.size
      match s.impRun index with
      | .error error => return { s with physicsError := some error }
      | .ok next => s := next
      for (_,event) in s.impEvents[first:].toArray do
        match event with
        | .melee target amount => s := s.applyCombatDamage target amount (some (a.thing+1))
        | .missile target =>
          match s.spawnImpShot (a.thing+1) target (fun s target damage source inflictor => s.applyCombatDamage target damage source inflictor) with
          | .ok next => s := next
          | .error error => return { s with physicsError := some error }
        | .hitscan _ => s := s.zombieAttack s.actors[index]!
        | .sound _ => pure ()
      continue
    if a.kind == 2035 then
      s := { s with actors := s.actors.set! index a }
      continue
    if a.health == 0 || s.inventory.health == 0 then
      s := { s with actors := s.actors.set! index a }
      continue
    let t := s.map.things[a.thing]!
    let dx := s.player.camera.x.toFloat-number t.position.x
    let dy := s.player.camera.y.toFloat-number t.position.y
    let distance := (dx*dx+dy*dy).sqrt
    if a.mode == .idle then
      let facing := (Angle.ofDegrees t.angle).radians
      let heard := t.flags/8%2 == 0 && s.shots > 0 && s.ticks-s.lastShot < 35 && distance < 1024
      let looking := a.age == 1 || a.age % 10 == 0
      if looking && distance < 2048 && (dx*facing.cos+dy*facing.sin ≥ 0 || distance < 64 || heard) && actorSees s a then
        a := { a with mode := .chase, age := 0 }
        s := s.sound (if a.kind == 3002 then "sgtsit" else "posit1") (.actor (a.thing+1))
    else if a.mode == .pain then
      let duration := (actorPoses a.kind .pain).foldl (fun n p => n+p.ticks) 0
      if a.age ≥ duration then a := { a with mode := .chase, age := 0 }
    else if a.mode == .attack then
      if a.age == spec.attackTick then s := s.enemyAttack a
      if a.age ≥ spec.attackLength then a := { a with mode := .chase, age := 0, cooldown := 35 }
    else if a.mode == .chase then
      if a.cooldown == 0 && (if spec.melee then distance < 64 else distance < 1024) && actorSees s a then
        a := { a with mode := .attack, age := 0 }
      else if a.age % spec.movePeriod == 0 then
        s := s.moveActor a
    if a.mode != .idle then
      let angle := ((Float.atan2 dy dx * (180 / 3.141592653589793)).round.toInt64.toInt % 360).toNat
      let thing := { s.map.things[a.thing]! with angle }
      s := { s with map := { s.map with things := s.map.things.set! a.thing thing } }
    s := { s with actors := s.actors.set! index a }
  for thing in [cursor:s.map.things.size] do
    if s.collected.contains thing || s.crushedDrops.contains thing then
      s := s.dosRemove s!"thing:{thing}"
  return s

/-- Dead PlayerThink still lowers psprites, computes the fixed-point view,
turns toward the live attacker position, and then lets the player mobj move. -/
private def Simulation.deadPlayerTick (s : Simulation) (keys : UInt32)
    (command : Option Ticcmd) : Except String Simulation := do
  let mut s := s.weaponTick keys
  if let some error := s.physicsError then throw error
  let scene ← s.player.syncScene s.map
  let attacker := s.attacker.bind fun index => scene.things[index+1]?.map fun t =>
    (Angle.fromVector (t.x-s.player.body.x) (t.y-s.player.body.y)).raw
  let (angle,damage) := PlayerDeath.look s.player.body.angle.raw attacker s.inventory.pickupState.damageCount
  let body := { s.player.body with angle := ⟨angle⟩ }
  let view := PlayerDeath.view s.player.view body (Int32.ofNat (s.ticks-1))
  let inventory := Inventory.fromPickup { s.inventory.toPickup with damageCount := damage }
  let (cmd,keyboard) := match command with
    | some cmd => (cmd,s.player.keyboard)
    | none => s.player.keyboard.build (walkingKeys keys)
  let player := { s.player with body, view, inventory, keyboard }
  let lighting : SectorLights.World := {
    map := s.map, thinkers := s.lights, rng := s.rng,
    busy := s.doors.map (·.sector) ++ s.movers.map (·.sector),
    movers := s.movers, moverSounds := s.moverSounds }
  let oldLandings := player.landingEvents
  let player ← player.moveTick s.map cmd s.dropped (some lighting)
  s := { s with player, inventory := player.inventory }
  if let some world := player.scene.bind (·.lighting) then
    s := { s with
      map := world.map, lights := world.thinkers, rng := world.rng,
      movers := world.movers, moverSounds := world.moverSounds }
  if player.landingEvents > oldLandings then s := s.sound "oof"
  return s

/-- Shared combat/interaction tick. Free flight pauses combat for inspection. -/
def Simulation.tick (s : Simulation) (keys : UInt32) (walking : Bool := true)
    (command : Option Ticcmd := none) : Simulation := Id.run do
  if keyDown keys 1024 && !s.restartHeld then return { s.restart with restartHeld := true }
  -- G_ExitLevel queues completion; the activation tic finishes normally. Until
  -- G_DoCompleted/WI_Ticker are ported, hold the last level state at that boundary.
  if s.exitRequested then return { s with restartHeld := keyDown keys 1024 }
  let alive := s.inventory.health > 0
  let s := { s with blastEvents := #[], impEvents := #[], projectileEvents := #[] }
  let mut s := s.interactionTick keys (walking && alive) command
    (fun current => if current.combatEnabled then current.weaponTick keys else current)
    (fun current => if current.combatEnabled then current.hurtFromFloor else current)
  if s.physicsError.isSome then return s
  s := { s with restartHeld := keyDown keys 1024 }
  if s.combatEnabled && walking then
    if !alive then
      match s.deadPlayerTick keys command with
      | .ok next => s := next
      | .error error => return { s with physicsError := some error }
    -- The player's mobj precedes the prototype enemy loop. A death caused by
    -- an enemy this tic begins its countdown on the following tic.
    if s.inventory.health > 0 then
      let (animation,painSound) := PlayerAnim.tick s.player.animation
      s := { s with player := { s.player with animation } }
      if painSound then s := s.sound "plpain"
    match s.tickPlayerCorpse with
    | .ok next => s := next
    | .error error => return { s with physicsError := some error }
    s := s.actorTick
    if s.physicsError.isSome then return s
  -- Map-spawn lighting thinkers follow map actors but precede missiles appended
  -- during play. Their P_Random draws must precede missile explosion duration.
  let (map, lights, rng) := SectorLights.tickMap s.map s.lights s.rng
  s := { s with map, lights, rng }
  if s.combatEnabled && walking then
    match s.tickDoorsAndProjectiles (fun s target damage source inflictor => s.applyCombatDamage target damage source inflictor) with
    | .ok next => s := next
    | .error error => return { s with physicsError := some error }
    if s.physicsError.isSome then return s
  if !s.combatEnabled || !walking then s := s.moveDoors
  if s.physicsError.isSome then return s
  s := s.moveFloors
  if s.physicsError.isSome then return s
  for (sector,sound) in s.moverSounds do
    s := s.sound (match sound with | .move => "stnmov" | .stop => "pstop" | .start => "pstart") (.sector sector)
  -- P_UpdateSpecials follows the map thinkers; unrelated button timing and
  -- the surrounding actor scheduling remain the existing adapters.
  match Scrolling.tickMap s.map s.scrollers with
  | .ok map => s := { s with map }
  | .error error => return { s with physicsError := some error }
  if s.combatEnabled && walking then
    let (random, rng) := s.rng.nextMisc
    let attackerAngle := s.attacker.bind fun index => do
      let thing ← s.map.things[index]?
      return (Angle.fromVector (Fixed.ofInt thing.position.x - s.player.camera.x)
        (Fixed.ofInt thing.position.y - s.player.camera.y)).raw
    let face := s.statusFace.tick {
      player := s.inventory.toPickup
      attack := s.attackDown, angle := s.player.camera.angle.raw, attackerAngle, random }
    s := { s with statusFace := face, rng }
  return s

/-- Feed a decoded demo command directly to the same engine as the viewer.
No conversion of movement or turning into keyboard presses. This initial demo
profile supports ordinary buttons and fist/pistol/shotgun selection only. -/
def Simulation.tickCommand (s : Simulation) (cmd : Ticcmd) : Except String Simulation := do
  if cmd.buttons &&& 0xc0 != 0 then throw "demo: special/reserved buttons unsupported"
  let change := cmd.buttons &&& 4 != 0
  let weapon := (cmd.buttons >>> 3).toNat &&& 7
  if change && weapon > 2 then throw "demo: weapon selection outside fist/pistol/shotgun profile"
  let keys : UInt32 := (if cmd.buttons &&& 1 != 0 then 8192 else 0) |||
    (if cmd.buttons &&& 2 != 0 then 4096 else 0) |||
    (if change then #[16384,32768,65536][weapon]! else 0)
  if s.exitRequested then throw "demo: level completion/intermission is not implemented"
  let next := s.tick keys true (some cmd)
  if let some error := next.physicsError then throw error
  return next

end Doom
