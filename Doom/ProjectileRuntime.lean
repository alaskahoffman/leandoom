import Doom.ImpRuntime
import Doom.PlayerDamage

namespace Doom

abbrev ProjectileDamage := Simulation → Nat → Nat → Option Nat → Option PlayerDamage.Inflictor → Simulation

private def record (s : Simulation) (id : Nat) (e : Projectile.Event) : Simulation :=
  let s := { s with projectileEvents := s.projectileEvents.push (id,e) }
  let s := match e with
    | .remove => s.dosDefer (s.projectiles[id]?.map (·.thinkerSerial) |>.getD s.nextDynamicSerial) s!"missile:{id}"
    | _ => s
  match e with | .remove => s.stopSound (.missile id) | _ => s

private def explode (s : Simulation) (id : Nat) (p : Projectile.Body) : Simulation × Projectile.Body :=
  let (p,rng) := Projectile.explode p s.rng
  ((record { s with rng } id (.sound "firxpl")).soundAt "firxpl" (some (.missile id)) ⟨p.motion.x,p.motion.y⟩,p)

private def attempt (damage : ProjectileDamage) (s : Simulation) (id : Nat) (p : Projectile.Body)
    (x y : Fixed) (spawn : Bool := false) : Except String (Simulation × Projectile.Body) := do
  let scene ← s.player.syncScene s.map
  let (position,ok) ← Projectile.position scene s.map p x y
  if ok then
    return (s,{ p with motion := { p.motion with x,y,floorz := position.floor,ceilingz := position.ceiling } })
  let mut s := s
  if let some target := position.missileHit then
    let (roll,rng) := s.rng.nextPlay
    let amount := 3*(roll%8+1)
    s := damage { s with rng } target amount (some p.source) (some ⟨p.motion.x,p.motion.y,p.motion.z⟩)
    s := record s id (.hit target amount)
  -- The sky check belongs to XYMovement, not CheckMissileSpawn.
  if !spawn then
    if let some line := position.ceilingLine then
      let sky := (s.map.sides[s.map.lines[line]!.back]?.bind (fun side => s.map.sectors[side.sector]?)).any (·.ceilingTexture == "F_SKY1")
      if sky then return (record s id .remove,{ p with removed := true })
  return explode s id p

def Simulation.spawnImpShot (s : Simulation) (source target : Nat) (damage : ProjectileDamage) : Except String Simulation := do
  let (p,rng) ← Projectile.spawn source (← s.impThing source) (← s.impThing target)
    (target == 0 && s.inventory.pickupState.shadow) s.rng
  let id := s.projectiles.size
  let s := s.dosSpawn s!"missile:{id}" 154
  let s := record (record { s with rng } id (.spawn source target)) id (.sound "firsht")
  let s := s.soundAt "firsht" (some (.actor source)) ⟨(← s.impThing source).x,(← s.impThing source).y⟩
  let (s,p) ← attempt damage s id p p.motion.x p.motion.y true
  return { s with
    projectiles := s.projectiles.push { p with thinkerSerial := s.nextDynamicSerial },
    nextDynamicSerial := s.nextDynamicSerial+1 }

def Simulation.tickProjectiles (s : Simulation) (damage : ProjectileDamage)
    (onlyId : Option Nat := none) : Except String Simulation := do
  let mut s := s
  for id in [:s.projectiles.size] do
    if onlyId.any (· != id) then continue
    let mut p := s.projectiles[id]!
    if p.removed then continue
    if !p.exploding then
      for (dx,dy) in p.motion.xySteps do
        (s,p) ← attempt damage s id p (p.motion.x+dx) (p.motion.y+dy)
        if p.removed then break
    if !p.removed && (p.motion.z != p.motion.floorz || p.motion.momz.raw != 0) then
      let mut motion := { p.motion with z := p.motion.z+p.motion.momz }
      let mut hit := false
      if motion.z.raw ≤ motion.floorz.raw then
        motion := { motion with z := motion.floorz, momz := ⟨max 0 motion.momz.raw⟩ }
        hit := true
      else if (motion.z+motion.height).raw > motion.ceilingz.raw then
        motion := { motion with z := motion.ceilingz-motion.height, momz := ⟨min 0 motion.momz.raw⟩ }
        hit := true
      p := { p with motion }
      if hit && !p.exploding then (s,p) := explode s id p
    let removed := p.removed
    p ← Projectile.tickState p
    if p.removed && !removed then s := record s id .remove
    s := { s with projectiles := s.projectiles.set! id p }
  return s

/-- P_RunThinkers visits doors and missiles in allocation order, not one batch
per kind, including effect thinkers and deferred frees. Imp fireballs have MF_NOBLOCKMAP, so a door does not height-clip them:
they observe changed plane heights on their own next position check. Map actors
and map-spawn lights still precede this dynamic subset; floors remain separate. -/
def Simulation.tickDoorsAndProjectiles (initial : Simulation) (damage : ProjectileDamage)
    : Except String Simulation := do
  let mut order : Array (Nat × Nat × Nat) := #[]
  for door in initial.doors do
    order := order.push (door.thinkerSerial,0,door.sector)
  for id in [:initial.projectiles.size] do
    let p := initial.projectiles[id]!
    if !p.removed then order := order.push (p.thinkerSerial,1,id)
  for i in [:initial.impacts.size] do
    order := order.push (initial.impacts[i]!.thinkerSerial,2,i)
  for i in [:initial.dosDeferred.size] do
    order := order.push (initial.dosDeferred[i]!.1,3,i)
  order := order.qsort (fun a b => a.1 < b.1)
  let mut s := { initial with doorSounds := #[], dosDeferred := #[] }
  for (_,door,id) in order do
    if door == 0 then
      s := s.moveDoors (some id)
      if let some error := s.physicsError then throw error
    else if door == 1 then s ← s.tickProjectiles damage (some id)
    else if door == 2 then
      let p ← Impact.tick s.impacts[id]!
      if p.removed then s := s.dosDefer p.thinkerSerial s!"impact:{p.thinkerSerial}"
      s := { s with impacts := s.impacts.set! id p }
    else s := s.dosRemove initial.dosDeferred[id]!.2
  return { s with impacts := s.impacts.filter (!·.removed) }

end Doom
