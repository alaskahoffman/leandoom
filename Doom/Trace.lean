import Doom.Combat
import Lean.Data.Json

namespace Doom.Trace
open Lean

private def fixed (n : Fixed) : Json := toJson n.raw.toInt

/-- Lossless raw integer snapshot. Array order is WAD order; actor keys are
original THINGS indices. No display floats, tolerances, or pointer addresses. -/
def snapshot (s : Simulation) : Except String Json := do
  -- Prototype enemies own their current position in map.things; imps retain
  -- precise positions in the collision scene. Use the same pure synchronization
  -- as gameplay queries, without mutating the running simulation.
  let scene ← s.player.syncScene s.map
  let b := s.player.body
  let p := s.inventory.toPickup
  let mut actors : List (String × Json) := []
  for i in [:s.original.things.size] do
    let thing := s.original.things[i]!
    if thing.kind ≤ 4 || !thing.active || (thingDef thing.kind).isNone then continue
    let some body := scene.things[i+1]? | throw "trace: missing map actor slot"
    let actor := s.actors.find? (·.thing == i)
    if body.removed || actor.any (fun a => a.death.any (·.removed)) then continue
    let health := actor.map (fun a => a.death.map (fun d => d.health.toInt) |>.getD (Int.ofNat a.health)) |>.getD body.health.toInt
    actors := actors ++ [(toString i, Json.mkObj [
      ("kind",toJson thing.kind),("x",fixed body.x),("y",fixed body.y),
      ("z",fixed body.z),("health",toJson health)])]
  let mut brains : List (String × Json) := []
  for actor in s.actors do
    if actor.thing ≥ s.original.things.size || actor.death.any (·.removed) then continue
    let some brain := actor.imp | continue
    let body := scene.things[actor.thing+1]!
    brains := brains ++ [(toString actor.thing,Json.mkObj [
      ("state",toJson (actor.death.map (·.state) |>.getD brain.frame)),
      ("tics",toJson ((actor.death.map (·.tics) |>.getD brain.tics).toInt)),
      ("angle",toJson brain.angle.raw.toNat),("movedir",toJson brain.movedir),
      ("movecount",toJson brain.movecount.toInt),("reaction",toJson brain.reaction.toInt),
      ("threshold",toJson brain.threshold.toInt),("lastlook",toJson brain.lastlook),
      ("target",toJson (brain.target.map Int.ofNat |>.getD (-1))),
      ("behaviorFlags",toJson ((if brain.ambush then 32 else 0)+(if brain.justHit then 64 else 0)+(if brain.justAttacked then 128 else 0) : Nat)),
      ("x",fixed body.x),("y",fixed body.y),("z",fixed body.z),
      ("momx",fixed body.momx),("momy",fixed body.momy),("momz",fixed actor.momz),
      ("health",toJson (actor.death.map (·.health.toInt) |>.getD (Int.ofNat actor.health)))])]
  return Json.mkObj [
    ("enemyBrains",Json.mkObj brains),
    ("levelTime",toJson s.ticks),
    ("rng",Json.mkObj [("play",toJson s.rng.play.toNat),("misc",toJson s.rng.misc.toNat)]),
    ("player",Json.mkObj [
      ("x",fixed b.x),("y",fixed b.y),("z",fixed b.z),
      ("momx",fixed b.momx),("momy",fixed b.momy),("momz",fixed b.momz),
      ("angle",toJson b.angle.raw.toNat),("floor",fixed b.floorz),("ceiling",fixed b.ceilingz),
      ("viewZ",fixed s.player.view.z),("viewHeight",fixed s.player.view.height),
      ("viewDelta",fixed s.player.view.delta),("bob",fixed s.player.view.bob),
      ("health",toJson p.health.toInt),("armor",toJson p.armor.toInt),("armorType",toJson p.armorType.toInt),
      ("ammo",toJson (p.ammo.toArray.map Int32.toInt)),
      ("readyWeapon",toJson p.readyWeapon.val),
      ("pendingWeapon",if p.pendingWeapon.val == 9 then .null else toJson p.pendingWeapon.val),
      ("secrets",toJson s.secrets.toInt)]),
    ("weapon",Json.mkObj [
      ("state",toJson s.weapon.weapon.frame),("tics",toJson s.weapon.weapon.tics.toInt),
      ("x",fixed s.weapon.weapon.x),("y",fixed s.weapon.weapon.y),
      ("flashState",toJson s.weapon.flash.frame),("flashTics",toJson s.weapon.flash.tics.toInt),
      ("refire",toJson s.weapon.refire.toInt),("extraLight",toJson s.weapon.extraLight.toInt)]),
    ("sectors",toJson (s.map.sectors.map fun sec => Json.mkObj [
      ("floor",fixed (Fixed.ofInt sec.floor)),("ceiling",fixed (Fixed.ofInt sec.ceiling)),
      ("light",toJson sec.light),("special",toJson sec.special)])),
    ("lineSpecials",toJson (s.map.lines.map (·.special))),
    ("sideOffsets",toJson (s.map.sides.map fun side => (Fixed.ofInt side.xOffset).raw.toInt)),
    ("impacts",toJson (s.impacts.map fun effect => Json.mkObj [
      ("x",fixed effect.motion.x),("y",fixed effect.motion.y),("z",fixed effect.motion.z),
      ("momz",fixed effect.motion.momz),("floor",fixed effect.motion.floorz),
      ("ceiling",fixed effect.motion.ceilingz),("state",toJson effect.frame),
      ("tics",toJson effect.tics.toInt),("lastlook",toJson effect.lastlook)])),
    ("projectiles",toJson ((s.projectiles.filter (!·.removed)).map fun shot => Json.mkObj [
      ("x",fixed shot.motion.x),("y",fixed shot.motion.y),("z",fixed shot.motion.z),
      ("momx",fixed shot.motion.momx),("momy",fixed shot.motion.momy),("momz",fixed shot.motion.momz),
      ("angle",toJson shot.motion.angle.raw.toNat),
      ("floor",fixed shot.motion.floorz),("ceiling",fixed shot.motion.ceilingz),
      ("state",toJson shot.frame),("tics",toJson shot.tics.toInt),
      ("source",toJson shot.source),("lastlook",toJson shot.lastlook),
      ("missile",toJson (if shot.exploding then 0 else 1 : Nat))])),
    ("actors",Json.mkObj actors), ("exitRequested",toJson s.exitRequested)]

def record (s : Simulation) (tick : Nat) (cmd : Option Ticcmd) : Except String Json := do
  return Json.mkObj [
  ("tick",toJson tick),
  ("command",cmd.map (fun c => toJson #[c.forwardMove.toInt,c.sideMove.toInt,c.angleTurn.toInt,Int.ofNat c.buttons.toNat]) |>.getD .null),
  ("state",← snapshot s)]

end Doom.Trace
