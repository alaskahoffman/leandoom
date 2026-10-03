import Doom.Combat
import Lean.Data.Json

namespace Doom
open Lean

/-- Comma-separated `ticks:keys` commands, capped at 10000 ticks in total. -/
def runScript (start : Simulation) (script : String) : Except String Simulation := do
  let mut state := start
  let mut total := 0
  for command in script.splitOn "," do
    let [duration, mask] := command.splitOn ":" | throw "script: expected ticks:keymask pairs"
    let some ticks := duration.toNat? | throw "script: invalid tick count"
    let some keys := mask.toNat? | throw "script: invalid key mask"
    total := total + ticks
    let maximum := if start.combatEnabled then 131071 else 8191
    if total > 10000 || keys > maximum then throw s!"script: maximum 10000 ticks, keymask 0..{maximum}"
    for _ in [:ticks] do
      state := state.tick keys.toUInt32
      if let some error := state.physicsError then throw error
  return state

private def fixedJson (value : Fixed) : Json :=
  if value.raw == 0 then .num 0 else .num ⟨value.raw.toInt * 152587890625, 16⟩

private def floatJson (value : Float) : Json :=
  match JsonNumber.fromFloat? value with
  | .inr n => .num n
  | .inl error => .str error

private def deathJson (body : Option Death.Body) : Json :=
  match body with
  | none => .null
  | some body => Json.mkObj [
    ("health",toJson body.health.toInt),("flags",toJson body.flags.toNat),
    ("height",fixedJson body.height),("tics",toJson body.tics.toInt),
    ("state",toJson ((Death.frames.find? (·.id == body.state)).map (·.label) |>.getD "S_NULL")),
    ("solid",toJson (body.flags &&& 2 != 0))]

def Simulation.json (s : Simulation) : Json := Json.mkObj [
  ("ticks", toJson s.ticks),
  ("audioEvents",toJson (s.audioEvents.map fun e => Json.mkObj [("name",toJson e.name),("origin",toJson (reprStr e.origin)),("x",fixedJson e.position.x),("y",fixedJson e.position.y)])),
  ("secrets", toJson s.secrets.toInt), ("totalSecrets", toJson s.totalSecrets.toInt),
  ("exitRequested", toJson s.exitRequested), ("secretExit", toJson false),
  ("exitSwitchSound", toJson (if s.exitSwitchSound then "swtchn" else "")),
  ("playerDeath",deathJson s.playerDeath),
  ("impEvents",toJson (s.impEvents.map fun (id,e) => s!"{id}: {reprStr e}")),
  ("projectileEvents",toJson (s.projectileEvents.map fun (id,e) => s!"{id}: {reprStr e}")),
  ("soundTargets",toJson s.soundTargets),
  ("projectiles",toJson (s.projectiles.map fun p => Json.mkObj [
    ("source",toJson (Int.ofNat p.source-1)), ("x",fixedJson p.motion.x), ("y",fixedJson p.motion.y), ("z",fixedJson p.motion.z),
    ("momx",fixedJson p.motion.momx), ("momy",fixedJson p.motion.momy), ("momz",fixedJson p.motion.momz),
    ("tics",toJson p.tics.toInt), ("removed",toJson p.removed), ("exploding",toJson p.exploding),
    ("frame",toJson (((ImpData.frames.find? (·.id == p.frame)).map (·.label)).getD "")) ])),
  ("blastEvents",toJson (s.blastEvents.map fun (spot,target,damage) => Json.mkObj [
    ("spot",toJson (Int.ofNat spot-1)),("target",toJson (Int.ofNat target-1)),("damage",toJson damage.toInt)])),
  ("deathEvents",toJson (s.deathEvents.map fun (id,event) => Json.mkObj [("actor",toJson (Int.ofNat id-1)),("event",toJson (reprStr event))])),
  ("frags",toJson (s.deathStats[0].frags.toArray.map Int32.toInt)),
  ("shotSlope", fixedJson s.shotSlope),
  ("shotEvents", toJson (s.shotEvents.map fun (source,event) =>
    let fields := match event with
      | .special id => [("kind",toJson "special"),("line",toJson id)]
      | .puff x y z => [("kind",toJson "puff"),("x",fixedJson x),("y",fixedJson y),("z",fixedJson z)]
      | .blood x y z damage => [("kind",toJson "blood"),("x",fixedJson x),("y",fixedJson y),("z",fixedJson z),("damage",toJson damage.toInt)]
      | .damage target amount => [("kind",toJson "damage"),("target",toJson (Int.ofNat target-1)),("damage",toJson amount.toInt)]
    Json.mkObj (("source",toJson (Int.ofNat source-1))::fields))),
  ("shots", toJson s.shots), ("kills", toJson s.kills), ("rng", toJson s.rng.play.toNat),
  ("miscRng", toJson s.rng.misc.toNat),
  ("readyWeapon", toJson s.inventory.pickupState.readyWeapon.val),
  ("weaponState", toJson s.weapon.weapon.frame), ("weaponTics",toJson s.weapon.weapon.tics.toInt),
  ("weaponX",fixedJson s.weapon.weapon.x), ("weaponY",fixedJson s.weapon.weapon.y),
  ("flashState",toJson s.weapon.flash.frame), ("flashTics",toJson s.weapon.flash.tics.toInt),
  ("extraLight",toJson s.weapon.extraLight.toInt), ("refire",toJson s.weapon.refire.toInt),
  ("weaponAge", toJson s.weaponAge), ("dropped", toJson s.dropped),
  ("gibbed", toJson s.gibbed), ("crushedDrops", toJson s.crushedDrops),
  ("actors", toJson (s.actors.map (fun a => Json.mkObj [
    ("thing", toJson a.thing), ("kind", toJson a.kind), ("health", toJson a.health), ("death",deathJson a.death), ("pose",toJson a.pose.frame),
    ("impState",toJson (a.imp.map fun i => s!"{i.frame}:{i.tics}:{i.movedir}:{i.movecount}:{i.reaction}:{i.threshold}")),
    ("removed",toJson (a.death.any (·.removed))), ("damageTarget",toJson (a.damageTarget.map (fun id => Int.ofNat id-1))),
    ("mode", toJson (reprStr a.mode)), ("age", toJson a.age),
    ("x", toJson s.map.things[a.thing]!.position.x), ("y", toJson s.map.things[a.thing]!.position.y)]))),
  ("x", fixedJson s.player.camera.x),
  ("y", fixedJson s.player.camera.y),
  ("feet", floatJson s.player.feet), ("eye", fixedJson s.player.camera.z),
  ("momentum", toJson (#[s.player.body.momx, s.player.body.momy, s.player.body.momz].map fixedJson)),
  ("angle", toJson s.player.body.angle.raw.toNat),
  ("viewHeight", fixedJson s.player.view.height),
  ("landingEvents", toJson s.player.landingEvents),
  ("health", toJson s.inventory.health), ("armor", toJson s.inventory.armor),
  ("armorType", toJson s.inventory.armorType),
  ("blue", toJson s.inventory.blue), ("red", toJson s.inventory.red), ("yellow", toJson s.inventory.yellow),
  ("ammo", toJson #[s.inventory.bullets, s.inventory.shells, s.inventory.rockets, s.inventory.cells]),
  ("backpack", toJson s.inventory.backpack), ("weapons", toJson s.inventory.weapons),
  ("powers", toJson #[s.inventory.invulnerability, s.inventory.invisibility, s.inventory.suit, s.inventory.visor]),
  ("berserk", toJson s.inventory.berserk), ("computerMap", toJson s.inventory.computerMap),
  ("cards", toJson s.inventory.pickupState.cards.toArray),
  ("pendingWeapon", toJson s.inventory.pickupState.pendingWeapon.val),
  ("pickupBonus", toJson s.inventory.pickupState.bonus.toInt),
  ("strengthTics", toJson s.inventory.pickupState.powers[1].toInt),
  ("shadow", toJson s.inventory.pickupState.shadow),
  ("fixedColormap", toJson s.inventory.pickupState.fixedColormap.toInt),
  ("itemCount", toJson s.inventory.pickupState.items.toInt),
  ("collected", toJson s.collected), ("message", toJson s.message),
  ("sectorLights", toJson (s.map.sectors.map (·.light))),
  ("sectorSpecials", toJson (s.map.sectors.map (·.special))),
  ("lightThinkers", toJson (s.lights.map (fun t => Json.mkObj [
    ("sector", toJson t.sector), ("kind", toJson (reprStr t.kind)),
    ("count", toJson t.count.toInt), ("min", toJson t.minimum.toInt),
    ("max", toJson t.maximum.toInt), ("dark", toJson t.dark.toInt),
    ("direction", toJson t.direction.toInt)]))),
  ("floors", toJson (s.map.sectors.map (·.floor))),
  ("moverSounds", toJson (s.moverSounds.map (fun (sector,sound) =>
    Json.mkObj [("sector", toJson sector), ("sound", toJson (reprStr sound))]))),
  ("floorMovers", toJson (s.movers.map (fun m => Json.mkObj [
    ("sector", toJson m.sector), ("kind", toJson (reprStr m.kind)),
    ("status", toJson (reprStr m.status)), ("count", toJson m.count.toInt),
    ("low", fixedJson m.low), ("high", fixedJson m.high)]))),
  ("ceilings", toJson (s.map.sectors.map (·.ceiling))),
  ("specials", toJson (s.map.lines.map (·.special))),
  ("sideOffsets", toJson (s.map.sides.map (·.xOffset))),
  ("scrollers", toJson s.scrollers),
  ("textures", toJson (s.map.sides.map (fun side => #[side.upper, side.middle, side.lower]))),
  ("doorSounds", toJson (s.doorSounds.map (fun (sector,sound) =>
    Json.mkObj [("sector", toJson sector), ("sound", toJson (reprStr sound))]))),
  ("doors", toJson (s.doors.map (fun d => Json.mkObj [("sector", toJson d.sector),
    ("direction", toJson d.state.direction.toInt), ("wait", toJson d.state.countdown.toInt)])))
  ]

def Simulation.title (s : Simulation) (flying : Bool) : String :=
  let i := s.inventory
  let keys := (if i.blue then "B " else "") ++ (if i.red then "R " else "") ++ (if i.yellow then "Y" else "")
  s!"Lean DOOM | {if flying then "Fly" else "Walk"} | " ++
  (if i.health == 0 then "DEAD - R to restart" else if s.messageTicks > 0 then s.message else "Ctrl fire - Space use - F fly - R reset") ++
  s!" | Keys [{keys}] Health {i.health} Armor {i.armor} | Ammo {i.bullets}/{i.shells}/{i.rockets}/{i.cells}"

end Doom
