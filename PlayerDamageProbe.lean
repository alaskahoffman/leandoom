import Doom.PlayerDamage
import Doom.PlayerAnim
import Doom.Death

open Doom

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "usage: player-damage-probe commands.txt")
  let stdout ← IO.getStdout
  for line in (← IO.FS.readFile path).splitOn "\n" do
    if line.trimAscii.isEmpty then continue
    let fields := line.splitOn " "
    let bookOnly := fields.head? == some "bookkeeping"
    let corpseOnly := fields.head? == some "corpse"
    let armorOnly := fields.head? == some "armor"
    let entryOnly := fields.head? == some "entry"
    let returnOnly := fields.head? == some "player-return"
    let painOnly := fields.head? == some "player-pain" || returnOnly
    let actorOnly := fields.head? == some "actor-health" || painOnly
    let healthOnly := fields.head? == some "entry-health" || actorOnly
    let values ← (if bookOnly || corpseOnly || armorOnly || entryOnly || healthOnly then fields.drop 1 else fields).toArray.mapM fun s =>
      match s.toInt? with
      | some n => pure (Int32.ofInt n)
      | none => throw (IO.userError "invalid fixture integer")
    if bookOnly then
      if values.size != 5 then throw (IO.userError "expected flags, netgame, kills, frags and player slot")
      let n := values[4]!.toInt.toNat
      if hi : n < 4 then
        let i : Fin 4 := ⟨n,hi⟩
        let body : Death.Body := {flags := values[0]!.toUInt32,player := some i}
        let world : Death.World := {netgame := (values[1]! != 0), players := Vector.replicate 4 { kills := values[2]!, frags := Vector.replicate 4 (values[3]!) }}
        let (body,world) := Death.bookkeeping body world
        stdout.putStrLn s!"{body.flags.toNat} {world.players[0].kills.toInt} {world.players[i].frags[i].toInt} {if world.players[i].dead then 1 else 0}"
        continue
      else throw (IO.userError "invalid player slot")
    if corpseOnly then
      if values.size != 2 then throw (IO.userError "expected flags and height")
      let body := Death.corpse {kind := 0,flags := values[0]!.toUInt32,height := ⟨values[1]!⟩}
      stdout.putStrLn s!"{body.flags.toNat} {body.height.raw.toInt}"
      continue
    if armorOnly then
      if values.size != 3 then throw (IO.userError "expected damage, armor and armor type")
      let (state,damage) := PlayerDamage.absorbArmor
        {armor := values[1]!,armorType := values[2]!} values[0]!
      stdout.putStrLn s!"{damage.toInt} {state.armor.toInt} {state.armorType.toInt}"
      continue
    if entryOnly || healthOnly then
      if values.size != (if returnOnly then 12 else if painOnly then 11 else if healthOnly then 10 else 8) then throw (IO.userError "expected damage, health, armor, type, shootable, god, invulnerability, baby")
      let v : PlayerDamage.State := {
        health := values[1]!,playerHealth := if healthOnly then values[8]! else values[1]!,
        damageCount := if healthOnly then values[9]! else 0,
        armor := values[2]!,armorType := values[3]!,shootable := values[4]! != 0,
        god := values[5]! != 0,invulnerable := values[6]! != 0,sectorSpecial := 5}
      let out := PlayerDamage.apply v values[0]! none false (values[7]! != 0) {play := if painOnly then UInt8.ofNat values[10]!.toUInt32.toNat else 0}
      if returnOnly then
        stdout.putStrLn s!"{if out.applied then 1 else 0} {(v.health-out.state.health).toInt} {out.state.armor.toInt} {out.state.armorType.toInt} {out.state.playerHealth.toInt} {out.state.damageCount.toInt} {out.state.health.toInt} {if out.killed then 1 else 0} {out.rng.play.toNat} {if out.pain then 1 else 0} {(out.reactionTime values[11]!).toInt}"
        continue
      if painOnly then
        stdout.putStrLn s!"{if out.applied then 1 else 0} {(v.health-out.state.health).toInt} {out.state.armor.toInt} {out.state.armorType.toInt} {out.state.playerHealth.toInt} {out.state.damageCount.toInt} {out.state.health.toInt} {if out.killed then 1 else 0} {out.rng.play.toNat} {if out.pain then 1 else 0}"
        continue
      if actorOnly then
        stdout.putStrLn s!"{if out.applied then 1 else 0} {(v.health-out.state.health).toInt} {out.state.armor.toInt} {out.state.armorType.toInt} {out.state.playerHealth.toInt} {out.state.damageCount.toInt} {out.state.health.toInt} {if out.killed then 1 else 0}"
        continue
      if healthOnly then
        stdout.putStrLn s!"{if out.applied then 1 else 0} {(v.health-out.state.health).toInt} {out.state.armor.toInt} {out.state.armorType.toInt} {out.state.playerHealth.toInt} {out.state.damageCount.toInt}"
        continue
      stdout.putStrLn s!"{if out.applied then 1 else 0} {(v.health-out.state.health).toInt} {out.state.armor.toInt} {out.state.armorType.toInt}"
      continue
    if values.size != 27 then throw (IO.userError "expected 27 damage fields")
    let n (i : Nat) := values[i]!
    let f (i : Nat) : Fixed := ⟨n i⟩
    let b (i : Nat) := n i != 0
    let state : PlayerDamage.State := {
      x := f 0, y := f 1, z := f 2, momx := f 3, momy := f 4, momz := f 5,
      health := n 6, playerHealth := n 7, armor := n 8, armorType := n 9,
      damageCount := n 10, shootable := b 11, skullFly := b 12, noClip := b 13,
      god := b 14, invulnerable := b 15, sectorSpecial := n 16 }
    let inflictor := if b 17 then some (⟨f 18,f 19,f 20⟩ : PlayerDamage.Inflictor) else none
    let result := PlayerDamage.apply state (n 21) inflictor (b 22) (b 23)
      { play := UInt8.ofNat (n 24).toUInt32.toNat }
    let s := result.state
    let bit (v : Bool) := if v then 1 else 0
    stdout.putStrLn s!"{s.momx.raw.toInt} {s.momy.raw.toInt} {s.momz.raw.toInt} {s.health.toInt} {s.playerHealth.toInt} {s.armor.toInt} {s.armorType.toInt} {s.damageCount.toInt} {result.rng.play.toNat} {bit result.applied} {bit result.killed} {bit result.pain}"
    let mut animation : PlayerAnim.State := ⟨(n 25).toInt.toNat,n 26⟩
    let mut trace := ""
    for _ in [:16] do
      let (next,sound) := PlayerAnim.tick animation
      animation := next
      trace := trace ++ s!" {animation.frame}:{animation.tics.toInt}:{bit sound}"
    stdout.putStrLn trace
