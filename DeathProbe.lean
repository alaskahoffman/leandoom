import Doom.DeathData
import Doom.Replay
import Doom.App
open Doom Doom.Death

private def dump (body : Body) (world : World) : String := Id.run do
  let mut text := s!"{body.flags.toNat} {body.height.raw.toInt} {body.health} {body.state} {body.tics} {if body.removed then 1 else 0} {if world.automap then 1 else 0} {world.rng.play.toNat}"
  for player in world.players.toArray do
    text := text ++ s!" | {player.kills} {if player.dead then 1 else 0}"
    for n in player.frags.toArray do text := text ++ s!" {n}"
  text := text ++ " /"
  for event in world.events do
    text := text ++ match event with
    | .dropWeapon player => s!" weapon {player}"
    | .stopAutomap => " automap"
    | .state id => s!" state {id}"
    | .sound name global => s!" sound {name} {if global then 1 else 0}"
    | .drop editor => s!" drop {editor}"
    | .remove => " remove"
    | .explode => " explode"
  return text

private def fin (n : Int) : Except String (Fin 4) :=
  if h : n.toNat < 4 then .ok ⟨n.toNat,h⟩ else .error "invalid player"

private def run (body : Body) (world : World) (line : String) : Except String (Body × World) := do
  let op::args := (line.splitOn " ").filter (!·.isEmpty) | throw "empty command"
  let args ← args.mapM fun a => do
    let some n := a.toInt? | throw "invalid integer"
    if n < -2147483648 || n > 2147483647 then throw "integer outside int32"
    pure n
  match op,args with
  | "kill",[profile,kind,flags,health,height,player,source,net,auto,commercial,chex,seed,kills,frags] =>
    let some editor := #[0,3004,9,3002,3001,2035][profile.toNat]? | throw "bad metadata"
    let some info := Death.info editor | throw "no metadata"
    let playerIndex ← if player < 0 then pure none else some <$> fin player
    let sourceIndex ← if source < 0 then pure none else some <$> fin source
    let body : Body := {
      kind := kind.toNat, flags := (Int32.ofInt flags).toUInt32
      health := Int32.ofInt health, height := ⟨Int32.ofInt height⟩, info,
      player := playerIndex }
    let world : World := {
      source := if source == -2 then none else some sourceIndex
      netgame := net != 0, automap := auto != 0, commercial := commercial != 0, chex := chex != 0
      rng := { play := UInt8.ofNat seed.toNat }
      players := Vector.replicate 4 { kills := Int32.ofInt kills, frags := Vector.replicate 4 (Int32.ofInt frags) } }
    Death.kill frames body world
  | "tick",[] => Death.tick frames body { world with events := #[] }
  | _,_ => throw "invalid death command"

def main (args : List String) : IO Unit := do
  if args.head? == some "death-timing" || args.head? == some "death-return" then
    let [mode,path,output] := args | throw (IO.userError "bad death timing/return arguments")
    let mut rows : Array String := #[]
    for line in (← IO.FS.readFile path).splitOn "\n" do
      if line.trimAscii.isEmpty then continue
      let [tics,play,misc] := line.splitOn " " | throw (IO.userError "bad death-timing row")
      let some tics := tics.toInt? | throw (IO.userError "bad tics")
      let some play := play.toNat? | throw (IO.userError "bad play index")
      let some misc := misc.toNat? | throw (IO.userError "bad misc index")
      if tics < -2147483648 || tics > 2147483647 || play > 255 || misc > 255 then
        throw (IO.userError "death-timing input outside range")
      let body : Body := { tics := Int32.ofInt tics }
      let world : World := { rng := { play := UInt8.ofNat play, misc := UInt8.ofNat misc }, events := #[.state 158] }
      let (body,world) := Death.randomizeTics body world
      let (body,world) := if mode == "death-return" then Death.dropItem body world else (body,world)
      rows := rows.push s!"{body.tics} {world.rng.play.toNat} {world.rng.misc.toNat} {world.events.size}"
    IO.FS.writeFile output (String.intercalate "\n" rows.toList ++ "\n")
    return
  if let ["state-entry",path,output] := args then
    let mut rows : Array String := #[]
    for line in (← IO.FS.readFile path).splitOn "\n" do
      if line.trimAscii.isEmpty then continue
      let [state,seed] := line.splitOn " " | throw (IO.userError "bad state-entry row")
      let some state := state.toNat? | throw (IO.userError "bad state")
      let some seed := seed.toNat? | throw (IO.userError "bad seed")
      if (state != 158 && state != 165) || seed > 255 then throw (IO.userError "unsupported state-entry case")
      let some info := Death.info 0 | throw (IO.userError "missing player info")
      let body : Body := { kind := 0, health := -1, flags := info.flags, height := Fixed.ofInt 14, info }
      let world : World := { rng := { play := UInt8.ofNat seed } }
      let (body,world) ← checked (Death.setState frames body world state)
      let some frame := frames.find? (·.id == body.state) | throw (IO.userError "missing entry frame")
      rows := rows.push s!"{body.state} {body.tics} {frame.sprite} {frame.frame} {frame.next} {world.rng.play.toNat} {world.events.size}"
    IO.FS.writeFile output (String.intercalate "\n" rows.toList ++ "\n")
    return
  if let ["choice",path,output] := args then
    let mut rows : Array String := #[]
    for line in (← IO.FS.readFile path).splitOn "\n" do
      if line.trimAscii.isEmpty then continue
      let [hp,spawn,normal,extreme] := line.splitOn " " | throw (IO.userError "bad choice row")
      let some hp := hp.toInt? | throw (IO.userError "bad health")
      let some spawn := spawn.toInt? | throw (IO.userError "bad spawn health")
      let some normal := normal.toNat? | throw (IO.userError "bad normal state")
      let some extreme := extreme.toNat? | throw (IO.userError "bad extreme state")
      if hp < -2147483648 || hp > 2147483647 || spawn < -2147483648 || spawn > 2147483647 ||
          normal >= 4294967296 || extreme >= 4294967296 then throw (IO.userError "choice outside 32 bits")
      let info : Death.Info := { spawnHealth := Int32.ofInt spawn,normal,extreme,sound := "",flags := 0 }
      rows := rows.push (toString (Death.deathState (Int32.ofInt hp) info))
    IO.FS.writeFile output (String.intercalate "\n" rows.toList ++ "\n")
    return
  -- Test-only injection for deaths between integer map coordinates.
  let (args,position) ← match args with
    | "runtime-position"::x::y::z::rest => do
      let some x := x.toInt? | throw (IO.userError "bad x")
      let some y := y.toInt? | throw (IO.userError "bad y")
      let some z := z.toInt? | throw (IO.userError "bad z")
      pure ("runtime"::rest, some (x,y,z))
    | _ => pure (args,none)
  if let ["runtime",path,target,health,script,output] := args then
    let wad ← checked (Wad.parse (← IO.FS.readBinFile path))
    let map ← checked (Map.load wad.lumps "E1M1")
    let state ← checked (Simulation.spawn map true)
    let some target := target.toInt? | throw (IO.userError "bad target")
    let some health := health.toInt? | throw (IO.userError "bad health")
    if health > 0 || health < -2147483648 then throw (IO.userError "expected nonpositive int32 health")
    let state ← match position with
      | none => pure state
      | some (x,y,z) => do
        let id := target.toNat+1
        let mut scene ← checked (state.player.syncScene map)
        let some body := scene.things[id]? | throw (IO.userError "bad actor")
        scene ← checked (scene.unlinkThing id)
        scene := { scene with things := scene.things.set! id { body with
          x := ⟨Int32.ofInt x⟩, y := ⟨Int32.ofInt y⟩, z := ⟨Int32.ofInt z⟩ } }
        scene ← checked (scene.linkThing id map.sectorAt)
        pure { state with player := { state.player with scene := some scene } }
    let state ← if target < 0 then checked (({ state with inventory := { state.inventory with health := 0 } } : Simulation).killPlayer (Int32.ofInt health) none)
      else do
        let some index := state.actors.findIdx? (fun a => a.thing == target.toNat) | throw (IO.userError "target has no combat actor")
        checked (state.killActor index (Int32.ofInt health) (some (some 0)))
    let state ← checked (runScript state script)
    let some scene := state.player.scene | throw (IO.userError "missing scene")
    let drops := state.dropped.map fun index => Id.run do
      let body := scene.things[index+1]!
      return Lean.Json.mkObj [
        ("position",Lean.toJson (#[body.x,body.y,body.z].map (·.raw.toInt))),
        ("floor",Lean.toJson body.floor.raw.toInt),
        ("dropped",Lean.toJson (body.pickup.any (·.dropped))),
        ("blockLinks",Lean.toJson (scene.links.flatten.count (index+1))),
        ("sectorLinks",Lean.toJson (scene.sectorLinks.flatten.count (index+1)))]
    let json := if position.isSome then state.json.setObjVal! "dropBodies" (Lean.toJson drops) else state.json
    IO.FS.writeFile output (json.pretty ++ "\n")
    return
  let [path] := args | throw (IO.userError "usage: death-probe input.txt")
  let out ← IO.getStdout
  let mut body : Body := {}
  let mut world : World := {}
  for line in (← IO.FS.readFile path).splitOn "\n" do
    if line.trimAscii.isEmpty then continue
    match run body world line with
    | .error error => throw (IO.userError error)
    | .ok (next,state) => body := next; world := state; out.putStrLn (dump body world)
