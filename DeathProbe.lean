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
  if let ["runtime",path,target,health,script,output] := args then
    let wad ← checked (Wad.parse (← IO.FS.readBinFile path))
    let map ← checked (Map.load wad.lumps "E1M1")
    let state ← checked (Simulation.spawn map true)
    let some target := target.toInt? | throw (IO.userError "bad target")
    let some health := health.toInt? | throw (IO.userError "bad health")
    if health > 0 || health < -2147483648 then throw (IO.userError "expected nonpositive int32 health")
    let state ← if target < 0 then checked (({ state with inventory := { state.inventory with health := 0 } } : Simulation).killPlayer (Int32.ofInt health) none)
      else do
        let some index := state.actors.findIdx? (fun a => a.thing == target.toNat) | throw (IO.userError "target has no combat actor")
        checked (state.killActor index (Int32.ofInt health) (some (some 0)))
    let state ← checked (runScript state script)
    IO.FS.writeFile output (state.json.pretty ++ "\n")
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
