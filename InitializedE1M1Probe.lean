import Doom.App
import Doom.Engine
import Doom.Proofs.InitializedE1M1
open Doom Lean

private def fix (v : Fixed) : Json := toJson v.raw.toInt
private def actor (t : Collision.SolidThing) : Json := Json.mkObj [
  ("kind",toJson t.kind),("x",fix t.x),("y",fix t.y),("z",fix t.z),
  ("radius",fix t.radius),("height",fix t.height),("floor",fix t.floor),
  ("ceiling",fix t.ceiling),("solid",toJson t.solid),("shootable",toJson t.shootable),
  ("removed",toJson t.removed),("noBlockmap",toJson t.moveFlags.noBlockmap)]
private def line (l : Collision.Line) : Json := Json.mkObj [
  ("x",fix l.x),("y",fix l.y),("dx",fix l.dx),("dy",fix l.dy),
  ("front",toJson #[l.front.floor.raw.toInt,l.front.ceiling.raw.toInt]),
  ("back",toJson (l.back.map fun h => #[h.floor.raw.toInt,h.ceiling.raw.toInt])),
  ("twoSided",toJson l.twoSided),("blocking",toJson l.blocking)]

def main (args : List String) : IO UInt32 := do
  try
    let (path,input) ← match args with
      | [path] => pure (path,none)
      | [path,input] => pure (path,some input)
      | _ => throw (IO.userError "initialized-e1m1-probe WAD [CAPTURED-INPUT.json]")
    let lumps := (← checked (Wad.parse (← IO.FS.readBinFile path))).lumps
    let (_,state,_) ← checked (Engine.start lumps true false)
    -- Same expression as the private production Combat.combatScene adapter.
    let scene ← checked (state.game.player.syncScene state.game.map)
    let record ← checked (Trace.record state.game 0 none)
    let mut checks : List (String × Json) := []
    if let some input := input then
      let data ← checked (Json.parse (← IO.FS.readFile input))
      let values ← checked (data.getObjValAs? (Array Nat) "actor")
      let stamps ← checked (data.getObjValAs? (Array Nat) "stamps")
      let epoch ← checked (data.getObjValAs? Nat "epoch")
      unless values.size == 4 do throw (IO.userError "expected four captured actor words")
      let words : Proofs.InitializedE1M1.ActorWords :=
        ⟨BitVec.ofNat 32 values[0]!,BitVec.ofNat 32 values[1]!,
          BitVec.ofNat 32 values[2]!,BitVec.ofNat 32 values[3]!⟩
      checks := [("engineCheck",toJson (Proofs.InitializedE1M1.engineCheck state words)),
        ("startCheck",toJson (Proofs.InitializedE1M1.startCheck lumps words)),
        ("stampCheck",toJson (Proofs.InitializedE1M1.stampCheck stamps epoch))]
    let json := Json.mkObj (checks ++ [
      ("boundary",toJson "Engine.start true false, before advance/afterPresent"),
      ("record",record),("width",toJson scene.grid.width),("height",toJson scene.grid.height),
      ("origin",toJson #[scene.grid.origin.x,scene.grid.origin.y]),
      ("vanillaOffsets",toJson scene.grid.vanillaOffsets),
      ("cells",toJson scene.grid.cells),("links",toJson scene.links),
      ("things",Json.arr (scene.things.map actor)),("lines",Json.arr (scene.lines.map line)),
      ("phase",toJson state.phase.toNat),
      ("previousHeap",toJson (state.previous.bind (·.dosHeap)).isSome),
      ("spawnThings",Json.arr (state.game.map.things.map fun t =>
        toJson #[t.position.x,t.position.y,Int.ofNat t.angle,Int.ofNat t.kind,Int.ofNat t.flags]))])
    (← IO.getStdout).putStrLn json.compress
    return 0
  catch e =>
    (← IO.getStderr).putStrLn s!"initialization: {e}"
    return 1
