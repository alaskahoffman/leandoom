import Doom.Automap
import Doom.App
import Doom.Render
import Doom.Replay
import Doom.CombatView
import Doom.Audio.Runtime

open Doom Lean

private def usage : String :=
  "Lean DOOM — WAD textured viewer\n\n" ++
  "  lean-doom render-audio <map> <ticks:keys,...> <output.wav> <base.wad> [patch.wad ...]\n" ++
  "  lean-doom inspect <base.wad> [patch.wad ...]\n" ++
  "  lean-doom validate <base.wad> [patch.wad ...]\n" ++
  "  lean-doom map <E1M1|MAP01> <output.svg> <base.wad> [patch.wad ...]\n" ++
  "  lean-doom render <map> <output.ppm> <base.wad> [patch.wad ...]\n" ++
  "  lean-doom render-at <map> <output.ppm> <x> <y> <z> <degrees> <base.wad> [patch.wad ...]\n\n" ++
  "  lean-doom render-flat / render-flat-at: same arguments, diagnostic colors\n" ++
  "  lean-doom simulate <map> <ticks:keys,...> <output.json> <base.wad> [patch.wad ...]\n" ++
  "  lean-doom render-sim <map> <ticks:keys,...> <output.ppm> <base.wad> [patch.wad ...]\n" ++
  "  lean-doom combat / render-combat: simulation scripts with pistol and enemy AI\n" ++
  "  lean-doom walk <map> <ticks> <keymask> <base.wad> [patch.wad ...]\n" ++
  "  lean-doom asset <texture|patch|flat> <name> <output.ppm> <base.wad> [patch.wad ...]\n\n" ++
  "Later archives override earlier lumps. Vanilla DOOM map format only.\n"

private def coordinate (text : String) : IO Int := do
  let some n := text.toInt? | throw (IO.userError s!"invalid integer: {text}")
  if n < -32768 || n > 32767 then throw (IO.userError "coordinate/angle must be in -32768..32767")
  return n

private def saveFrame (m : Doom.Map) (camera : Camera) (output : String) (assets : Option Assets) : IO Unit := do
  if !output.toLower.endsWith ".ppm" then throw (IO.userError "frame output must have a .ppm extension")
  IO.FS.writeBinFile output (ppm (render m camera assets))
  IO.println s!"Wrote 320×200 frame to {output} (camera {camera.x.toFloat}, {camera.y.toFloat}, {camera.z.toFloat})"

private def summary (m : Doom.Map) : String :=
  s!"{m.name}: {m.vertices.size} vertices, {m.lines.size} linedefs, {m.sides.size} sidedefs, " ++
  s!"{m.sectors.size} sectors, {m.things.size} things, {m.segs.size} segs, " ++
  s!"{m.subsectors.size} subsectors, {m.nodes.size} BSP nodes, " ++
  s!"blockmap {m.blockmap.width}×{m.blockmap.height}"

def main (args : List String) : IO UInt32 := do
  try
    let flatMode := args.head? == some "render-flat" || args.head? == some "render-flat-at"
    let args := match args with
      | "render-flat" :: rest => "render" :: rest
      | "render-flat-at" :: rest => "render-at" :: rest
      | _ => args
    match args with
    | ["--help"] | ["-h"] | [] => IO.print usage
    | "render-audio" :: name :: script :: output :: paths =>
      if !output.toLower.endsWith ".wav" then throw (IO.userError "audio output must be .wav")
      let lumps ← loadWads paths
      let map ← checked (Doom.Map.load lumps name)
      let (initial,effects) ← checked (Audio.Playback.load lumps name)
      let mut playback := initial
      let mut state ← checked (Simulation.spawn map true (LevelSpecials.switchEpisode lumps))
      state := { state with audio := some effects }
      let mut pcm := ByteArray.empty
      let mut trace : Array Lean.Json := #[]
      let mut count := 0
      for command in script.splitOn "," do
        let [duration,mask] := command.splitOn ":" | throw (IO.userError "audio script: expected ticks:keymask")
        let some ticks := duration.toNat? | throw (IO.userError "audio script: invalid ticks")
        let some keys := mask.toNat? | throw (IO.userError "audio script: invalid keys")
        count := count+ticks
        if count > 10000 || keys > 131071 then throw (IO.userError "audio script: exceeds bounds")
        for _ in [:ticks] do
          let reset := keyDown keys.toUInt32 1024 && !state.restartHeld
          state := state.tick keys.toUInt32
          if let some error := state.physicsError then throw (IO.userError error)
          if reset then playback := initial
          let (block,next,newState) ← checked (playback.render state)
          state := newState; playback := next; pcm := pcm ++ block
          trace := trace.push (Lean.Json.mkObj [("tick",toJson state.ticks),("sounds",toJson (state.audioEvents.map (·.name)))])
      IO.FS.writeBinFile output (Audio.wav pcm)
      IO.FS.writeFile (output ++ ".json") (Lean.Json.mkObj [("state",state.json),("trace",toJson trace),("frames",toJson (pcm.size/4)),("musicLoops",toJson playback.music.loops)]).pretty
      IO.println s!"Wrote {pcm.size/4} stereo frames at 44100 Hz to {output}"
    | "inspect" :: paths =>
      let lumps ← loadWads paths
      let maps := mapNames lumps
      IO.println s!"Map markers ({maps.size}): {String.intercalate ", " maps.toList}"
    | "validate" :: paths =>
      let lumps ← loadWads paths
      let maps := mapNames lumps
      if maps.isEmpty then throw (IO.userError "no vanilla map markers found")
      let mut failures := 0
      for name in maps do
        match Doom.Map.load lumps name with
        | .ok m => IO.println (summary m)
        | .error e =>
          (← IO.getStderr).putStrLn s!"{name}: {e}"
          failures := failures + 1
      IO.println s!"Validated {maps.size - failures}/{maps.size} maps"
      if failures > 0 then return 1
    | "map" :: name :: output :: paths =>
      if !(output.toLower.endsWith ".svg") then
        throw (IO.userError "automap output must have a .svg extension")
      let lumps ← loadWads paths
      let m ← checked (Doom.Map.load lumps name)
      IO.FS.writeFile output m.toSvg
      IO.println (summary m)
      IO.println s!"Wrote {output}"
    | "render" :: name :: output :: paths =>
      let lumps ← loadWads paths
      let m ← checked (Doom.Map.load lumps name)
      let assets ← if flatMode then pure none else some <$> checked (Assets.load lumps m)
      saveFrame m (← checked (Camera.spawn m)) output assets
    | "render-at" :: name :: output :: x :: y :: z :: angle :: paths =>
      let camera : Camera := ⟨Fixed.ofInt (← coordinate x), Fixed.ofInt (← coordinate y),
        Fixed.ofInt (← coordinate z), Angle.ofDegrees (← coordinate angle)⟩
      let lumps ← loadWads paths
      let m ← checked (Doom.Map.load lumps name)
      let assets ← if flatMode then pure none else some <$> checked (Assets.load lumps m)
      saveFrame m camera output assets
    | "walk" :: name :: ticks :: keys :: paths =>
      let some ticks := ticks.toNat? | throw (IO.userError "invalid tick count")
      let some keys := keys.toNat? | throw (IO.userError "invalid key mask")
      if ticks > 10000 || keys > 1023 then throw (IO.userError "walk: maximum 10000 ticks, keymask 0..1023")
      let map ← checked (Doom.Map.load (← loadWads paths) name)
      let mut player ← checked (Player.spawn map)
      for _ in [:ticks] do player ← checked (player.tick map keys.toUInt32)
      IO.println s!"position {player.camera.x.toFloat} {player.camera.y.toFloat} {player.feet} {player.velocityZ}"
    | "asset" :: kind :: name :: output :: paths =>
      if !output.toLower.endsWith ".ppm" then throw (IO.userError "asset output must have a .ppm extension")
      let art ← checked (Art.load (← loadWads paths))
      let texture ← checked <| match kind with
        | "texture" => (art.texture name).map Prod.fst
        | "patch" => (art.patch name).map (·.image)
        | "flat" => art.flat name
        | _ => .error "asset kind must be texture, patch, or flat"
      IO.FS.writeBinFile output (art.texturePpm texture)
      IO.println s!"Wrote {texture.width}×{texture.height} {kind} {name} to {output}"
    | command :: name :: script :: output :: paths =>
      if #["simulate", "render-sim", "combat", "render-combat"].contains command then
        let combat := command == "combat" || command == "render-combat"
        let exportJson := command == "simulate" || command == "combat"
        let expected := if exportJson then ".json" else ".ppm"
        if !output.toLower.endsWith expected then throw (IO.userError s!"output must end in {expected}")
        let lumps ← loadWads paths
        let original ← checked (Doom.Map.load lumps name)
        let state ← checked (runScript (← checked (Simulation.spawn original combat (LevelSpecials.switchEpisode lumps))) script)
        if exportJson then IO.FS.writeFile output (state.json.pretty ++ "\n")
        else
          let assets ← checked (Assets.load lumps original true combat)
          IO.FS.writeBinFile output (ppm (← checked (state.frame assets)))
        IO.println s!"Wrote {output} at tick {state.ticks}: {state.message}"
      else
        (← IO.getStderr).putStr usage
        return 2
    | _ =>
      (← IO.getStderr).putStr usage
      return 2
    return 0
  catch e =>
    (← IO.getStderr).putStrLn s!"error: {e}"
    return 1
