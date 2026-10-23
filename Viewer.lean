import Doom.App
import Doom.Replay
import Doom.CombatView
import Doom.Platform
import Doom.Audio.Runtime
import Doom.DemoTelemetry

open Doom

private def usage : String :=
  "Usage: lean-doom-viewer [--no-audio] [--telemetry PATH] [--frames N] <E1M1|MAP01> <base.wad> [patch.wad ...]"

private def runViewer (mapName : String) (paths : List String) (limit : Nat) (audioEnabled : Bool := true) (telemetry : Option String := none) : IO Unit := do
  let lumps ← loadWads paths
  let map ← checked (Doom.Map.load lumps mapName)
  let assets ← checked (Assets.load lumps map true true)
  let start ← checked (Simulation.spawn map true (LevelSpecials.switchEpisode lumps))
  let playback ← if audioEnabled then some <$> checked (Audio.Playback.load lumps mapName) else pure none
  let start := { start with audio := playback.map (·.2) }
  let mut playback := playback.map (·.1)
  Platform.openWindow frameWidth.toUInt32 frameHeight.toUInt32
  try
    if audioEnabled then
      Platform.openAudio
      Platform.queueAudio (ByteArray.mk (Array.replicate (Audio.framesPerTic*4*3) 0))
    IO.println "1 fist · 2 pistol · 3 shotgun · Ctrl / left click: fire · Space: use · WASD move · arrows turn · Shift fast · F toggle free camera · Q/E fly down/up · R reset · Esc quit"
    let mut state := start
    let mut camera := start.player.camera
    let mut flying := false
    let mut previousTitle := ""
    let mut priorKeys : UInt32 := 0
    let mut accumulator := 0.0
    let mut previous ← Platform.seconds
    let mut fuzzPhase : Fuzz.Phase := 0
    let mut previousFrame : Option IndexedFrame := none
    let mut count := 0
    let begin := previous
    let mut lastSnapshot := previous - 1
    repeat
      let keys ← Platform.poll
      if keyDown keys 1 then break
      let now ← Platform.seconds
      let elapsed := max 0 (min 0.25 (now - previous))
      previous := now
      if keyDown keys 2048 && !keyDown priorKeys 2048 then
        flying := !flying
        -- Return to the last valid walking position when leaving inspection mode.
        camera := state.player.camera
        accumulator := 0
        IO.println (if flying then "Free camera" else "Walking")
      if keyDown keys 1024 && !keyDown priorKeys 1024 then
        state := { state.restart with restartHeld := true }
        -- ST_Start requests a full widget refresh on the next presentation.
        previousFrame := previousFrame.map (fun f => { f with statusWidgets := none })
        if let some p := playback then
          playback := some { p with music := p.initial }
          Platform.clearAudio
          Platform.queueAudio (ByteArray.mk (Array.replicate (Audio.framesPerTic*4*3) 0))
        camera := state.player.camera
        accumulator := 0
      accumulator := accumulator + elapsed
      for _ in [:9] do
        if accumulator < 1.0 / 35.0 then break
        state := state.tick keys (!flying)
        if let some error := state.physicsError then throw (IO.userError error)
        if let some p := playback then
          let (pcm,p,next) ← checked (p.render state)
          state := next
          playback := some p
          Platform.queueAudio pcm
        accumulator := accumulator - 1.0 / 35.0
      if flying then camera := camera.move keys elapsed
      else camera := state.player.camera
      let title := state.title flying
      if title != previousTitle then
        Platform.setTitle title
        previousTitle := title
      priorKeys := keys
      if let some path := telemetry then
        if now - lastSnapshot ≥ 0.05 then
          Demo.writeSnapshot path (Demo.snapshot state flying keys)
          lastSnapshot := now
      let frame ← checked (state.drawIndexedFrame assets (if flying then some camera else none) fuzzPhase previousFrame)
      fuzzPhase := frame.phase
      Platform.present frame.rgb
      previousFrame := some frame
      count := count + 1
      if limit > 0 && count ≥ limit then break
    let elapsed := (← Platform.seconds) - begin
    IO.println s!"Presented {count} frames in {elapsed} seconds"
  finally
    Platform.closeWindow
    if let some path := telemetry then
      Demo.writeSnapshot path (Lean.Json.mkObj [("schema", Lean.toJson (1 : Nat)), ("status", Lean.toJson "stopped")])

def main (args : List String) : IO UInt32 := do
  try
    let mut audioEnabled := true
    let mut telemetry : Option String := none
    let mut limit := 0
    let mut positional := []
    let mut remaining := args
    while !remaining.isEmpty do
      match remaining with
      | "--no-audio" :: rest => audioEnabled := false; remaining := rest
      | "--telemetry" :: path :: rest => telemetry := some path; remaining := rest
      | "--frames" :: n :: rest =>
        let some count := n.toNat? | throw (IO.userError "--frames requires a positive integer")
        if count == 0 then throw (IO.userError "--frames must be positive")
        limit := count
        remaining := rest
      | "--help" :: _ | "-h" :: _ => IO.println usage; return 0
      | arg :: rest =>
        if arg.startsWith "--" then throw (IO.userError s!"unknown or incomplete option: {arg}")
        positional := positional ++ [arg]
        remaining := rest
      | [] => pure ()
    match positional with
    | map :: paths => runViewer map paths limit audioEnabled telemetry
    | [] => IO.println usage; return 2
    return 0
  catch e =>
    (← IO.getStderr).putStrLn s!"error: {e}"
    return 1
