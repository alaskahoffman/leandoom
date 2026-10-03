import Doom.App
import Doom.DemoTelemetry
open Doom

def main (args : List String) : IO UInt32 := do
  try
    let [mapName,path,script] := args | throw (IO.userError "demo-probe MAP WAD TICS:KEYS,...")
    let lumps ← loadWads [path]
    let map ← checked (Map.load lumps mapName)
    let start ← checked (Simulation.spawn map true (LevelSpecials.switchEpisode lumps))
    let state ← checked (runScript start script)
    IO.println (Demo.snapshot state).compress
    return 0
  catch e =>
    (← IO.getStderr).putStrLn s!"{e}"
    return 1
