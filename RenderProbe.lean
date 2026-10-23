import Doom.App
import Doom.CombatView
import Doom.Trace
open Doom

/-- Replay ordinary demo commands, then present exactly once (fuzz phase zero). -/
def main (args : List String) : IO UInt32 := do
  try
    let [wadPath,commandsPath,imagePath,statePath] := args
      | throw (IO.userError "render-probe WAD COMMANDS IMAGE STATE")
    let lumps := (← checked (Wad.parse (← IO.FS.readBinFile wadPath))).lumps
    let map ← checked (Map.load lumps "E1M1")
    let assets ← checked (Assets.load lumps map true true)
    let mut state ← checked (Simulation.spawn map true (LevelSpecials.switchEpisode lumps))
    for line in (← IO.FS.readFile commandsPath).splitOn "\n" do
      if line.isEmpty then continue
      let [f,s,a,b] ← checked (line.splitOn " " |>.mapM fun v => match v.toInt? with
        | some n => Except.ok n
        | none => Except.error "invalid command integer")
        | throw (IO.userError "invalid command fields")
      if f < -127 || f > 127 || s < -128 || s > 127 || a < -32768 || a > 32512 || a % 256 != 0 || b < 0 || b > 255 then
        throw (IO.userError "command outside vanilla encoding")
      state ← checked (state.tickCommand ⟨Int8.ofInt f,Int8.ofInt s,Int16.ofInt a,UInt8.ofInt b⟩)
    IO.FS.writeFile statePath (← checked (Trace.snapshot state)).compress
    IO.FS.writeBinFile imagePath (ppm (← checked (state.frame assets)))
    return 0
  catch e =>
    (← IO.getStderr).putStrLn s!"{e}"
    return 1
