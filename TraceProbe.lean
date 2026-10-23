import Doom.App
import Doom.Trace
open Doom

private def parseCommand (line : String) : Except String Ticcmd := do
  let fields := line.splitOn " "
  let [f,s,a,b] ← fields.mapM (fun value => match value.toInt? with
    | some n => Except.ok n
    | none => Except.error "trace: expected integer command fields")
    | throw "trace: expected forward side angle buttons"
  if f < -127 || f > 127 || s < -128 || s > 127 || a < -32768 || a > 32512 || a % 256 != 0 || b < 0 || b > 255 then
    throw "trace: command outside vanilla demo encoding"
  return ⟨Int8.ofInt f,Int8.ofInt s,Int16.ofInt a,UInt8.ofInt b⟩

def main (args : List String) : IO UInt32 := do
  try
    let [mapName,wadPath,commandsPath] := args | throw (IO.userError "trace-probe MAP WAD COMMANDS")
    let wad ← checked (Wad.parse (← IO.FS.readBinFile wadPath))
    let lumps := wad.lumps
    let map ← checked (Map.load lumps mapName)
    let mut state ← checked (Simulation.spawn map true (LevelSpecials.switchEpisode lumps))
    let commands := (← IO.FS.readFile commandsPath).splitOn "\n" |>.filter (!·.isEmpty)
    let commands ← checked (commands.mapM parseCommand)
    IO.println (← checked (Trace.record state 0 none)).compress
    for h : i in [:commands.length] do
      let command := commands[i]
      state ← checked (state.tickCommand command)
      IO.println (← checked (Trace.record state (i+1) (some command))).compress
    return 0
  catch e =>
    (← IO.getStderr).putStrLn s!"{e}"
    return 1
