import Doom.App
import Doom.DosStartup
open Doom

def main (args : List String) : IO UInt32 := do
  try
    let [wad] := args | throw (IO.userError "dos-startup-probe WAD")
    let lumps := (← checked (Wad.parse (← IO.FS.readBinFile wad))).lumps
    let art ← checked (Art.load lumps)
    let map ← checked (Map.load lumps "E1M1")
    let sim ← checked (Simulation.spawn map true)
    let heap ← checked (DosHeap.startup art sim {} true)
    for e in heap.events do
      IO.println s!"{e.op} {e.size} {e.tag.toInt} {e.owner} {e.address}"
    return 0
  catch e =>
    (← IO.getStderr).putStrLn e.toString
    return 1
