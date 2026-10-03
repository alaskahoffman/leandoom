import Doom.Wad

namespace Doom

def checked (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error e => throw (IO.userError e)

def loadWads (paths : List String) : IO (Array Lump) := do
  if paths.isEmpty then throw (IO.userError "provide at least one WAD file")
  let mut lumps := #[]
  let mut archive := 0
  for path in paths do
    let bytes ← IO.FS.readBinFile path
    let wad ← checked ((Wad.parse bytes).mapError fun e => s!"{path}: {e}")
    IO.println s!"{path}: {wad.kind}, {wad.lumps.size} lumps, {bytes.size} bytes"
    lumps := lumps ++ wad.lumps.map (fun lump => { lump with archive := archive })
    archive := archive + 1
  return lumps

end Doom
