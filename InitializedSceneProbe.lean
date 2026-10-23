import Doom.App
import Doom.Proofs.InitializedSceneRegions
open Doom Lean
open Doom.Verification.X86Memory Doom.Proofs.InitializedScene

private def memory (bytes : ByteArray) : Memory := fun a => BitVec.ofNat 8 bytes[a.toNat]!.toNat

def main (args : List String) : IO UInt32 := do
  try
    let (wad,rawPath,canonicalPath,inputPath) ← match args with
      | [w,r,c,i] => pure (w,r,c,i)
      | _ => throw (IO.userError "initialized-scene-probe WAD RAW CANONICAL INPUT.json")
    let lumps := (← checked (Wad.parse (← IO.FS.readBinFile wad))).lumps
    let bytes ← IO.FS.readBinFile rawPath
    let canonical ← IO.FS.readBinFile canonicalPath
    let input ← checked (Json.parse (← IO.FS.readFile inputPath))
    let dataBase ← checked (input.getObjValAs? Nat "dataBase")
    let stackLo ← checked (input.getObjValAs? Nat "guardStackLo")
    let stackHi ← checked (input.getObjValAs? Nat "guardStackHi")
    let base ← checked (input.getObjValAs? Nat "blockmap")
    let lines ← checked (input.getObjValAs? Nat "lines")
    let links ← checked (input.getObjValAs? Nat "links")
    let words ← checked (input.getObjValAs? (Array Nat) "words")
    let pointers ← checked (input.getObjValAs? (Array Nat) "pointers")
    unless canonical.size+dataBase==bytes.size do throw (IO.userError "canonical extent")
    unless dataBase < 2^32 && base < 2^32 && lines < 2^32 && links < 2^32 &&
        pointers.all (· < 2^32) && words.all (· < 65536) do
      throw (IO.userError "oversized source literal; refusing truncation")
    let d : Input := ⟨BitVec.ofNat 32 base,BitVec.ofNat 32 lines,BitVec.ofNat 32 links,
      words,pointers.map (BitVec.ofNat 32)⟩
    let raw := memory bytes
    let m := memory canonical
    let (_,state,_) ← checked (Engine.start lumps true false)
    let scene ← checked (Proofs.InitializedE1M1.aimingScene state)
    let failures := (List.range 828).filter fun i =>
      !(cellCheck raw m dataBase bytes.size d scene i (fun _ => Fixed.ofInt 0))
    let readCount := (mapReads d).length + ((List.range 828).map fun i =>
      (cellReads m d (cell m d scene i (fun _ => Fixed.ofInt 0))).length).sum
    let output := Json.mkObj [
      ("sceneCheck",toJson (sceneCheck raw m dataBase bytes.size scene d)),
      ("layoutCheck",toJson (Proofs.InitializedSceneRegions.check ⟨stackLo,stackHi⟩ m d scene)),
      ("startCheck",toJson (startCheck lumps raw m dataBase bytes.size d)),
      ("mapCheck",toJson (Proofs.InitializedAddress.check raw m dataBase bytes.size (mapReads d))),
      ("cells",toJson scene.grid.cells.size),("lines",toJson scene.lines.size),
      ("readOccurrences",toJson readCount),("failedCells",toJson failures),
      ("previousHeap",toJson (state.previous.bind (·.dosHeap)).isSome)]
    (← IO.getStdout).putStrLn output.compress
    return 0
  catch e =>
    (← IO.getStderr).putStrLn s!"initialized scene: {e}"
    return 1
