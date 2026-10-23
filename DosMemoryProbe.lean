import Doom.DosCache
import Doom.App
import Doom.Render
open Doom DosMemory

private def number (s : String) : IO UInt32 := do
  let some n := s.toNat? | throw (IO.userError "expected unsigned decimal word")
  if n > 4294967295 then throw (IO.userError "word exceeds 32 bits")
  return n.toUInt32

/-- Offline allocator/guest-memory diagnostic. Never reads the running reference. -/
def main (args : List String) : IO UInt32 := do
  try
    let [path] := args | throw (IO.userError "dos-memory-probe COMMANDS")
    let mut z : Zone := default
    let mut cache : Option LumpCache := none
    let output ← IO.getStdout
    for line in (← IO.FS.readFile path).splitOn "\n" do
      if line.isEmpty then continue
      let words := line.splitOn " "
      let result ← match words with
        | ["map",base,path] => do
          let memory ← checked (z.memory.map (← number base) (← IO.FS.readBinFile path))
          z := { z with memory }
          pure (Except.ok (0,z))
        | ["unknown",base,size] => do
          let memory ← checked (z.memory.reserve (← number base) (← number size).toNat)
          pure (Except.ok (0,{ z with memory }))
        | ["zone",base,size] => do
          pure ((DosMemory.init z.memory (← number base) (← number size)).map fun next => (0,next))
        | ["clear"] => pure ((clear.run z).map fun (_,next) => (0,next))
        | ["alloc",size,tag,user] => (alloc (← number size) (← number tag).toInt32 (← number user)).run z |> pure
        | ["free",ptr] => pure (((free (← number ptr)).run z).map fun (_,next) => (0,next))
        | ["tag",ptr,tag] => pure (((changeTag (← number ptr) (← number tag).toInt32).run z).map fun (_,next) => (0,next))
        | ["tags",low,high] => pure (((freeTags (← number low).toInt32 (← number high).toInt32).run z).map fun (_,next) => (0,next))
        | ["write",addr,value] => do
          let memory ← checked (z.memory.write32 (← number addr) (← number value))
          pure (Except.ok (0,{ z with memory }))
        | ["load",addr,path] => do
          let memory ← checked (z.memory.writeBytes (← number addr) (← IO.FS.readBinFile path))
          pure (Except.ok (0,{ z with memory }))
        | ["forget",addr,size] => do
          let memory ← checked (z.memory.forget (← number addr) (← number size).toNat)
          pure (Except.ok (0,{ z with memory }))
        | ["read",addr] => pure ((z.memory.read32 (← number addr)).map fun value => (value,z))
        | ["cache",cells,count] => do
          match LumpCache.create z (← number cells) (← number count).toNat with
          | .error e => pure (Except.error e)
          | .ok c =>
            cache := some c
            pure (Except.ok (c.cells,c.zone))
        | ["lump",index,tag,path] => do
          let some c := cache | throw (IO.userError "create cache first")
          match ({ c with zone := z }).load (← number index).toNat (← IO.FS.readBinFile path) (← number tag).toInt32 with
          | .error e => pure (Except.error e)
          | .ok (address,c) =>
            cache := some c
            pure (Except.ok (address,c.zone))
        | ["sample",addr,offset,row] => do
          let source : ColumnSource := ⟨ByteArray.empty,(← number offset).toNat,true,some (← number addr),none⟩
          pure (match source.sample (← number row).toNat (some z.memory) with
            | some value => Except.ok (value.toUInt32,z)
            | none => Except.error "unmapped guest sample")
        | ["drawpatch",addr,path,u,scale,mid,step,dest] => do
          let patch ← checked (Patch.decode (← IO.FS.readBinFile path))
          let patch := patch.atDosAddress (← number addr)
          let palette : ByteArray := ⟨(Array.range 768).map (fun i => (i/3).toUInt8)⟩
          let maps : ByteArray := ⟨(Array.range (256*32)).map (fun i => i.toUInt8)⟩
          let art : Art := {
            palettes := palette, colormaps := maps, lumps := #[], pnames := #[]
            definitions := {}, dosMemory := some z.memory }
          let frame : IndexedFrame := { viewHeight := 168, indices := ⟨Array.replicate 64000 77⟩ }
          let frame := drawPatchColumn frame art patch.image 0 (← number u).toNat
            (← number scale).toInt32 (← number mid).toInt32 (← number step).toInt32 (-1) 168 (some 0)
          IO.FS.writeBinFile dest frame.indices
          pure (Except.ok (0,z))
        | ["dump",path] => do
          let mut bytes := ByteArray.empty
          for r in z.memory.regions do bytes := bytes ++ r.bytes
          IO.FS.writeBinFile path bytes
          pure (Except.ok (0,z))
        | _ => throw (IO.userError s!"unknown memory command: {line}")
      match result with
      | .ok (value,next) =>
        z := next
        output.putStrLn s!"ok {value}"
      | .error e => output.putStrLn s!"error {e}"
    return 0
  catch e =>
    (← IO.getStderr).putStrLn s!"DOS memory probe: {e}"
    return 1
