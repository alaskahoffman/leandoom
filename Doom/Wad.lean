import Doom.Binary

namespace Doom
open Binary

structure Lump where
  name : String
  bytes : ByteArray
  archive : Nat := 0
  deriving Inhabited

structure Wad where
  kind : String
  lumps : Array Lump

def Wad.parse (bytes : ByteArray) : Parse Wad := do
  checkRange bytes 0 12
  let kind ← name bytes 0 4
  require (kind == "IWAD" || kind == "PWAD") "expected IWAD or PWAD signature"
  let count ← u32 bytes 4
  let directory ← u32 bytes 8
  require (count < 2147483648 && directory < 2147483648) "negative WAD header field"
  checkRange bytes directory (count * 16)
  let mut lumps := #[]
  for i in [:count] do
    let base := directory + i * 16
    let offset ← u32 bytes base
    let size ← u32 bytes (base + 4)
    let lumpName ← name bytes (base + 8) 8
    require (size < 2147483648) s!"lump {i} ({lumpName}): negative size"
    -- Marker lumps have no payload; their offsets need not point into the file.
    if size > 0 then
      require (offset < 2147483648) s!"lump {i} ({lumpName}): negative offset"
      match checkRange bytes offset size with
      | .error e => throw s!"lump {i} ({lumpName}): {e}"
      | .ok _ => pure ()
    let payload := if size == 0 then ByteArray.empty else bytes.extract offset (offset + size)
    lumps := lumps.push ⟨lumpName, payload, 0⟩
  return ⟨kind, lumps⟩

/-- Last definition wins, including across IWAD + PWAD archives. -/
def findLump (lumps : Array Lump) (query : String) : Option Nat := Id.run do
  let query := query.toUpper
  for i in [:lumps.size] do
    let index := lumps.size - 1 - i
    if lumps[index]!.name == query then return some index
  return none

def isMapName (name : String) : Bool :=
  match name.toList with
  | ['E', e, 'M', m] => e.isDigit && m.isDigit
  | ['M', 'A', 'P', a, b] => a.isDigit && b.isDigit
  | _ => false

def mapNames (lumps : Array Lump) : Array String := Id.run do
  let mut names := #[]
  for lump in lumps do
    if isMapName lump.name && !names.contains lump.name then
      names := names.push lump.name
  return names

end Doom
