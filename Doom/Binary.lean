namespace Doom.Binary

abbrev Parse := Except String

def require (condition : Bool) (message : String) : Parse Unit :=
  if condition then .ok () else .error message

def checkRange (bytes : ByteArray) (offset size : Nat) : Parse Unit :=
  require (offset ≤ bytes.size && size ≤ bytes.size - offset)
    s!"range {offset}+{size} exceeds {bytes.size} bytes"

def u16 (bytes : ByteArray) (offset : Nat) : Parse Nat := do
  checkRange bytes offset 2
  return bytes[offset]!.toNat + bytes[offset + 1]!.toNat * 256

def i16 (bytes : ByteArray) (offset : Nat) : Parse Int := do
  let n ← u16 bytes offset
  return if n ≥ 32768 then (Int.ofNat n) - 65536 else Int.ofNat n

def u32 (bytes : ByteArray) (offset : Nat) : Parse Nat := do
  checkRange bytes offset 4
  return bytes[offset]!.toNat + bytes[offset + 1]!.toNat * 256 +
    bytes[offset + 2]!.toNat * 65536 + bytes[offset + 3]!.toNat * 16777216

def name (bytes : ByteArray) (offset size : Nat) : Parse String := do
  checkRange bytes offset size
  let mut chars := []
  for i in [offset:offset + size] do
    let n := bytes[i]!.toNat
    if n == 0 then break
    chars := Char.ofNat n :: chars
  return (String.ofList chars.reverse).toUpper

def records (label : String) (bytes : ByteArray) (stride : Nat)
    (parse : ByteArray → Nat → Parse α) : Parse (Array α) := do
  require (stride > 0 && bytes.size % stride == 0)
    s!"{label}: {bytes.size} bytes is not a multiple of record size {stride}"
  let mut result := #[]
  for i in [:bytes.size / stride] do
    match parse bytes (i * stride) with
    | .ok value => result := result.push value
    | .error e => throw s!"{label}[{i}]: {e}"
  return result

end Doom.Binary
