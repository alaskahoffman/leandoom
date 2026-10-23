import Std

namespace Doom.DosMemory

/-- Guest addresses, never host pointers. Unmapped bytes are unknown, not zero. -/
structure Region where
  base : UInt32
  bytes : ByteArray
  /-- None means every byte is supplied/known. Otherwise one byte per address
  marks initialized bytes. Uninitialized modeled RAM must not become black. -/
  known : Option ByteArray := none
  deriving Inhabited

structure Memory where
  regions : Array Region := #[]
  deriving Inhabited

def Memory.map (m : Memory) (base : UInt32) (bytes : ByteArray) : Except String Memory := do
  let start := base.toNat
  let stop := start + bytes.size
  if stop > 4294967296 then throw "DOS memory region wraps address space"
  if m.regions.any (fun r => start < r.base.toNat + r.bytes.size && r.base.toNat < stop) then
    throw "DOS memory regions overlap"
  return { regions := m.regions.push ⟨base, bytes, none⟩ }

def Memory.reserve (m : Memory) (base : UInt32) (size : Nat) : Except String Memory := do
  let m ← m.map base ⟨Array.replicate size 0⟩
  let i := m.regions.size-1
  return { regions := m.regions.modify i fun r =>
    { r with known := some ⟨Array.replicate size 0⟩ } }

def Memory.read8 (m : Memory) (address : UInt32) : Option UInt8 := do
  let r ← m.regions.find? fun r => r.base ≤ address && address.toNat - r.base.toNat < r.bytes.size
  let i := address.toNat-r.base.toNat
  if let some known := r.known then
    if known[i]? != some 1 then none else r.bytes[i]?
  else r.bytes[i]?

def Memory.read32 (m : Memory) (address : UInt32) : Except String UInt32 := do
  let mut result : UInt32 := 0
  for i in [:4] do
    let some b := m.read8 (address + i.toUInt32) | throw "unmapped DOS word read"
    result := result ||| (b.toUInt32 <<< (i*8).toUInt32)
  return result

def Memory.write8 (m : Memory) (address : UInt32) (value : UInt8) : Except String Memory := do
  let some i := m.regions.findIdx? (fun r => r.base ≤ address && address.toNat - r.base.toNat < r.bytes.size)
    | throw "unmapped DOS byte write"
  return { regions := m.regions.modify i fun r =>
    let offset := address.toNat-r.base.toNat
    { r with bytes := r.bytes.set! offset value
             known := r.known.map (fun k => k.set! offset 1) } }

def Memory.write32 (m : Memory) (address value : UInt32) : Except String Memory := do
  let mut m := m
  for i in [:4] do
    m ← m.write8 (address+i.toUInt32) (value >>> (i*8).toUInt32).toUInt8
  return m

def Memory.writeBytes (m : Memory) (address : UInt32) (bytes : ByteArray) : Except String Memory := do
  -- WAD copies are contiguous. Copy the range once, retaining sharing of other
  -- regions, instead of finding/copying the region for each payload byte.
  if let some i := m.regions.findIdx? (fun r => r.base ≤ address &&
      address.toNat-r.base.toNat+bytes.size ≤ r.bytes.size) then
    let knownBytes : ByteArray := ⟨Array.replicate bytes.size 1⟩
    return { regions := m.regions.modify i fun r =>
      let offset := address.toNat-r.base.toNat
      { r with bytes := bytes.copySlice 0 r.bytes offset bytes.size
               known := r.known.map (fun k => knownBytes.copySlice 0 k offset bytes.size) } }
  let mut m := m
  for i in [:bytes.size] do
    m ← m.write8 (address+i.toUInt32) bytes[i]!
  return m

/-- Conservatively forget payloads written by an as-yet unmodeled subsystem.
This is not a DOS write: it prevents stale known bytes from posing as new data. -/
def Memory.forget (m : Memory) (address : UInt32) (size : Nat) : Except String Memory := do
  let some i := m.regions.findIdx? (fun r => r.base ≤ address &&
      address.toNat-r.base.toNat+size ≤ r.bytes.size)
    | throw "unmapped DOS invalidation"
  return { regions := m.regions.modify i fun r =>
    let known := r.known.getD ⟨Array.replicate r.bytes.size 1⟩
    let unknown : ByteArray := ⟨Array.replicate size 0⟩
    { r with known := some (unknown.copySlice 0 known (address.toNat-r.base.toNat) size) } }

/-- The original 32-bit zone header is 32 bytes; a block header is 24 bytes.
All headers and owner cells live in the same modeled address space as payloads,
so a texture overread can observe them without any unsafe host-memory access. -/
structure Zone where
  memory : Memory
  base : UInt32
  deriving Inhabited

abbrev Action := StateT Zone (Except String)

private def read (address : UInt32) : Action UInt32 := do
  (← get).memory.read32 address

private def write (address value : UInt32) : Action Unit := fun z => do
  -- Consume the old state before updating RAM; get/set would keep an alias to
  -- the entire arena alive during each header write and force a full copy.
  let ⟨memory,base⟩ := z
  let memory ← memory.write32 address value
  return ((),⟨memory,base⟩)

def zoneId : UInt32 := 0x1d4a11

/-- Z_ClearZone, DOS code offset 0x39570. Deliberately does not clear tag/id or
payload bytes which the original routine leaves untouched. Size is preinstalled. -/
def clear : Action Unit := do
  let zone := (← get).base
  let size ← read zone
  if size.toNat < 56 || zone.toNat + size.toNat > 4294967296 then
    throw "invalid DOS zone size"
  let block := zone + 32
  write (zone+12) 1
  write (zone+8) zone
  write (zone+24) block
  write (zone+20) block
  write (zone+28) block
  write (block+4) 0
  write (block+16) (zone+4)
  write (block+20) (zone+4)
  write block (size-32)

/-- Caller supplies initial RAM, including any known nonzero/stale bytes. -/
def init (memory : Memory) (base : UInt32) (size : UInt32) : Except String Zone := do
  let memory ← memory.write32 base size
  return (← clear.run ⟨memory,base⟩).2

/-- Z_Free, DOS offset 0x39600. Free means user=0 (not tag=0). Small user values
are sentinels; only user > 0x100 is dereferenced. Payloads stay byte-for-byte. -/
def free (ptr : UInt32) : Action Unit := do
  let zone := (← get).base
  let mut block := ptr - 24
  if (← read (block+12)) != zoneId then throw "Z_Free: invalid ZONEID"
  let user ← read (block+4)
  if user > 256 then write user 0
  write (block+4) 0
  write (block+8) 0
  write (block+12) 0
  let prev ← read (block+20)
  if (← read (prev+4)) == 0 then
    write prev ((← read prev) + (← read block))
    let next ← read (block+16)
    write (prev+16) next
    write (next+20) prev
    if (← read (zone+28)) == block then write (zone+28) prev
    block := prev
  let next ← read (block+16)
  if (← read (next+4)) == 0 then
    write block ((← read block) + (← read next))
    let after ← read (next+16)
    write (block+16) after
    write (after+20) block
    if (← read (zone+28)) == next then write (zone+28) block

/-- Z_Malloc, DOS offset 0x39690, for nonnegative nonoverflowing sizes.
The bounded walk rejects corrupt lists instead of looping forever. -/
def alloc (requested : UInt32) (tag : Int32) (user : UInt32 := 0) : Action UInt32 := do
  if requested.toNat > 2147483616 then throw "DOS allocation size outside supported domain"
  let size := ((requested + 3) &&& 0xfffffffc) + 24
  let zone := (← get).base
  let mut base ← read (zone+28)
  let prev ← read (base+20)
  if (← read (prev+4)) == 0 then base := prev
  let mut rover := base
  let start ← read (base+20)
  let mut found := false
  let fuel := (← read zone).toNat / 24 + 2
  for _ in [:fuel] do
    if rover == start then throw "Z_Malloc: out of memory"
    if (← read (rover+4)) != 0 then
      if (← read (rover+8)).toInt32 < 100 then
        rover ← read (rover+16)
        base := rover
      else
        base ← read (base+20)
        free (rover+24)
        base ← read (base+16)
        rover ← read (base+16)
    else rover ← read (rover+16)
    if (← read (base+4)) == 0 && (← read base).toInt32 ≥ size.toInt32 then
      found := true
      break
  if !found then throw "Z_Malloc: corrupt block list"
  let extra := (← read base) - size
  if extra.toInt32 > 64 then
    let newblock := base + size
    write (newblock+4) 0
    write (newblock+8) 0
    write newblock extra
    write (newblock+20) base
    let next ← read (base+16)
    write (newblock+16) next
    write (next+20) newblock
    write (base+16) newblock
    write base size
  let result := base+24
  if user != 0 then
    write (base+4) user
    write user result
  else
    if tag ≥ 100 then throw "Z_Malloc: purgeable block requires owner"
    write (base+4) 2
  write (base+8) tag.toUInt32
  write (zone+28) (← read (base+16))
  write (base+12) zoneId
  return result

/-- Z_ChangeTag2, DOS offset 0x399b0; preserves the original >=0x100 gate,
which differs by one from Z_Free's owner-pointer test. -/
def changeTag (ptr : UInt32) (tag : Int32) : Action Unit := do
  let block := ptr-24
  if (← read (block+12)) != zoneId then throw "Z_ChangeTag: invalid ZONEID"
  if tag ≥ 100 && (← read (block+4)) < 256 then
    throw "Z_ChangeTag: purgeable block requires owner"
  write (block+8) tag.toUInt32

/-- Z_FreeTags, DOS offset 0x39780. Retain next before coalescing blocks. -/
def freeTags (low high : Int32) : Action Unit := do
  let zone := (← get).base
  let mut block ← read (zone+20)
  let fuel := (← read zone).toNat / 24 + 2
  for _ in [:fuel] do
    if block == zone+4 then return
    let next ← read (block+16)
    let user ← read (block+4)
    let tag := (← read (block+8)).toInt32
    if user != 0 && tag ≥ low && tag ≤ high then free (block+24)
    block := next
  throw "Z_FreeTags: corrupt block list"

end Doom.DosMemory
