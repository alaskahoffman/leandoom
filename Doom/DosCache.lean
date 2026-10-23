import Doom.DosMemory

namespace Doom.DosMemory

/-- DOS W_CacheLumpNum ownership: the zone writes the payload address into a
32-bit cell and clears that cell when a cache block is purged. Resource bytes
come from the caller's WAD, never from a running comparison reference. -/
structure LumpCache where
  zone : Zone
  cells : UInt32
  count : Nat
  deriving Inhabited

/-- W_InitMultipleFiles obtains lumpcache from the C runtime heap, outside the
zone. Its mapped address must be supplied by the startup model; allocating the
directory inside the zone would shift every subsequent texture allocation. -/
def LumpCache.create (zone : Zone) (cells : UInt32) (count : Nat) : Except String LumpCache := do
  if cells.toNat + count*4 > 4294967296 then throw "DOS lump directory wraps address space"
  let mut memory := zone.memory
  for i in [:count] do memory ← memory.write32 (cells + (i*4).toUInt32) 0
  return ⟨{ zone with memory },cells,count⟩

def LumpCache.cell (cache : LumpCache) (index : Nat) : Except String UInt32 := do
  if index ≥ cache.count then throw "DOS lump index out of range"
  return cache.cells + (index*4).toUInt32

def LumpCache.address (cache : LumpCache) (index : Nat) : Except String (Option UInt32) := do
  let address ← cache.zone.memory.read32 (← cache.cell index)
  return if address == 0 then none else some address

/-- A hit changes only the tag; a miss allocates and copies the complete lump.
Caller order is significant: this layer does not guess the game's cache order. -/
def LumpCache.load (cache : LumpCache) (index : Nat) (bytes : ByteArray)
    (tag : Int32 := 101) : Except String (UInt32 × LumpCache) := do
  let cell ← cache.cell index
  if let some address ← cache.address index then
    let (_,zone) ← (changeTag address tag).run cache.zone
    return (address,{ cache with zone })
  if bytes.size > 2147483616 then throw "DOS lump too large"
  let (address,zone) ← (alloc bytes.size.toUInt32 tag cell).run cache.zone
  let memory ← zone.memory.writeBytes address bytes
  return (address,{ cache with zone := { zone with memory } })

end Doom.DosMemory
