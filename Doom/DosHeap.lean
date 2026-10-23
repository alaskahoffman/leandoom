import Doom.DosCache
import Doom.Wad

namespace Doom.DosHeap

/-- Resource identities, independent of where the allocator eventually puts them. -/
inductive Resource where
  | lump (index : Nat)
  | composite (index : Nat)
  deriving Inhabited, BEq

structure Composite where
  bytes : ByteArray
  patches : Array Nat
  deriving Inhabited

/-- Explicit platform ABI for the pinned silent DOS live-comparison profile.
These are process-layout inputs, not addresses copied from a frame or replay. -/
structure Layout where
  zoneBase : UInt32 := 0x28e024
  zoneSize : UInt32 := 8*1024*1024
  lumpCells : UInt32 := 0xa8f024
  inputCapacity : Nat := 10000
  deriving Inhabited

structure Event where
  op : String
  size : Nat := 0
  tag : Int32 := 0
  owner : UInt32 := 0
  address : UInt32 := 0
  deriving Inhabited

structure Heap where
  cache : DosMemory.LumpCache
  lumps : Array Lump
  compositeCells : UInt32 := 0
  composites : Array Composite := #[]
  objects : Std.HashMap String UInt32 := {}
  /-- Optional diagnostics are output only; never drive allocation decisions. -/
  tracing : Bool := false
  events : Array Event := #[]
  deriving Inhabited

abbrev Action := StateT Heap (Except String)

def create (lumps : Array Lump) (layout : Layout := {}) : Except String Heap := do
  let memory ← ({} : DosMemory.Memory).reserve layout.zoneBase layout.zoneSize.toNat
  let memory ← memory.reserve layout.lumpCells ((lumps.size+1)*4)
  let zone ← DosMemory.init memory layout.zoneBase layout.zoneSize
  let cache ← DosMemory.LumpCache.create zone layout.lumpCells (lumps.size+1)
  return { cache, lumps }

private def record (h : Heap) (e : Event) : Heap :=
  if h.tracing then { h with events := h.events.push e } else h

def allocate (size : Nat) (tag : Int32 := 1) (owner : UInt32 := 0) : Action UInt32 := fun h => do
  if size > 2147483616 then throw "DOS allocation size outside supported domain"
  let (address,zone) ← (DosMemory.alloc size.toUInt32 tag owner).run h.cache.zone
  return (address, record { h with cache := { h.cache with zone } } ⟨"alloc",size,tag,owner,address⟩)

def release (address : UInt32) : Action Unit := fun h => do
  let (_,zone) ← (DosMemory.free address).run h.cache.zone
  return ((),record { h with cache := { h.cache with zone } } { op := "free", address })

def tag (address : UInt32) (value : Int32) : Action Unit := fun h => do
  -- Reapplying an unchanged tag is a memory no-op, including on DOS.
  if (← h.cache.zone.memory.read32 (address-16)) == value.toUInt32 then return ((),h)
  let (_,zone) ← (DosMemory.changeTag address value).run h.cache.zone
  return ((),{ h with cache := { h.cache with zone } })

def write (address : UInt32) (bytes : ByteArray) : Action Unit := fun h => do
  let memory ← h.cache.zone.memory.writeBytes address bytes
  return ((),{ h with cache := { h.cache with zone := { h.cache.zone with memory } } })

def forget (address : UInt32) (size : Nat) : Action Unit := fun h => do
  let memory ← h.cache.zone.memory.forget address size
  return ((),{ h with cache := { h.cache with zone := { h.cache.zone with memory } } })

def load (index : Nat) (value : Int32 := 101) : Action UInt32 := do
  if let some address ← (← get).cache.address index then
    tag address value
    return address
  let h ← get
  let some lump := h.lumps[index]? | throw "DOS cache: missing lump payload"
  let owner ← h.cache.cell index
  let address ← allocate lump.bytes.size value owner
  write address lump.bytes
  return address

def named (label : String) (value : Int32 := 101) : Action UInt32 := do
  let some index := findLump (← get).lumps label | throw s!"DOS cache: missing {label}"
  load index value

def acquire (resource : Resource) : Action UInt32 := do
  match resource with
  | .lump i => load i
  | .composite i =>
    let h ← get
    let some data := h.composites[i]? | throw "DOS texture index out of range"
    let cell := h.compositeCells + (i*4).toUInt32
    let old ← h.cache.zone.memory.read32 cell
    if old != 0 then return old
    let address ← allocate data.bytes.size 1 cell
    -- R_GenerateComposite locks the buffer while caching its patches, then
    -- makes it purgeable. Patch order is texture-definition order.
    for p in data.patches do let _ ← load p
    write address data.bytes
    tag address 101
    return address

def spawn (key : String) (size : Nat) : Action Unit := do
  if (← get).objects.contains key then throw s!"DOS duplicate thinker {key}"
  let address ← allocate size 50
  forget address size
  modify fun h => { h with objects := h.objects.insert key address }

def remove (key : String) : Action Unit := do
  let some address := (← get).objects[key]? | throw s!"DOS missing thinker {key}"
  release address
  modify fun h => { h with objects := h.objects.erase key }

/-- Opening wipe temporaries, after the first captured presentation. -/
def openingWipe : Action Unit := do
  -- DOS wipe_shittyColMajorXform uses and frees one temporary per screen.
  for _ in [:2] do
    let temp ← allocate 64000
    forget temp 64000
    release temp
  let columns ← allocate (320*4)
  forget columns (320*4)
  release columns

end Doom.DosHeap
