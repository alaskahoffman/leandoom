import Doom.Proofs.OriginalFloorEntry
open Doom Doom.Verification Doom.Verification.X86Memory Doom.Verification.X86Control
open Doom.Proofs
open Doom.Proofs.FloorDamage (Kind)
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

namespace FloorEntryFixture

def tableMemory : Memory := fun a =>
  if 0x1261c ≤ a.toNat ∧ a.toNat < 0x1271c then
    (Doom19.randomTableBytes.toArray[a.toNat-0x1261c]!).toBitVec
  else 0

def initial (kind : Kind) (z floor : Int32) (seed : UInt8) (suit time : Nat) : X86Memory.State :=
  let memory := store32 (store32 (store32 (store32 (store32 tableMemory
    0x40000 0x41000) 0x40038 (BitVec.ofNat 32 suit)) 0x2cf80 (BitVec.ofNat 32 time))
    0x12720 (BitVec.ofNat 32 seed.toNat)) 0x1271c 173
  let memory := store32 (store32 (store32 (store32 memory
    0x41034 0x42000) 0x42000 0x43000) 0x41014 z.toBitVec) 0x43000 floor.toBitVec
  ⟨fun r => if r=0 then 0x40000 else if r=4 then 0x50000 else 0xa5a5a5a5,
    X86Routine.store16 memory 0x4300e (BitVec.ofNat 16 kind.special)⟩

-- Initial ESI/EAX do not have the case-entry values. The proved loads establish them.
-- Both high bits of Z and special 16's inclusive switch bound are exercised.
example : FloorEntry.Inputs .sixteen (initial .sixteen (-2147483648) (-2147483648) 255 1 32)
    ⟨-2147483648⟩ ⟨-2147483648⟩ 32 true ⟨255,173⟩ := by
  constructor <;> first | decide | (intro; constructor <;> decide)
example : FloorEntry.Inputs .four (initial .four 1 0 65 1 32)
    ⟨1⟩ ⟨0⟩ 32 true ⟨65,173⟩ := by
  constructor <;> first | decide | (intro; constructor <;> decide)
example : FloorEntry.Inputs .seven (initial .seven 2147483647 2147483647 0 0 0)
    ⟨2147483647⟩ ⟨2147483647⟩ 0 false ⟨0,173⟩ := by
  constructor <;> first | decide | (intro; constructor <;> decide)

def checks (kind : Kind) (z floor : Int32) (seed : UInt8) (suit time amount index : Nat) : Bool :=
  (X86CodeMemory.run FloorEntry.cm FloorEntry.program FloorDamage.exits 31
    ⟨initial kind z floor seed suit time,none,0x2fb24⟩).map FloorDamage.observe ==
      some (amount,BitVec.ofNat 32 index,(173#32))

#eval [
  checks .five 0 0 65 0 32 10 65,
  checks .five 0 0 65 1 32 0 65,
  checks .seven 2147483647 2147483647 0 0 0 5 0,
  checks .seven (-2147483648) (-2147483648) 0 0 1 0 0,
  checks .four 0 0 65 1 32 20 66,
  checks .four 0 0 65 1 1 0 66,
  checks .four 1 0 65 1 32 0 65,
  checks .four (-1) 0 65 1 32 0 65,
  checks .sixteen (-2147483648) (-2147483648) 255 1 32 20 0,
  checks .sixteen 0 0 0 1 32 0 1,
  checks .sixteen 1 0 255 1 32 0 255,
  checks .sixteen 0 0 65 0 32 20 65]
end FloorEntryFixture
