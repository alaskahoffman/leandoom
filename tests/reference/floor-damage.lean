import Doom.Proofs.OriginalFloorDamage
open Doom Doom.Verification Doom.Verification.X86Memory Doom.Verification.X86Control Doom.Proofs.FloorDamage
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

def tableMemory : Memory := fun a =>
  if 0x1261c ≤ a.toNat ∧ a.toNat < 0x1271c then
    (Doom19.randomTableBytes.toArray[a.toNat-0x1261c]!).toBitVec
  else 0

def fixture (seed : UInt8) (suit time : Nat) : X86Memory.State :=
  ⟨fun r => if r=0 then 0x41000 else if r=6 then 0x40000 else if r=4 then 0x50000 else 0xa5a5a5a5,
    store32 (store32 (store32 (store32 (store32 tableMemory
      0x40000 0x41000) 0x40038 (BitVec.ofNat 32 suit)) 0x2cf80 (BitVec.ofNat 32 time))
      0x12720 (BitVec.ofNat 32 seed.toNat)) 0x1271c 173⟩

-- Concrete witnesses show that the alias/encoding premises are satisfiable.
-- Seed 65 advances to the leaking roll 4. Seed 255 exercises index wrap.
example : Inputs (fixture 65 1 1) 1 true ⟨65,173⟩ := by
  constructor <;> first | decide | (intro; constructor <;> decide)
example : Inputs (fixture 255 1 32) 32 true ⟨255,173⟩ := by
  constructor <;> first | decide | (intro; constructor <;> decide)
example : Inputs (fixture 0 0 0) 0 false ⟨0,173⟩ := by
  constructor <;> first | decide | (intro; constructor <;> decide)

example : observe (result .four (fixture 65 1 1) ⟨65,173⟩) = (0,66,173) := by decide
example : observe (result .four (fixture 65 1 32) ⟨65,173⟩) = (20,66,173) := by decide
example : observe (result .sixteen (fixture 255 1 32) ⟨255,173⟩) = (20,0,173) := by decide
example : observe (result .five (fixture 0 0 0) ⟨0,173⟩) = (10,0,173) := by decide
example : observe (result .seven (fixture 0 0 32) ⟨0,173⟩) = (5,0,173) := by decide
example : observe (result .seven (fixture 0 1 32) ⟨0,173⟩) = (0,0,173) := by decide

-- Large Nat clocks still use precisely the original low-five-bit gate.
example : ((BitVec.ofNat 8 (2^80+32) &&& (31#8)) == 0) = true := by decide
