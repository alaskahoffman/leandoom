import Doom.Proofs.E1M1AimMapEntry
set_option backward.isDefEq.respectTransparency false
namespace Doom.Proofs.E1M1AimObjectRegions
open Verification X86 X86Memory X86Control BlockSummary
open E1M1NoiseAllocation (Region)

/-- A read prefix, not a claim about an object's full allocation size. Aliasing
between read-only objects is permitted; only writes require separation. -/
def region (base : Word) (bytes : Nat) : Region := ⟨base.toNat,base.toNat+bytes⟩
structure Storage (stack : Region) (base : Word) (bytes : Nat) : Prop where
  bound : base.toNat+bytes ≤ 2^32
  stackApart : (region base bytes).Disjoint stack
  globalsApart : (region base bytes).Disjoint E1M1AimMapRegions.globalStores

def Located (stack : Region) (a : Word) : Prop :=
  ∃ r : Region, r.Contains a ∧ r.Disjoint stack ∧ r.Disjoint E1M1AimMapRegions.globalStores

theorem field (stack : Region) (base : Word) (bytes off : Nat)
    (storage : Storage stack base bytes) (fits : off+4 ≤ bytes) :
    Located stack (base+BitVec.ofNat 32 off) :=
  ⟨region base bytes,E1M1AimRegions.field base bytes off storage.bound fits,
    storage.stackApart,storage.globalsApart⟩

/-- The flags read is a byte, but existing memory transport protects a full word
at that address, so the actor prefix extends through byte 107. -/
theorem actor (stack : Region) (base : Word) (storage : Storage stack base 108) :
    ∀ a∈[base+104,base+20,base+68], Located stack a := by
  intro a member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl <;> exact field stack base 108 _ storage (by decide)

theorem wall (stack : Region) (line : Word) (storage : Storage stack line 62) :
    Located stack (line+16) := by
  exact field stack line 62 16 storage (by decide)

/-- Covers unaligned line pointer fields at offsets 46/50 and the first two
sector words. Front/back sectors may be the same object. -/
theorem opening (stack : Region) (line front back : Word)
    (lineStorage : Storage stack line 62)
    (frontStorage : Storage stack front 8) (backStorage : Storage stack back 8) :
    ∀ a∈(line+16)::E1M1OpeningHeights.reads line front back, Located stack a := by
  intro a member
  simp only [E1M1OpeningHeights.reads,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact wall stack line lineStorage
  · exact field stack line 62 24 lineStorage (by decide)
  · exact field stack line 62 46 lineStorage (by decide)
  · exact field stack line 62 50 lineStorage (by decide)
  · simpa using field stack _ 8 0 frontStorage (by decide)
  · exact field stack front 8 4 frontStorage (by decide)
  · simpa using field stack _ 8 0 backStorage (by decide)
  · exact field stack back 8 4 backStorage (by decide)

theorem setup_safe (stack : Region) (s : X86Memory.State) (a : Word)
    (reserve : E1M1AimSetupFootprint.Reserve stack s) (located : Located stack a) :
    E1M1PathMapQuery.Safe s a := by
  obtain ⟨r,inside,apartStack,apartGlobals⟩ := located
  apply E1M1AimSetupFootprint.region_safe stack r s a reserve inside apartStack
  intro b member
  exact Region.apart inside (E1M1AimMapRegions.stores_contained b member) apartGlobals

/-- The real opening helper's four stack saves require sixteen bytes. -/
def OpeningReserve (stack : Region) (s : X86Memory.State) : Prop :=
  stack.lo+16 ≤ (s.regs 4).toNat ∧ (s.regs 4).toNat ≤ stack.hi ∧ stack.hi ≤ 2^32

theorem opening_safe (stack : Region) (s : X86Memory.State) (front back : Word)
    (reserve : OpeningReserve stack s) (lineStorage : Storage stack (s.regs 0) 62)
    (frontStorage : Storage stack front 8) (backStorage : Storage stack back 8) :
    E1M1OpeningHeights.Safe s front back := by
  have stackWord (n : Nat) (low : 4 ≤ n) (high : n ≤ 16) :
      stack.Contains (s.regs 4-BitVec.ofNat 32 n) := by
    have size := (s.regs 4).isLt
    simp only [OpeningReserve] at reserve
    simp only [Region.Contains,BitVec.toNat_sub,BitVec.toNat_ofNat]
    omega
  intro a member b written
  obtain ⟨r,inside,apartStack,apartGlobals⟩ := opening stack _ front back
    lineStorage frontStorage backStorage a (List.mem_cons_of_mem _ member)
  simp only [List.mem_append] at written
  rcases written with saved|global
  · apply Region.apart inside ?_ apartStack
    simp only [E1M1OpeningHeights.saves,List.mem_cons,List.not_mem_nil,or_false] at saved
    rcases saved with rfl|rfl|rfl|rfl <;> exact stackWord _ (by decide) (by decide)
  · apply Region.apart inside ?_ apartGlobals
    simp only [E1M1NoiseLineProgress.openingGlobals,List.mem_cons,List.not_mem_nil,or_false] at global
    rcases global with rfl|rfl|rfl|rfl <;> decide
end Doom.Proofs.E1M1AimObjectRegions
