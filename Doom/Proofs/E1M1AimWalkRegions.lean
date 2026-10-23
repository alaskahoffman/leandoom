import Doom.Proofs.E1M1AimCatalogEntry
set_option backward.isDefEq.respectTransparency false
namespace Doom.Proofs.E1M1AimWalkRegions
open Verification X86 X86Memory X86Control BlockSummary
open E1M1NoiseAllocation (Region)
open E1M1AimObjectRegions (Located)

/-- Conservative stack reserve for the collection/first-selection read guards,
relative to the established context anchor q.sp. Not a whole-game stack bound. -/
def Reserve (stack : Region) (sp : Word) : Prop :=
  stack.lo+212 ≤ sp.toNat ∧ sp.toNat ≤ stack.hi ∧ stack.hi ≤ 2^32

/-- A common byte-range argument handles both positive local offsets and
negative pushes once their combined displacement is normalized. -/
theorem stack_apart (stack : Region) (sp a offset : Word)
    (reserve : Reserve stack sp) (located : Located stack a)
    (fits : 2^32-212 ≤ offset.toNat ∧ offset.toNat ≤ 2^32-4) : Apart a (sp+offset) := by
  obtain ⟨r,inside,apartStack,_⟩ := located
  apply Region.apart inside ?_ apartStack
  have size := sp.isLt
  simp only [Reserve] at reserve
  simp only [Region.Contains,BitVec.toNat_add]
  omega

theorem global_apart (stack : Region) (a b : Word) (located : Located stack a)
    (inside : E1M1AimMapRegions.globalStores.Contains b) : Apart a b := by
  obtain ⟨r,read,_,apartGlobals⟩ := located
  exact Region.apart read inside apartGlobals

/-- The fixed-store envelope already encloses the complete 128-record intercept
buffer, including all three words of the last record. Capacity itself is separate. -/
theorem array_safe (stack : Region) (a : Word) (located : Located stack a) :
    OriginalLineMixedInvariant.ArraySafe 0x2ba20 a := by
  constructor
  · intro k hk off member
    apply global_apart stack a _ located
    have contains (n : Nat) (hn : n ≤ 8) : E1M1AimMapRegions.globalStores.Contains
        (OriginalLineCollection.slot 0x2ba20 k (BitVec.ofNat 32 n)) := by
      have address : OriginalLineCollection.slot 0x2ba20 k (BitVec.ofNat 32 n)=
          BitVec.ofNat 32 (178720+12*k+n) := by
        simp [OriginalLineCollection.slot,BitVec.ofNat_add]
      rw [address]
      simp only [E1M1AimMapRegions.globalStores,Region.Contains,BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (show 178720+12*k+n<2^32 by omega)]
      omega
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl <;> exact contains _ (by decide)
  · exact global_apart stack a _ located (by decide)

/-- All collection stack/buffer guards are derived. Linedef visit-stamp writes
are singled out because they share an allocation with read-only line fields. -/
theorem collection (stack : Region) (sp lines a : Word)
    (reserve : Reserve stack sp) (located : Located stack a)
    (stamps : ∀ j<475, Apart a (OriginalLineVisits.stamp lines j)) :
    E1M1FiringMapState.Safe sp lines a := by
  have pushes := stack_apart stack sp a
  have push (off : Word) (fits : 2^32-212 ≤ off.toNat ∧ off.toNat ≤ 2^32-4) :=
    pushes off reserve located fits
  have array := array_safe stack a located
  refine ⟨⟨⟨stamps,?_,?_,?_⟩,array⟩,?_,⟨?_,⟨?_,?_⟩,?_,?_,array⟩,?_⟩
  all_goals first
    | (intro off member
       simp only [OriginalLineTail.stackOffsets,List.mem_cons,List.not_mem_nil,or_false] at member
       rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
       all_goals simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
       all_goals exact push _ (by decide))
    | (simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]; exact push _ (by decide))

/-- Protection through intercept setup, minimum scan and the first callback CALL. -/
theorem selection (stack : Region) (sp a : Word)
    (reserve : Reserve stack sp) (located : Located stack a) :
    E1M1AimEntryFrame.SafeWord (sp-112) a := by
  refine ⟨?_,global_apart stack a _ located (by decide),?_⟩
  · intro off member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    all_goals exact stack_apart stack sp a _ reserve located (by decide)
  · simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    exact stack_apart stack sp a _ reserve located (by decide)
/-- Region separation also supplies the persistent ordered-hit word guard,
including every possible fraction mark and the callback's own return slot. -/
theorem ordered (stack : Region) (sp a : Word) (s : X86Memory.State)
    (reserve : Reserve stack sp) (located : Located stack a)
    (position : s.regs 4=sp-140) : E1M1AimMapFrame.StableWord s a := by
  have push (off : Word) (fits : 2^32-212 ≤ off.toNat ∧ off.toNat ≤ 2^32-4) :=
    stack_apart stack sp a off reserve located fits
  refine ⟨⟨?_,?_⟩,?_,global_apart stack a _ located (by decide),?_⟩
  · intro off member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp only [position,BitVec.sub_eq_add_neg,BitVec.add_assoc]
    all_goals exact push _ (by decide)
  · intro b member
    simp only [E1M1AimReturnFrame.writes,List.mem_append] at member
    rcases member with (localWrites|opening)|clip
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at localWrites
      rcases localWrites with rfl|rfl|rfl|rfl|rfl
      all_goals simp only [position,BitVec.sub_eq_add_neg,BitVec.add_assoc]
      all_goals exact push _ (by decide)
    · apply global_apart stack a _ located
      simp only [E1M1NoiseLineProgress.openingGlobals,List.mem_cons,List.not_mem_nil,or_false] at opening
      rcases opening with rfl|rfl|rfl|rfl <;> decide
    · apply global_apart stack a _ located
      simp only [List.mem_cons,List.not_mem_nil,or_false] at clip
      rcases clip with rfl|rfl <;> decide
  · intro i hi
    simpa [E1M1MinimumScan.address,OriginalLineCollection.slot,BitVec.ofNat_add] using
      (array_safe stack a located).1 i hi 0 (by simp)
  · simp only [position,BitVec.sub_eq_add_neg]
    exact push _ (by decide)
end Doom.Proofs.E1M1AimWalkRegions
