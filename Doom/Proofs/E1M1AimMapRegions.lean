import Doom.Proofs.E1M1AimSetupFootprint
set_option backward.isDefEq.respectTransparency false
namespace Doom.Proofs.E1M1AimMapRegions
open Verification X86 X86Memory X86Control BlockSummary
open E1M1NoiseAllocation (Region)
open E1M1AimSetupFootprint (Reserve)

/-- Encloses all fixed setup stores. Read-only globals inside this envelope are
checked individually; heap map windows must be disjoint from the envelope. -/
def globalStores : Region := ⟨0x13580,0x2c1ec⟩
def mapGlobals : List Word := [0x2c0fc,0x2c110,0x2c100,0x2c10c,0x2c120]

structure Layout (stack : Region) (base : Word) : Prop where
  mapBound : base.toNat+6924 ≤ 2^32
  mapStack : (E1M1AimStaticRegions.blockmap base).Disjoint stack
  mapStores : (E1M1AimStaticRegions.blockmap base).Disjoint globalStores
  globalsStack : E1M1AimStaticRegions.globals.Disjoint stack

/-- Concrete global addresses are byte-disjoint, including the final byte of
each store. No assumption that the entire global-data region is immutable. -/
theorem fixed_globals :
    ∀ a∈mapGlobals, ∀ b∈E1M1AimSetupFootprint.globals, Apart a b := by
  simp [mapGlobals,E1M1AimSetupFootprint.globals]
  unfold Apart
  repeat' apply And.intro
  all_goals decide

theorem stores_contained :
    ∀ b∈E1M1AimSetupFootprint.globals, globalStores.Contains b := by
  simp [E1M1AimSetupFootprint.globals]
  decide

theorem global_safe (stack : Region) (s : X86Memory.State) (base a : Word)
    (reserve : Reserve stack s) (placement : Layout stack base) (member : a∈mapGlobals) :
    E1M1PathMapQuery.Safe s a := by
  apply E1M1AimSetupFootprint.region_safe stack E1M1AimStaticRegions.globals s a reserve
    ?_ placement.globalsStack (fixed_globals a member)
  simp only [mapGlobals,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl <;> decide

theorem word_safe (stack : Region) (s : X86Memory.State) (base : Word)
    (reserve : Reserve stack s) (placement : Layout stack base) (i : Nat) (hi : i<3461) :
    E1M1PathMapQuery.Safe s (base+BitVec.ofNat 32 (2*i)) := by
  have inside := E1M1AimStaticRegions.map_word base placement.mapBound i hi
  apply E1M1AimSetupFootprint.region_safe stack (E1M1AimStaticRegions.blockmap base) s _
    reserve inside placement.mapStack
  intro b member
  exact Region.apart inside (stores_contained b member) placement.mapStores

/-- The same layout also protects the blockmap through the earlier controller
prologue. This is a read-address fact, independent of map contents. -/
theorem covered (stack : Region) (base : Word) (words : Array Nat)
    (placement : Layout stack base) (size : words.size=3461) :
    E1M1AimRegions.Covered stack (E1M1AimRetryData.mapReads base words) := by
  intro a member
  simp only [E1M1AimRetryData.mapReads,List.mem_append] at member
  rcases member with global|word
  · refine ⟨E1M1AimStaticRegions.globals,?_,placement.globalsStack⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false] at global
    rcases global with rfl|rfl|rfl|rfl|rfl <;> decide
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp word
    refine ⟨E1M1AimStaticRegions.blockmap base,
      E1M1AimStaticRegions.map_word base placement.mapBound i ?_,placement.mapStack⟩
    have := List.mem_range.mp hi
    omega
end Doom.Proofs.E1M1AimMapRegions
