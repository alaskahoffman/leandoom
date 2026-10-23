import Doom.Proofs.E1M1AimRegions
import Doom.Proofs.E1M1AimControllerData
set_option backward.isDefEq.respectTransparency false
namespace Doom.Proofs.E1M1AimStaticRegions
open Verification X86 X86Memory X86Control BlockSummary
open E1M1NoiseAllocation (Region)
open E1M1AimRegions (StackReserve Covered field)
open E1M1AimControllerInputs (layout)

/-- A conservative envelope of the fixed DOS table and input-global addresses.
Only separation from stack stores is asserted, not immutability of this range. -/
def globals : Region := ⟨0x5a84,0x2c124⟩
/-- The 3461 halfwords occupy 6922 bytes. Existing transport uses four-byte read
windows, so its guard envelope extends two bytes beyond the last halfword.
This is a protection envelope, not a claim of two extra allocated map bytes. -/
def blockmap (base : Word) : Region := ⟨base.toNat,base.toNat+6924⟩
def linedefs (base : Word) : Region := ⟨base.toNat,base.toNat+475*62⟩
/-- Includes exactly the shooter prefix needed here (up to height at offset 68). -/
def shooter (base : Word) : Region := ⟨base.toNat,base.toNat+72⟩

structure Layout (stack : Region) (base lines who : Word) : Prop where
  mapBound : base.toNat+6924 ≤ 2^32
  linesBound : lines.toNat+475*62 ≤ 2^32
  shooterBound : who.toNat+72 ≤ 2^32
  globalsStack : globals.Disjoint stack
  mapStack : (blockmap base).Disjoint stack
  linesStack : (linedefs lines).Disjoint stack
  shooterStack : (shooter who).Disjoint stack

theorem table_word (i : Fin 10240) :
    globals.Contains (0x5a84+BitVec.ofNat 32 (i.val*4)) := by
  have hi := i.isLt
  simp [globals,Region.Contains,BitVec.toNat_add,BitVec.toNat_ofNat]
  omega

theorem sample_words (angle : Angle) :
    ∀ a∈E1M1AimRetryGeometry.sampleReads angle, globals.Contains a := by
  intro a member
  simp only [E1M1AimRetryGeometry.sampleReads,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl
  · decide
  all_goals
    rw [thrust_table_index]
    have hi := angle.fineIndex.isLt
    simp [globals,Region.Contains,BitVec.toNat_add,BitVec.toNat_ofNat]
    omega

theorem map_word (base : Word) (bound : base.toNat+6924 ≤ 2^32)
    (i : Nat) (hi : i<3461) :
    (blockmap base).Contains (base+BitVec.ofNat 32 (2*i)) :=
  field base 6924 (2*i) bound (by omega)

theorem line_stamp (lines : Word) (bound : lines.toNat+475*62 ≤ 2^32)
    (j : Nat) (hj : j<475) : (linedefs lines).Contains (OriginalLineVisits.stamp lines j) := by
  have address : OriginalLineVisits.stamp lines j=lines+BitVec.ofNat 32 (62*j+54) := by
    simp only [OriginalLineVisits.stamp,BitVec.ofNat_add,BitVec.ofNat_mul]
    rw [BitVec.mul_comm (BitVec.ofNat 32 j)]
    ac_rfl
  rw [address]
  exact field lines (475*62) (62*j+54) bound (by omega)

/-- Discharges all map read guards from the pinned word count and range bounds. -/
theorem map_covered (stack : Region) (base lines who : Word) (words : Array Nat)
    (placement : Layout stack base lines who) (size : words.size=3461) :
    Covered stack (E1M1AimRetryData.mapReads base words) := by
  intro a member
  simp only [E1M1AimRetryData.mapReads,List.mem_append] at member
  rcases member with global|word
  · refine ⟨globals,?_,placement.globalsStack⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false] at global
    rcases global with rfl|rfl|rfl|rfl|rfl <;> decide
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp word
    refine ⟨blockmap base,map_word base placement.mapBound i ?_,placement.mapStack⟩
    have := List.mem_range.mp hi
    omega

/-- Stamp values change during play; only their addresses are used in this proof. -/
theorem stamps_covered (stack : Region) (base lines who : Word) (count : Nat)
    (placement : Layout stack base lines who) (size : count=475) :
    Covered stack (E1M1AimStampQuery.stampWords lines count) := by
  intro a member
  simp only [E1M1AimStampQuery.stampWords,List.mem_cons] at member
  rcases member with rfl|stamp
  · exact ⟨globals,by decide,placement.globalsStack⟩
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp stamp
    refine ⟨linedefs lines,line_stamp lines placement.linesBound j ?_,placement.linesStack⟩
    have := List.mem_range.mp hj
    omega

theorem geometry_covered (stack : Region) (base lines : Word)
    (s : X86Memory.State) (angle : Angle) (placement : Layout stack base lines (s.regs 0)) :
    Covered stack (E1M1AimRetryGeometry.reads (layout s angle) angle) := by
  intro a member
  simp only [E1M1AimRetryGeometry.reads,List.mem_append] at member
  rcases member with (actor|origin)|sample
  · refine ⟨shooter (s.regs 0),?_,placement.shooterStack⟩
    simp only [OriginalAimSetup.actorReads,layout,put,write,
      List.mem_cons,List.not_mem_nil,or_false] at actor
    rcases actor with rfl|rfl|rfl|rfl <;>
      exact field _ 72 _ placement.shooterBound (by decide)
  · refine ⟨globals,?_,placement.globalsStack⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false] at origin
    rcases origin with rfl|rfl <;> decide
  · exact ⟨globals,sample_words angle a sample,placement.globalsStack⟩

/-- Includes the complete table, hence is reusable for every probe angle. -/
theorem tables_safe (stack : Region) (s : X86Memory.State)
    (reserve : StackReserve stack s) (separate : globals.Disjoint stack) :
    E1M1AimControllerData.TableSafe s := by
  have writes := E1M1AimRegions.writes_contained stack s reserve
  exact ⟨fun b hb => Region.apart (show globals.Contains 0x13584 by decide) (writes b hb) separate,
    fun i b hb => Region.apart (table_word i) (writes b hb) separate⟩
end Doom.Proofs.E1M1AimStaticRegions
