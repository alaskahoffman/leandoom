import Doom.Proofs.E1M1AimCellStamps
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
namespace Doom.Proofs.E1M1AimCellWalk
open Verification X86 X86Memory X86Control BlockSummary
open E1M1NoiseAllocation (Region)
open E1M1CellWalkInvariant (Context Cell)
open E1M1AimCellStamps (Layout)

/-- Collection preserves these initialized trace/option globals and the
blocklinks pointer. Setup itself writes some of them. -/
def globals : List Word := [0x2ba10,0x2ba14,0x2ba18,0x2ba1c,0x2c024,0x2c0f8]

def buffer : Region := ⟨0x2ba20,0x2c020⟩

theorem buffer_word (k : Nat) (hk : k<128) (off : Word) (member : off∈[(0#32),4,8]) :
    buffer.Contains (OriginalLineCollection.slot 0x2ba20 k off) := by
  have contains (n : Nat) (hn : n≤8) :
      buffer.Contains (OriginalLineCollection.slot 0x2ba20 k (BitVec.ofNat 32 n)) := by
    have address : OriginalLineCollection.slot 0x2ba20 k (BitVec.ofNat 32 n)=
        BitVec.ofNat 32 (178720+12*k+n) := by
      simp [OriginalLineCollection.slot,BitVec.ofNat_add]
    rw [address]
    simp only [buffer,Region.Contains,BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (show 178720+12*k+n<2^32 by omega)]
    omega
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl <;> exact contains _ (by decide)

theorem global_array (a : Word) (member : a∈globals) :
    OriginalLineMixedInvariant.ArraySafe 0x2ba20 a := by
  have bytes : (E1M1AimObjectRegions.region a 4).Contains a ∧
      (E1M1AimObjectRegions.region a 4).Disjoint buffer ∧ Apart a (0x2c028#32) := by
    simp only [globals,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl <;>
      refine ⟨by decide,by decide,?_⟩ <;> unfold Apart <;> decide
  exact ⟨fun k hk off ho => Region.apart bytes.1 (buffer_word k hk off ho) bytes.2.1,bytes.2.2⟩

/-- A region need not avoid every setup write to survive collection. In this
phase only stack stores, intercept records/cursor and visit stamps matter. -/
theorem word (stack r : Region) (sp lines a : Word)
    (reserve : E1M1AimWalkRegions.Reserve stack sp) (inside : r.Contains a)
    (separate : r.Disjoint stack) (array : OriginalLineMixedInvariant.ArraySafe 0x2ba20 a)
    (stamps : ∀ j<475, Apart a (OriginalLineVisits.stamp lines j)) :
    E1M1FiringMapState.Safe sp lines a := by
  have push (off : Word) (fits : 2^32-212≤off.toNat ∧ off.toNat≤2^32-4) : Apart a (sp+off) := by
    apply Region.apart inside ?_ separate
    have size := sp.isLt
    simp only [E1M1AimWalkRegions.Reserve] at reserve
    simp only [Region.Contains,BitVec.toNat_add]
    omega
  refine ⟨⟨⟨stamps,?_,?_,?_⟩,array⟩,?_,⟨?_,⟨?_,?_⟩,?_,?_,array⟩,?_⟩
  all_goals first
    | (intro off member
       simp only [OriginalLineTail.stackOffsets,List.mem_cons,List.not_mem_nil,or_false] at member
       rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
       all_goals simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
       all_goals exact push _ (by decide))
    | (simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]; exact push _ (by decide))

theorem global_safe (stack : Region) (q : Context) (c : Cell) (placement : Layout stack q c)
    (reserve : E1M1AimWalkRegions.Reserve stack q.sp) (a : Word) (member : a∈globals) :
    E1M1FiringMapState.Safe q.sp q.lines a := by
  have inside : E1M1AimStaticRegions.globals.Contains a ∧ E1M1AimMapRegions.globalStores.Contains a := by
    simp only [globals,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  exact word stack E1M1AimStaticRegions.globals q.sp q.lines a reserve inside.1
    placement.globalsStack (global_array a member) (E1M1AimCellStamps.global stack q c placement a inside.2)

theorem reads_safe (stack : Region) (q : Context) (c : Cell) (placement : Layout stack q c)
    (reserve : E1M1AimWalkRegions.Reserve stack q.sp) :
    ∀ a∈E1M1AimRetryData.cellReads q c, E1M1FiringMapState.Safe q.sp q.lines a := by
  intro a member
  rcases E1M1AimCellRegions.reads stack q c placement.input a member with located|rfl
  · exact E1M1AimWalkRegions.collection stack q.sp q.lines a reserve located
      (E1M1AimCellStamps.reads stack q c placement a member)
  · exact global_safe stack q c placement reserve _ (by simp [globals])

/-- Reconstruct the existing whole-cell image protection, including initialized
trace words which deliberately were absent from the pre-setup payload. -/
theorem scene_safe (stack : Region) (q : Context) (c : Cell) (placement : Layout stack q c)
    (reserve : E1M1AimWalkRegions.Reserve stack q.sp) :
    E1M1CellSceneInvariant.Protected q.sp q.lines c.cell c.data c.nodes := by
  have allReads := reads_safe stack q c placement reserve
  have line (i : Fin c.cell.ids.length) (a : Word)
      (member : a∈E1M1ScanMemory.lineReads (E1M1ScanGeometry.linePointer q.lines c.cell.ids[i.val])
        (c.data i.val).v (c.data i.val).w ++ [E1M1ScanGeometry.linePointer q.lines c.cell.ids[i.val]+50]) :=
    allReads a (by simp only [E1M1AimRetryData.cellReads,List.mem_append]; exact Or.inl (Or.inl
      (List.mem_flatMap.mpr ⟨i,by simp,member⟩)))
  have node (n : E1M1ThingList.Node) (member : n∈c.nodes) (a : Word)
      (field : a∈[n.pointer+12,n.pointer+16,n.pointer+64,n.pointer+44]) :=
    allReads a (by simp only [E1M1AimRetryData.cellReads,List.mem_append]; exact Or.inl (Or.inr
      (List.mem_flatMap.mpr ⟨n,member,field⟩)))
  refine ⟨?_,global_safe stack q c placement reserve _ (by simp [globals]),
    fun i a ha => line i a (List.mem_append_left _ ha),
    fun i => line i _ (List.mem_append_right _ (by simp)),?_,fun n hn => node n hn _ (by simp)⟩
  · intro a ha
    apply global_safe stack q c placement reserve a
    simp only [E1M1ThingGeometry.traceReads,List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl|rfl <;> simp [globals]
  · intro n hn a ha
    simp only [E1M1ThingVisit.reads,List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact global_safe stack q c placement reserve _ (by simp [globals])
    · exact global_safe stack q c placement reserve _ (by simp [globals])
    · exact global_safe stack q c placement reserve _ (by simp [globals])
    · exact global_safe stack q c placement reserve _ (by simp [globals])
    · exact node n hn _ (by simp)
    · exact node n hn _ (by simp)
    · exact node n hn _ (by simp)

theorem selection_safe (stack : Region) (q : Context) (c : Cell) (placement : Layout stack q c)
    (reserve : E1M1AimWalkRegions.Reserve stack q.sp) :
    E1M1CellObjectSelection.Protected q.sp q.lines q.links c.x c.y q.width := by
  exact ⟨reads_safe stack q c placement reserve _ (by simp [E1M1AimRetryData.cellReads]),
    reads_safe stack q c placement reserve _ (by simp [E1M1AimRetryData.cellReads])⟩
end Doom.Proofs.E1M1AimCellWalk
