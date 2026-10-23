import Doom.Proofs.E1M1AimCellCollection
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
namespace Doom.Proofs.E1M1AimCallbackRegions
open Verification X86 X86Memory X86Control BlockSummary
open E1M1NoiseAllocation (Region)
open E1M1CellWalkInvariant (Context)

/-- Separation sufficient for the traversal/callback handoff. This is a
placement contract, not a claim about all reachable stack/heap allocations. -/
structure Layout (stack : Region) (lines : Word) : Prop where
  lineBound : lines.toNat+475*62≤2^32
  linesStack : (E1M1AimStaticRegions.linedefs lines).Disjoint stack
  globalsStack : E1M1AimMapRegions.globalStores.Disjoint stack

theorem stack_word (stack : Region) (sp : Word) (n : Nat)
    (reserve : E1M1AimWalkRegions.Reserve stack sp) (low : 4≤n) (high : n≤212) :
    stack.Contains (sp-BitVec.ofNat 32 n) := by
  have size := sp.isLt
  simp only [E1M1AimWalkRegions.Reserve] at reserve
  simp only [Region.Contains,BitVec.toNat_sub,BitVec.toNat_ofNat]
  omega

theorem global_stack (stack : Region) (sp lines a : Word) (n : Nat)
    (placement : Layout stack lines) (reserve : E1M1AimWalkRegions.Reserve stack sp)
    (inside : E1M1AimMapRegions.globalStores.Contains a) (low : 4≤n) (high : n≤212) :
    Apart a (sp-BitVec.ofNat 32 n) := by
  exact Region.apart inside (stack_word stack sp n reserve low high) placement.globalsStack

theorem stack_array (stack : Region) (sp lines : Word) (n : Nat)
    (placement : Layout stack lines) (reserve : E1M1AimWalkRegions.Reserve stack sp)
    (low : 4≤n) (high : n≤212) :
    OriginalLineMixedInvariant.ArraySafe 0x2ba20 (sp-BitVec.ofNat 32 n) := by
  constructor
  · intro i hi off ho
    have inside := E1M1AimCellWalk.buffer_word i hi off ho
    have larger : E1M1AimMapRegions.globalStores.Contains (OriginalLineCollection.slot 0x2ba20 i off) := by
      simp only [E1M1AimCellWalk.buffer,Region.Contains] at inside
      simp only [E1M1AimMapRegions.globalStores,Region.Contains]
      omega
    exact FloorCaller.apart_symm (global_stack stack sp lines _ n placement reserve larger low high)
  · exact FloorCaller.apart_symm (global_stack stack sp lines _ n placement reserve (by decide) low high)

theorem stack_stamps (stack : Region) (sp lines : Word) (n : Nat)
    (placement : Layout stack lines) (reserve : E1M1AimWalkRegions.Reserve stack sp)
    (low : 4≤n) (high : n≤212) :
    ∀ j<475, Apart (sp-BitVec.ofNat 32 n) (OriginalLineVisits.stamp lines j) := by
  intro j hj
  exact Region.apart (stack_word stack sp n reserve low high)
    (E1M1AimStaticRegions.line_stamp lines placement.lineBound j hj) placement.linesStack.symm

/-- Upper caller words are separated from the deeper collection scratch frame.
Translation makes this byte proof independent of the numeric stack base. -/
theorem above (sp : Word) (n : Nat) (off : Word) (low : 4≤n) (high : n≤64)
    (deeper : 2^32-212≤off.toNat ∧ off.toNat≤2^32-68) :
    Apart (sp-BitVec.ofNat 32 n) (sp+off) := by
  simp only [BitVec.sub_eq_add_neg]
  apply OriginalPathXStep.apart_translate
  intro i j same
  have ii := i.isLt; have jj := j.isLt
  have equal := congrArg BitVec.toNat same
  simp only [BitVec.toNat_add,BitVec.toNat_neg,BitVec.toNat_ofNat] at equal
  omega

theorem upper_collection (stack : Region) (sp lines : Word) (n : Nat)
    (placement : Layout stack lines) (reserve : E1M1AimWalkRegions.Reserve stack sp)
    (low : 4≤n) (high : n≤64) :
    E1M1FiringMapState.Safe sp lines (sp-BitVec.ofNat 32 n) := by
  have array := stack_array stack sp lines n placement reserve low (by omega)
  have stamps := stack_stamps stack sp lines n placement reserve low (by omega)
  have push (off : Word) (fits : 2^32-212≤off.toNat ∧ off.toNat≤2^32-68) :
      Apart (sp+ -BitVec.ofNat 32 n) (sp+off) := by
    simpa only [BitVec.sub_eq_add_neg] using above sp n off low high fits
  refine ⟨⟨⟨stamps,?_,?_,?_⟩,array⟩,?_,⟨?_,⟨?_,?_⟩,?_,?_,array⟩,?_⟩
  all_goals first
    | (intro off member
       simp only [OriginalLineTail.stackOffsets,List.mem_cons,List.not_mem_nil,or_false] at member
       rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
       all_goals simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
       all_goals exact push _ (by decide))
    | (simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]; exact push _ (by decide))

/-- Both the intercept prologue and final callback CALL preserve every record. -/
theorem selection (stack : Region) (q : Context) (placement : Layout stack q.lines)
    (reserve : E1M1AimWalkRegions.Reserve stack q.sp) :
    E1M1TraversalEntry.Protected q ∧
    (∀ i<128, ∀ off∈[(0#32),4,8], Apart (OriginalLineCollection.slot 0x2ba20 i off) (q.sp-140)) ∧
    Apart (0x2c028#32) (q.sp-140) := by
  have record (i : Nat) (hi : i<128) (off : Word) (ho : off∈[(0#32),4,8]) (n : Nat)
      (low : 4≤n) (high : n≤212) : Apart (OriginalLineCollection.slot 0x2ba20 i off) (q.sp-BitVec.ofNat 32 n) := by
    have inside := E1M1AimCellWalk.buffer_word i hi off ho
    apply global_stack stack q.sp q.lines _ n placement reserve ?_ low high
    simp only [E1M1AimCellWalk.buffer,Region.Contains] at inside
    simp only [E1M1AimMapRegions.globalStores,Region.Contains]
    omega
  refine ⟨⟨?_,?_⟩,fun i hi off ho => record i hi off ho 140 (by decide) (by decide),
    global_stack stack q.sp q.lines _ 140 placement reserve (by decide) (by decide) (by decide)⟩
  · intro off member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl <;> simp only [BitVec.sub_sub]
    all_goals exact global_stack stack q.sp q.lines _ _ placement reserve (by decide) (by decide) (by decide)
  · intro i hi off ho push member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl <;> simp only [BitVec.sub_sub]
    all_goals exact record i hi off ho _ (by decide) (by decide)

/-- The callback pointer is at q.sp-44, above every path-initialization store. -/
theorem initial (stack : Region) (q : Context) (s : X86Memory.State)
    (placement : Layout stack q.lines) (reserve : E1M1AimWalkRegions.Reserve stack q.sp)
    (position : s.regs 4=q.sp-52) : E1M1PathMapSetup.Safe s (q.sp-44) := by
  have fixed (a : Word) (inside : E1M1AimMapRegions.globalStores.Contains a) : Apart (q.sp-44) a :=
    FloorCaller.apart_symm (global_stack stack q.sp q.lines a 44 placement reserve inside (by decide) (by decide))
  have push (off : Word) (apart : Apart (-44#32) off) : Apart (q.sp+(-44#32)) (q.sp+off) := by
    exact OriginalPathXStep.apart_translate q.sp (-44#32) off apart
  constructor
  · intro b member
    simp [OriginalPathInit.writes] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · simp only [position,BitVec.sub_eq_add_neg,BitVec.add_assoc]
      exact push _ (by unfold Apart; decide)
    · simp only [position,BitVec.sub_eq_add_neg,BitVec.add_assoc]
      exact push _ (by unfold Apart; decide)
    · simp only [position,BitVec.sub_eq_add_neg,BitVec.add_assoc]
      exact push _ (by unfold Apart; decide)
    · exact fixed _ (by decide)
    · exact fixed _ (by decide)
    · exact fixed _ (by decide)
    · exact fixed _ (by decide)
    · exact fixed _ (by decide)
    · exact fixed _ (by decide)
    · exact fixed _ (by decide)
    · simp only [position,BitVec.sub_eq_add_neg,BitVec.add_assoc]
      exact push _ (by unfold Apart; decide)
    · simp only [position,BitVec.sub_eq_add_neg,BitVec.add_assoc]
      exact push _ (by unfold Apart; decide)
    · simp only [position,BitVec.sub_eq_add_neg,BitVec.add_assoc]
      exact push _ (by unfold Apart; decide)
    · simp only [position,BitVec.sub_eq_add_neg,BitVec.add_assoc]
      exact push _ (by unfold Apart; decide)
    · simp only [position,BitVec.sub_eq_add_neg,BitVec.add_assoc]
      exact push _ (by unfold Apart; decide)
  · intro off member
    simp only [E1M1PathMapSetup.offsets,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp only [position,BitVec.sub_eq_add_neg,BitVec.add_assoc]
    all_goals exact push _ (by unfold Apart; decide)

theorem callback (stack : Region) (q : Context) (s : X86Memory.State)
    (placement : Layout stack q.lines) (reserve : E1M1AimWalkRegions.Reserve stack q.sp)
    (position : s.regs 4=q.sp-52) : E1M1QueryCallback.CallbackSafe q s := by
  exact ⟨initial stack q s placement reserve position,
    upper_collection stack q.sp q.lines 44 placement reserve (by decide) (by decide),
    (selection stack q placement reserve).2.1⟩
end Doom.Proofs.E1M1AimCallbackRegions
