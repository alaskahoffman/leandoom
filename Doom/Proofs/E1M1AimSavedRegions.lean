import Doom.Proofs.E1M1AimCallbackEntry
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
namespace Doom.Proofs.E1M1AimSavedRegions
open Verification X86 X86Memory X86Control BlockSummary
open E1M1NoiseAllocation (Region)
open E1M1CellWalkInvariant (Context)
open E1M1AimCallbackRegions (Layout)

/-- Ordered processing writes below the saved caller area. Relative separation
works even for a wrapping stack base; allocation uses still require reserve. -/
theorem above (sp : Word) (n : Nat) (off : Word) (low : 4≤n) (high : n≤136)
    (deeper : 2^32-212≤off.toNat ∧ off.toNat≤2^32-140) :
    Apart (sp-BitVec.ofNat 32 n) (sp+off) := by
  simp only [BitVec.sub_eq_add_neg]
  apply OriginalPathXStep.apart_translate
  intro i j same
  have ii := i.isLt; have jj := j.isLt
  have equal := congrArg BitVec.toNat same
  simp only [BitVec.toNat_add,BitVec.toNat_neg,BitVec.toNat_ofNat] at equal
  omega

/-- Protect an upper stack word through continuing callbacks and every possible
fraction mark. The callback's own return address is excluded. -/
theorem ordered (stack : Region) (sp lines : Word) (s : X86Memory.State) (n : Nat)
    (placement : Layout stack lines) (reserve : E1M1AimWalkRegions.Reserve stack sp)
    (position : s.regs 4=sp-140) (low : 4≤n) (high : n≤136) :
    E1M1AimMapFrame.StableWord s (sp-BitVec.ofNat 32 n) := by
  have fixed (a : Word) (inside : E1M1AimMapRegions.globalStores.Contains a) :=
    FloorCaller.apart_symm (E1M1AimCallbackRegions.global_stack stack sp lines a n placement reserve inside low (by omega))
  have push (off : Word) (fits : 2^32-212≤off.toNat ∧ off.toNat≤2^32-140) :
      Apart (sp+ -BitVec.ofNat 32 n) (sp+off) := by
    simpa only [BitVec.sub_eq_add_neg] using above sp n off low high fits
  have array := E1M1AimCallbackRegions.stack_array stack sp lines n placement reserve low (by omega)
  refine ⟨⟨?_,?_⟩,?_,fixed _ (by decide),?_⟩
  · intro off member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp only [position,BitVec.sub_eq_add_neg,BitVec.add_assoc]
    all_goals exact push _ (by decide)
  · intro b member
    simp only [E1M1AimReturnFrame.writes,List.mem_append] at member
    rcases member with (locals|opening)|clip
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at locals
      rcases locals with rfl|rfl|rfl|rfl|rfl
      all_goals simp only [position,BitVec.sub_eq_add_neg,BitVec.add_assoc]
      all_goals exact push _ (by decide)
    · apply fixed
      simp only [E1M1NoiseLineProgress.openingGlobals,List.mem_cons,List.not_mem_nil,or_false] at opening
      rcases opening with rfl|rfl|rfl|rfl <;> decide
    · apply fixed
      simp only [List.mem_cons,List.not_mem_nil,or_false] at clip
      rcases clip with rfl|rfl <;> decide
  · intro i hi
    simpa [E1M1MinimumScan.address,OriginalLineCollection.slot,BitVec.ofNat_add] using array.1 i hi 0 (by simp)
  · simp only [position,BitVec.sub_eq_add_neg]
    exact push _ (by decide)

theorem protect (stack : Region) (sp lines : Word) (s : X86Memory.State) (n : Nat)
    (placement : Layout stack lines) (reserve : E1M1AimWalkRegions.Reserve stack sp)
    (position : s.regs 4=sp-140) (low : 4≤n) (high : n≤136) :
    E1M1AimSavedWords.Protect s (sp-BitVec.ofNat 32 n) := by
  exact ⟨ordered stack sp lines s n placement reserve position low high,
    FloorCaller.apart_symm (E1M1AimCallbackRegions.global_stack stack sp lines _ n placement reserve (by decide) low (by omega)),
    FloorCaller.apart_symm (E1M1AimCallbackRegions.global_stack stack sp lines _ n placement reserve (by decide) low (by omega))⟩

/-- The exact eight saved-word addresses, including nested return addresses,
are protected. This proves separation, not their contents or freshness. -/
theorem saved (stack : Region) (q : Context) (s : X86Memory.State)
    (placement : Layout stack q.lines) (reserve : E1M1AimWalkRegions.Reserve stack q.sp)
    (position : s.regs 4=q.sp-140) :
    ∀ a∈E1M1AimSavedCaller.words (q.sp-136), E1M1AimSavedWords.Protect s a := by
  intro a member
  obtain ⟨off,ho,rfl⟩ := List.mem_map.mp member
  simp only [E1M1AimSavedCaller.slots,List.mem_cons,List.not_mem_nil,or_false] at ho
  rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using protect stack q.sp q.lines s 120 placement reserve position (by decide) (by decide)
  · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using protect stack q.sp q.lines s 116 placement reserve position (by decide) (by decide)
  · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using protect stack q.sp q.lines s 52 placement reserve position (by decide) (by decide)
  · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using protect stack q.sp q.lines s 40 placement reserve position (by decide) (by decide)
  · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using protect stack q.sp q.lines s 36 placement reserve position (by decide) (by decide)
  · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using protect stack q.sp q.lines s 32 placement reserve position (by decide) (by decide)
  · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using protect stack q.sp q.lines s 28 placement reserve position (by decide) (by decide)
  · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using protect stack q.sp q.lines s 24 placement reserve position (by decide) (by decide)

/-- Selecting an actor writes the target and slope globals; neither can
clobber the seven words used by the callback return sequence. -/
theorem actor_return (stack : Region) (q : Context) (s : X86Memory.State)
    (placement : Layout stack q.lines) (reserve : E1M1AimWalkRegions.Reserve stack q.sp)
    (position : s.regs 4=q.sp-140) : E1M1AimActorReturn.Safe s := by
  intro off member
  have fixed (n : Nat) (low : 4≤n) (high : n≤212) :
      Apart (q.sp-BitVec.ofNat 32 n) (0x2b9f8#32) ∧ Apart (q.sp-BitVec.ofNat 32 n) (0x2b9b4#32) := by
    exact ⟨FloorCaller.apart_symm (E1M1AimCallbackRegions.global_stack stack q.sp q.lines _ n placement reserve (by decide) low high),
      FloorCaller.apart_symm (E1M1AimCallbackRegions.global_stack stack q.sp q.lines _ n placement reserve (by decide) low high)⟩
  simp only [E1M1AimReturnFrame.slots,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rw [position]
  · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using fixed 140 (by decide) (by decide)
  · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using fixed 144 (by decide) (by decide)
  · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using fixed 148 (by decide) (by decide)
  · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using fixed 152 (by decide) (by decide)
  · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using fixed 156 (by decide) (by decide)
  · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using fixed 160 (by decide) (by decide)
  · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using fixed 164 (by decide) (by decide)

/-- Reuse the actual completed return chain with derived saved-word guards.
The preserved image and final stack position remain execution obligations. -/
theorem restores (stack : Region) (q : Context) (start finish : X86Control.State)
    (placement : Layout stack q.lines) (reserve : E1M1AimWalkRegions.Reserve stack q.sp)
    (position : start.core.regs 4=q.sp-140)
    (image : E1M1AimSavedCaller.Image start finish (q.sp-136))
    (finished : finish.core.regs 4=q.sp-136) :
    E1M1AimSavedCaller.Restores start (q.sp-136) (E1M1AimCompletedReturn.result finish) := by
  exact E1M1AimSavedCaller.restores start finish (q.sp-136) image finished
    (saved stack q start.core placement reserve position)
end Doom.Proofs.E1M1AimSavedRegions
