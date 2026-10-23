import Doom.Proofs.E1M1AimSavedEntry
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
namespace Doom.Proofs.E1M1AimCallerRegions
open Verification X86 X86Memory X86Control BlockSummary
open E1M1NoiseAllocation (Region)
open E1M1CellWalkInvariant (Context)
open E1M1AimCallbackRegions (Layout)

/-- Path setup starts below the existing caller area. This is a relative byte
proof and does not require the stack base itself to be nonwrapping. -/
theorem above (sp : Word) (n : Nat) (off : Word) (low : 4≤n) (high : n≤52)
    (deeper : 2^32-212≤off.toNat ∧ off.toNat≤2^32-56) :
    Apart (sp-BitVec.ofNat 32 n) (sp+off) := by
  simp only [BitVec.sub_eq_add_neg]
  apply OriginalPathXStep.apart_translate
  intro i j same
  have ii := i.isLt; have jj := j.isLt
  have equal := congrArg BitVec.toNat same
  simp only [BitVec.toNat_add,BitVec.toNat_neg,BitVec.toNat_ofNat] at equal
  omega

/-- Protect the upper caller words from path initialization and axis setup.
These words already exist at path entry, including its newly created return. -/
theorem setup (stack : Region) (q : Context) (s : X86Memory.State) (n : Nat)
    (placement : Layout stack q.lines) (reserve : E1M1AimWalkRegions.Reserve stack q.sp)
    (position : s.regs 4=q.sp-52) (low : 4≤n) (high : n≤52) :
    E1M1PathMapSetup.Safe s (q.sp-BitVec.ofNat 32 n) := by
  have fixed (a : Word) (inside : E1M1AimMapRegions.globalStores.Contains a) :=
    FloorCaller.apart_symm (E1M1AimCallbackRegions.global_stack stack q.sp q.lines a n placement reserve inside low (by omega))
  have push (off : Word) (fits : 2^32-212≤off.toNat ∧ off.toNat≤2^32-56) :
      Apart (q.sp+ -BitVec.ofNat 32 n) (q.sp+off) := by
    simpa only [BitVec.sub_eq_add_neg] using above q.sp n off low high fits
  constructor
  · intro b member
    simp [OriginalPathInit.writes] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · simp only [position,BitVec.sub_eq_add_neg,BitVec.add_assoc]
      exact push _ (by decide)
    · simp only [position,BitVec.sub_eq_add_neg,BitVec.add_assoc]
      exact push _ (by decide)
    · simp only [position,BitVec.sub_eq_add_neg,BitVec.add_assoc]
      exact push _ (by decide)
    · exact fixed _ (by decide)
    · exact fixed _ (by decide)
    · exact fixed _ (by decide)
    · exact fixed _ (by decide)
    · exact fixed _ (by decide)
    · exact fixed _ (by decide)
    · exact fixed _ (by decide)
    · simp only [position,BitVec.sub_eq_add_neg,BitVec.add_assoc]
      exact push _ (by decide)
    · simp only [position,BitVec.sub_eq_add_neg,BitVec.add_assoc]
      exact push _ (by decide)
    · simp only [position,BitVec.sub_eq_add_neg,BitVec.add_assoc]
      exact push _ (by decide)
    · simp only [position,BitVec.sub_eq_add_neg,BitVec.add_assoc]
      exact push _ (by decide)
    · simp only [position,BitVec.sub_eq_add_neg,BitVec.add_assoc]
      exact push _ (by decide)
  · intro off member
    simp only [E1M1PathMapSetup.offsets,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp only [position,BitVec.sub_eq_add_neg,BitVec.add_assoc]
    all_goals exact push _ (by decide)

/-- Selection's six stores, cursor update and callback CALL are all below or
outside the caller area. -/
theorem selection (stack : Region) (q : Context) (n : Nat)
    (placement : Layout stack q.lines) (reserve : E1M1AimWalkRegions.Reserve stack q.sp)
    (low : 4≤n) (high : n≤52) :
    E1M1AimEntryFrame.SafeWord (q.sp-112) (q.sp-BitVec.ofNat 32 n) := by
  have push (off : Word) (fits : 2^32-212≤off.toNat ∧ off.toNat≤2^32-56) :
      Apart (q.sp+ -BitVec.ofNat 32 n) (q.sp+off) := by
    simpa only [BitVec.sub_eq_add_neg] using above q.sp n off low high fits
  refine ⟨?_,FloorCaller.apart_symm (E1M1AimCallbackRegions.global_stack stack q.sp q.lines _ n
    placement reserve (by decide) low (by omega)),?_⟩
  · intro off member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    all_goals exact push _ (by decide)
  · simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    exact push _ (by decide)

theorem path_guard (stack : Region) (q : Context) (s : X86Memory.State) (n : Nat)
    (placement : Layout stack q.lines) (reserve : E1M1AimWalkRegions.Reserve stack q.sp)
    (position : s.regs 4=q.sp-52) (low : 4≤n) (high : n≤52) :
    E1M1AimQueryCatalog.Protected q s (q.sp-BitVec.ofNat 32 n) := by
  exact ⟨setup stack q s n placement reserve position low high,
    E1M1AimCallbackRegions.upper_collection stack q.sp q.lines n placement reserve low (by omega),
    selection stack q n placement reserve low high⟩

/-- Rebase the address-only guard from aim entry to its known path-entry layout.
This does not assert that the earlier aim setup preserves every old value. -/
theorem later (stack : Region) (q : Context) (s : X86Memory.State) (n : Nat)
    (placement : Layout stack q.lines) (reserve : E1M1AimWalkRegions.Reserve stack q.sp)
    (position : s.regs 4=q.sp-24) (low : 4≤n) (high : n≤52) :
    E1M1AimPreRayMemory.Later q s (q.sp-BitVec.ofNat 32 n) := by
  apply path_guard stack q (E1M1AimPreRayMemory.layout s) n placement reserve ?_ low high
  simp [E1M1AimPreRayMemory.layout,E1M1PathMapQuery.withStack,write,position,BitVec.sub_sub]

theorem callers (stack : Region) (q : Context) (s : X86Memory.State)
    (placement : Layout stack q.lines) (reserve : E1M1AimWalkRegions.Reserve stack q.sp)
    (position : s.regs 4=q.sp-24) :
    ∀ off∈E1M1AimQueryCaller.callerSlots, E1M1AimPreRayMemory.Later q s ((q.sp-136)+off) := by
  intro off member
  simp only [E1M1AimQueryCaller.callerSlots,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl
  · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using later stack q s 52 placement reserve position (by decide) (by decide)
  · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using later stack q s 40 placement reserve position (by decide) (by decide)
  · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using later stack q s 36 placement reserve position (by decide) (by decide)
  · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using later stack q s 32 placement reserve position (by decide) (by decide)
  · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using later stack q s 28 placement reserve position (by decide) (by decide)
  · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using later stack q s 24 placement reserve position (by decide) (by decide)

/-- Apply the existing setup/collection/selection memory relation to a caller
word at actual path entry. Execution and its memory frame are still required. -/
theorem word (stack : Region) (q : Context) (s : X86Memory.State) (out : X86Control.State) (n : Nat)
    (placement : Layout stack q.lines) (reserve : E1M1AimWalkRegions.Reserve stack q.sp)
    (position : s.regs 4=q.sp-52) (low : 4≤n) (high : n≤52)
    (frame : ∀ a, E1M1PathMapSetup.Safe s a → E1M1FiringMapState.Safe q.sp q.lines a →
      E1M1AimEntryFrame.SafeWord (q.sp-112) a → load32 out.core.memory a=load32 s.memory a) :
    load32 out.core.memory (q.sp-BitVec.ofNat 32 n)=load32 s.memory (q.sp-BitVec.ofNat 32 n) := by
  have guard := path_guard stack q s n placement reserve position low high
  exact frame _ guard.1 guard.2.1 guard.2.2
end Doom.Proofs.E1M1AimCallerRegions
