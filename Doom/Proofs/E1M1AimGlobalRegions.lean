import Doom.Proofs.E1M1AimCallerEntry
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
namespace Doom.Proofs.E1M1AimGlobalRegions
open Verification X86 X86Memory X86Control BlockSummary
open E1M1NoiseAllocation (Region)
open E1M1CellWalkInvariant (Context)

/-- Aim setup creates these values; path setup, collection and selection must
preserve them. The clipping bounds are intentionally absent from stable. -/
def values : List Word := [0x2b9b8,0x2b9a8,0x2b9ac,0x2c1e4,0x2c1e8,0x2b9f8]
def stable : List Word := [0x2b9b8,0x2b9a8,0x2b9ac,0x2b9f8]

structure Layout (stack : Region) (lines : Word) : Prop where
  caller : E1M1AimCallbackRegions.Layout stack lines
  linesGlobals : (E1M1AimStaticRegions.linedefs lines).Disjoint E1M1AimMapRegions.globalStores

theorem contained (a : Word) (member : a∈values) : E1M1AimMapRegions.globalStores.Contains a := by
  simp only [values,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl <;> decide

theorem array (a : Word) (member : a∈values) : OriginalLineMixedInvariant.ArraySafe 0x2ba20 a := by
  have bytes : (E1M1AimObjectRegions.region a 4).Contains a ∧
      (E1M1AimObjectRegions.region a 4).Disjoint E1M1AimCellWalk.buffer ∧ Apart a (0x2c028#32) := by
    simp only [values,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl <;>
      refine ⟨by decide,by decide,?_⟩ <;> unfold Apart <;> decide
  exact ⟨fun k hk off ho => Region.apart bytes.1 (E1M1AimCellWalk.buffer_word k hk off ho) bytes.2.1,bytes.2.2⟩

/-- Generic fixed-global/stack separation, also usable for helper reads. -/
theorem push (stack : Region) (sp lines a off : Word) (placement : Layout stack lines)
    (reserve : E1M1AimWalkRegions.Reserve stack sp)
    (inside : E1M1AimMapRegions.globalStores.Contains a)
    (fits : 2^32-212≤off.toNat ∧ off.toNat≤2^32-4) : Apart a (sp+off) := by
  apply Region.apart inside ?_ placement.caller.globalsStack
  have size := sp.isLt
  simp only [E1M1AimWalkRegions.Reserve] at reserve
  simp only [Region.Contains,BitVec.toNat_add]
  omega

theorem collection (stack : Region) (q : Context) (a : Word)
    (placement : Layout stack q.lines) (reserve : E1M1AimWalkRegions.Reserve stack q.sp)
    (member : a∈values) : E1M1FiringMapState.Safe q.sp q.lines a := by
  exact E1M1AimCellWalk.word stack E1M1AimMapRegions.globalStores q.sp q.lines a reserve
    (contained a member) placement.caller.globalsStack (array a member)
    (fun j hj => Region.apart (contained a member)
      (E1M1AimStaticRegions.line_stamp q.lines placement.caller.lineBound j hj) placement.linesGlobals.symm)

/-- These aim globals survive path setup, not the earlier aim setup that writes
them. Fixed-global writes are checked individually at this phase boundary. -/
theorem path_setup (stack : Region) (q : Context) (s : X86Memory.State) (a : Word)
    (placement : Layout stack q.lines) (reserve : E1M1AimWalkRegions.Reserve stack q.sp)
    (position : s.regs 4=q.sp-52) (member : a∈values) : E1M1PathMapSetup.Safe s a := by
  have stackWrite (off : Word) (fits : 2^32-212≤off.toNat ∧ off.toNat≤2^32-4) :=
    push stack q.sp q.lines a off placement reserve (contained a member) fits
  have fixed (b : Word) (hb : b∈[(0x2c028#32),0x2c024,0x13580,0x2ba18,0x2ba10,0x2ba14,0x2ba1c]) : Apart a b := by
    simp only [values,List.mem_cons,List.not_mem_nil,or_false] at member hb
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl <;>
      rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> unfold Apart <;> decide
  constructor
  · intro b hb
    simp [OriginalPathInit.writes] at hb
    rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · simp only [position,BitVec.sub_eq_add_neg,BitVec.add_assoc]
      exact stackWrite _ (by decide)
    · simp only [position,BitVec.sub_eq_add_neg,BitVec.add_assoc]
      exact stackWrite _ (by decide)
    · simp only [position,BitVec.sub_eq_add_neg,BitVec.add_assoc]
      exact stackWrite _ (by decide)
    · exact fixed _ (by simp)
    · exact fixed _ (by simp)
    · exact fixed _ (by simp)
    · exact fixed _ (by simp)
    · exact fixed _ (by simp)
    · exact fixed _ (by simp)
    · exact fixed _ (by simp)
    · simp only [position,BitVec.sub_eq_add_neg,BitVec.add_assoc]
      exact stackWrite _ (by decide)
    · simp only [position,BitVec.sub_eq_add_neg,BitVec.add_assoc]
      exact stackWrite _ (by decide)
    · simp only [position,BitVec.sub_eq_add_neg,BitVec.add_assoc]
      exact stackWrite _ (by decide)
    · simp only [position,BitVec.sub_eq_add_neg,BitVec.add_assoc]
      exact stackWrite _ (by decide)
    · simp only [position,BitVec.sub_eq_add_neg,BitVec.add_assoc]
      exact stackWrite _ (by decide)
  · intro off ho
    simp only [E1M1PathMapSetup.offsets,List.mem_cons,List.not_mem_nil,or_false] at ho
    rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp only [position,BitVec.sub_eq_add_neg,BitVec.add_assoc]
    all_goals exact stackWrite _ (by decide)

theorem selection (stack : Region) (q : Context) (a : Word)
    (placement : Layout stack q.lines) (reserve : E1M1AimWalkRegions.Reserve stack q.sp)
    (member : a∈values) : E1M1AimEntryFrame.SafeWord (q.sp-112) a := by
  have stackWrite (off : Word) (fits : 2^32-212≤off.toNat ∧ off.toNat≤2^32-4) :=
    push stack q.sp q.lines a off placement reserve (contained a member) fits
  refine ⟨?_,(array a member).2,?_⟩
  · intro off ho
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
    rcases ho with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    all_goals exact stackWrite _ (by decide)
  · simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    exact stackWrite _ (by decide)

theorem later (stack : Region) (q : Context) (s : X86Memory.State) (a : Word)
    (placement : Layout stack q.lines) (reserve : E1M1AimWalkRegions.Reserve stack q.sp)
    (position : s.regs 4=q.sp-24) (member : a∈values) : E1M1AimPreRayMemory.Later q s a := by
  refine ⟨path_setup stack q (E1M1AimPreRayMemory.layout s) a placement reserve ?_ member,
    collection stack q a placement reserve member,selection stack q a placement reserve member⟩
  simp [E1M1AimPreRayMemory.layout,E1M1PathMapQuery.withStack,write,position,BitVec.sub_sub]

/-- Continuing callbacks preserve this smaller set. A target-selection callback
may still write the target word; StableWord does not claim otherwise. -/
theorem ordered (stack : Region) (q : Context) (s : X86Memory.State) (a : Word)
    (placement : Layout stack q.lines) (reserve : E1M1AimWalkRegions.Reserve stack q.sp)
    (position : s.regs 4=q.sp-140) (member : a∈stable) : E1M1AimMapFrame.StableWord s a := by
  have hv : a∈values := by
    simp only [stable,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl <;> simp [values]
  have stackWrite (off : Word) (fits : 2^32-212≤off.toNat ∧ off.toNat≤2^32-4) :=
    push stack q.sp q.lines a off placement reserve (contained a hv) fits
  have fixed (b : Word) (hb : b∈E1M1NoiseLineProgress.openingGlobals ++ [(0x2c1e4#32),0x2c1e8]) : Apart a b := by
    simp only [stable,E1M1NoiseLineProgress.openingGlobals,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member hb
    rcases member with rfl|rfl|rfl|rfl <;>
      rcases hb with (rfl|rfl|rfl|rfl)|(rfl|rfl) <;> unfold Apart <;> decide
  refine ⟨⟨?_,?_⟩,?_,(array a hv).2,?_⟩
  · intro off ho
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
    rcases ho with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp only [position,BitVec.sub_eq_add_neg,BitVec.add_assoc]
    all_goals exact stackWrite _ (by decide)
  · intro b hb
    simp only [E1M1AimReturnFrame.writes,List.mem_append] at hb
    rcases hb with (locals|opening)|clip
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at locals
      rcases locals with rfl|rfl|rfl|rfl|rfl
      all_goals simp only [position,BitVec.sub_eq_add_neg,BitVec.add_assoc]
      all_goals exact stackWrite _ (by decide)
    · exact fixed b (List.mem_append_left _ opening)
    · exact fixed b (List.mem_append_right _ clip)
  · intro i hi
    simpa [E1M1MinimumScan.address,OriginalLineCollection.slot,BitVec.ofNat_add] using (array a hv).1 i hi 0 (by simp)
  · simp only [position,BitVec.sub_eq_add_neg]
    exact stackWrite _ (by decide)

/-- Floor clipping can update the bottom slope while preserving the ceiling,
shoot height and upper slope needed by the following ceiling branch. -/
theorem clip (stack : Region) (q : Context) (s : X86Memory.State)
    (placement : Layout stack q.lines) (reserve : E1M1AimWalkRegions.Reserve stack q.sp)
    (position : s.regs 4=q.sp-140) : E1M1AimNextLine.ClipGlobalsSafe s := by
  intro a ha b hb
  have inside : E1M1AimMapRegions.globalStores.Contains a := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl <;> decide
  have fixed : Apart a (0x2c1e4#32) := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl <;> unfold Apart <;> decide
  have stackWrite (off : Word) (fits : 2^32-212≤off.toNat ∧ off.toNat≤2^32-4) :=
    push stack q.sp q.lines a off placement reserve inside fits
  simp only [E1M1AimClipFrame.writes,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl
  · simp only [position,BitVec.sub_eq_add_neg,BitVec.add_assoc]; exact stackWrite _ (by decide)
  · simp only [position,BitVec.sub_eq_add_neg,BitVec.add_assoc]; exact stackWrite _ (by decide)
  · simp only [position,BitVec.sub_eq_add_neg,BitVec.add_assoc]; exact stackWrite _ (by decide)
  · simp only [position,BitVec.sub_eq_add_neg,BitVec.add_assoc]; exact stackWrite _ (by decide)
  · exact fixed
/-- Apply the derived floor-write guard to the actual helper result. The
bottom slope can change while these three later inputs keep their values. -/
theorem floor_word (stack : Region) (q : Context) (s : X86Memory.State) (a : Word)
    (placement : Layout stack q.lines) (reserve : E1M1AimWalkRegions.Reserve stack q.sp)
    (position : s.regs 4=q.sp-164) (member : a∈[(0x2c034#32),0x2b9a8,0x2c1e8]) :
    load32 (E1M1AimFloor.result s).core.memory a=load32 s.memory a := by
  have guard := clip stack q (E1M1AimQueryCatalog.view q s) placement reserve rfl
  apply E1M1AimClipFrame.floor_frame s a
  intro b hb
  exact guard a member b (by
    simpa [E1M1AimQueryCatalog.view,put,write,position,BitVec.sub_sub] using hb)
end Doom.Proofs.E1M1AimGlobalRegions
