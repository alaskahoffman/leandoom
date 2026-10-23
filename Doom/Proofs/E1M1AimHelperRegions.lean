import Doom.Proofs.E1M1AimGlobalEntry
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
namespace Doom.Proofs.E1M1AimHelperRegions
open Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1NoiseAllocation (Region)
open E1M1CellWalkInvariant (Context)
open E1M1AimGlobalRegions (Layout)

/-- The record buffer and cursor end immediately before the opening globals.
This region is protected only through the callback, not collection or marking. -/
def recordArea : Region := ⟨0x2ba20,0x2c02c⟩

theorem opening_reads (stack : Region) (q : Context) (s : X86Memory.State) (a : Word)
    (placement : Layout stack q.lines) (reserve : E1M1AimWalkRegions.Reserve stack q.sp)
    (position : s.regs 4=q.sp-140) (inside : E1M1AimMapRegions.globalStores.Contains a)
    (fixed : ∀ b∈E1M1NoiseLineProgress.openingGlobals, Apart a b) :
    ∀ b∈E1M1AimOpeningFrame.writes (s.regs 4), Apart a b := by
  intro b hb
  simp only [E1M1AimOpeningFrame.writes,E1M1AimOpeningFrame.pushes,List.mem_append] at hb
  rcases hb with (early|late)|global
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at early
    rcases early with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp only [position,BitVec.sub_eq_add_neg,BitVec.add_assoc]
    all_goals exact E1M1AimGlobalRegions.push stack q.sp q.lines a _ placement reserve inside (by decide)
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at late
    rcases late with rfl|rfl|rfl|rfl
    all_goals simp only [position,BitVec.sub_eq_add_neg,BitVec.add_assoc]
    all_goals exact E1M1AimGlobalRegions.push stack q.sp q.lines a _ placement reserve inside (by decide)
  · exact fixed b global

/-- Read protection for the complete callback prologue, opening and clipping. -/
theorem read_word (stack : Region) (q : Context) (s : X86Memory.State) (a : Word)
    (placement : Layout stack q.lines) (reserve : E1M1AimWalkRegions.Reserve stack q.sp)
    (position : s.regs 4=q.sp-140) (inside : E1M1AimMapRegions.globalStores.Contains a)
    (fixed : ∀ b∈E1M1NoiseLineProgress.openingGlobals ++ [(0x2c1e4#32),0x2c1e8], Apart a b) :
    E1M1AimRecordFrame.ReadSafe s a := by
  have opening := opening_reads stack q s a placement reserve position inside
    (fun b hb => fixed b (List.mem_append_left _ hb))
  constructor
  · intro off ho
    apply opening
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
    rcases ho with rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp [E1M1AimOpeningFrame.writes,E1M1AimOpeningFrame.pushes]
  · intro b hb
    simp only [E1M1AimReturnFrame.writes,List.mem_append] at hb
    rcases hb with (locals|globals)|bounds
    · apply opening
      simp only [List.mem_cons,List.not_mem_nil,or_false] at locals
      rcases locals with rfl|rfl|rfl|rfl|rfl <;>
        simp [E1M1AimOpeningFrame.writes,E1M1AimOpeningFrame.pushes]
    · exact fixed b (List.mem_append_left _ globals)
    · exact fixed b (List.mem_append_right _ bounds)

theorem record_word (stack : Region) (q : Context) (s : X86Memory.State) (a : Word)
    (placement : Layout stack q.lines) (reserve : E1M1AimWalkRegions.Reserve stack q.sp)
    (position : s.regs 4=q.sp-140) (inside : recordArea.Contains a) :
    E1M1AimRecordFrame.ReadSafe s a := by
  apply read_word stack q s a placement reserve position
  · simp only [recordArea,Region.Contains] at inside
    simp only [E1M1AimMapRegions.globalStores,Region.Contains]
    omega
  · intro b hb
    have small : (E1M1AimObjectRegions.region b 4).Contains b ∧
        recordArea.Disjoint (E1M1AimObjectRegions.region b 4) := by
      simp only [E1M1NoiseLineProgress.openingGlobals,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hb
      rcases hb with (rfl|rfl|rfl|rfl)|(rfl|rfl) <;> exact ⟨by decide,by decide⟩
    exact Region.apart inside small.1 small.2

theorem records (stack : Region) (q : Context) (s : X86Memory.State) (hits : Array Intercept)
    (placement : Layout stack q.lines) (reserve : E1M1AimWalkRegions.Reserve stack q.sp)
    (position : s.regs 4=q.sp-140) (capacity : hits.size≤128) :
    E1M1AimRecordFrame.RecordsSafe s hits := by
  intro i hi off ho
  apply record_word stack q s _ placement reserve position
  have inside := E1M1AimCellWalk.buffer_word i (by omega) off ho
  simp only [E1M1AimCellWalk.buffer,Region.Contains] at inside
  simpa [recordArea,Region.Contains,E1M1MinimumScan.address,OriginalLineCollection.slot,
    BitVec.ofNat_add] using (show 0x2ba20≤(OriginalLineCollection.slot 0x2ba20 i off).toNat ∧
      (OriginalLineCollection.slot 0x2ba20 i off).toNat+4≤0x2c02c ∧ 0x2c02c≤2^32 by omega)

theorem cursor (stack : Region) (q : Context) (s : X86Memory.State)
    (placement : Layout stack q.lines) (reserve : E1M1AimWalkRegions.Reserve stack q.sp)
    (position : s.regs 4=q.sp-140) : E1M1AimRecordFrame.ReadSafe s 0x2c028 := by
  exact record_word stack q s _ placement reserve position (by decide)

/-- These are reads before clipping. The lower/upper stores have not happened. -/
theorem clipping_reads (stack : Region) (q : Context) (s : X86Memory.State)
    (placement : Layout stack q.lines) (reserve : E1M1AimWalkRegions.Reserve stack q.sp)
    (position : s.regs 4=q.sp-140) :
    E1M1AimFloorEntry.ReadSafe s ∧ E1M1AimCeilingEntry.ReadSafe s := by
  have guard (a : Word) (member : a∈[(0x2b9a8#32),0x2c1e4,0x2c1e8]) :=
    opening_reads stack q s a placement reserve position
      (by simp only [List.mem_cons,List.not_mem_nil,or_false] at member
          rcases member with rfl|rfl|rfl <;> decide)
      (by intro b hb
          simp only [E1M1NoiseLineProgress.openingGlobals,List.mem_cons,List.not_mem_nil,or_false] at member hb
          rcases member with rfl|rfl|rfl <;> rcases hb with rfl|rfl|rfl|rfl <;> unfold Apart <;> decide)
  constructor <;> intro a ha <;> apply guard a
  all_goals simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
  all_goals rcases ha with rfl|rfl <;> simp

theorem return_safe (stack : Region) (q : Context) (s : X86Memory.State)
    (placement : Layout stack q.lines) (reserve : E1M1AimWalkRegions.Reserve stack q.sp)
    (position : s.regs 4=q.sp-140) : E1M1AimReturnFrame.Safe s := by
  intro off ho a ha
  have inside : E1M1AimMapRegions.globalStores.Contains a := by
    simp only [E1M1NoiseLineProgress.openingGlobals,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with (rfl|rfl|rfl|rfl)|(rfl|rfl) <;> decide
  apply FloorCaller.apart_symm
  simp only [E1M1AimReturnFrame.slots,List.mem_cons,List.not_mem_nil,or_false] at ho
  rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp only [position,BitVec.sub_eq_add_neg,BitVec.add_assoc]
  all_goals exact E1M1AimGlobalRegions.push stack q.sp q.lines a _ placement reserve inside (by decide)

theorem helper (stack : Region) (q : Context) (s : X86Memory.State)
    (placement : Layout stack q.lines) (reserve : E1M1AimWalkRegions.Reserve stack q.sp)
    (position : s.regs 4=q.sp-140) : E1M1AimOpening.CallerSafe s := by
  intro a ha b hb
  have inside : E1M1AimMapRegions.globalStores.Contains b := by
    simp only [E1M1NoiseLineProgress.openingGlobals,List.mem_cons,List.not_mem_nil,or_false] at hb
    rcases hb with rfl|rfl|rfl|rfl <;> decide
  apply FloorCaller.apart_symm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl|rfl|rfl
  all_goals simp only [position,BitVec.sub_eq_add_neg,BitVec.add_assoc]
  all_goals exact E1M1AimGlobalRegions.push stack q.sp q.lines b _ placement reserve inside (by decide)

/-- All eleven fixed callback-layout fields follow from placement and capacity.
This does not establish either premise for reachable play. -/
theorem layout (stack : Region) (q : Context) (s : X86Memory.State) (hits : Array Intercept)
    (placement : Layout stack q.lines) (reserve : E1M1AimWalkRegions.Reserve stack q.sp)
    (position : s.regs 4=q.sp-140) (capacity : hits.size≤128) :
    E1M1AimCycleInvariant.Layout s hits := by
  have selected := E1M1AimCallbackRegions.selection stack q placement.caller reserve
  have upper := E1M1AimSavedRegions.ordered stack q.sp q.lines s 136 placement.caller reserve position (by decide) (by decide)
  have slot : s.regs 4+4=q.sp-136 := by simp [position,BitVec.sub_eq_add_neg,BitVec.add_assoc]
  have bounds := fun a ha => E1M1AimGlobalRegions.push stack q.sp q.lines a (-140#32) placement reserve ha (by decide)
  exact {
    returnSafe := return_safe stack q s placement reserve position
    recordsSafe := records stack q s hits placement reserve position capacity
    cursorSafe := cursor stack q s placement reserve position
    floorReads := (clipping_reads stack q s placement reserve position).1
    ceilingReads := (clipping_reads stack q s placement reserve position).2
    helperSafe := helper stack q s placement reserve position
    targetSafe := by rw [slot]; exact upper.2.2.1
    cursorStore := by rw [position]; exact selected.2.2
    recordStore := fun i hi off ho => by rw [position]; exact selected.2.1 i (by omega) off ho
    boundsStore := by
      simpa [position,BitVec.sub_eq_add_neg] using
        And.intro (bounds 0x2c1e4 (by decide)) (bounds 0x2c1e8 (by decide))
    slotSafe := by rw [slot]; exact upper.1
  }

/-- Apply the derived record guard to the actual open-line callback. The parent
may subsequently mark the selected fraction; that later store is not hidden. -/
theorem callback_records (stack : Region) (q : Context) (s : X86Memory.State)
    (hit : Intercept) (line front back ff fc bf bc : Word) (hits : Array Intercept)
    (lookup : Intercept → Word)
    (placement : Layout stack q.lines) (reserve : E1M1AimWalkRegions.Reserve stack q.sp)
    (position : s.regs 4=q.sp-140) (capacity : hits.size≤128)
    (input : E1M1AimMapped.Inputs s hit line front back ff fc bf bc)
    (image : OriginalLineFinish.Encodes s.memory 0x2ba20 lookup hits) :
    OriginalLineFinish.Encodes (E1M1AimWindow.result s).core.memory 0x2ba20 lookup hits := by
  exact E1M1AimRecordFrame.records s hit line front back ff fc bf bc input hits lookup image
    (records stack q s hits placement reserve position capacity)
end Doom.Proofs.E1M1AimHelperRegions
