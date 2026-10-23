import Doom.Proofs.E1M1AimCellRegions
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
namespace Doom.Proofs.E1M1AimCellEntry
open Verification X86 X86Memory X86Control BlockSummary
open E1M1NoiseAllocation (Region)
open E1M1CellWalkInvariant (Context Cell)
open E1M1AimCellRegions (Layout)
attribute [local irreducible] load32

/-- The blocklinks pointer is disjoint from every actual setup-global store. -/
theorem global_apart : ∀ b∈E1M1AimSetupFootprint.globals, Apart (0x2c0f8#32) b := by
  intro b member
  simp only [E1M1AimSetupFootprint.globals,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> unfold Apart <;> decide

theorem reads_safe (stack : Region) (s : X86Memory.State) (q : Context) (c : Cell)
    (reserve : E1M1AimSetupFootprint.Reserve stack s) (placement : Layout stack q c) :
    ∀ a∈E1M1AimRetryData.cellReads q c, E1M1PathMapQuery.Safe s a := by
  intro a member
  rcases E1M1AimCellRegions.reads stack q c placement a member with located|rfl
  · exact E1M1AimObjectRegions.setup_safe stack s a reserve located
  · exact E1M1AimSetupFootprint.region_safe stack (E1M1AimObjectRegions.region 0x2c0f8 4)
      s _ reserve (by decide) placement.globalStack global_apart

/-- Derive every field of the existing cell-payload guard from storage and the
signed grid check. No reached memory image or per-read safe premise is needed. -/
theorem safe (stack : Region) (s : X86Memory.State) (q : Context) (c : Cell)
    (reserve : E1M1AimSetupFootprint.Reserve stack s) (placement : Layout stack q c) :
    E1M1AimPreRayMemory.PayloadSafe s q c := by
  have allReads := reads_safe stack s q c reserve placement
  have line (i : Fin c.cell.ids.length) (a : Word)
      (member : a∈E1M1ScanMemory.lineReads (E1M1ScanGeometry.linePointer q.lines c.cell.ids[i.val])
        (c.data i.val).v (c.data i.val).w ++ [E1M1ScanGeometry.linePointer q.lines c.cell.ids[i.val]+50]) :=
    allReads a (by simp only [E1M1AimRetryData.cellReads,List.mem_append]; exact Or.inl (Or.inl
      (List.mem_flatMap.mpr ⟨i,by simp,member⟩)))
  have node (n : E1M1ThingList.Node) (member : n∈c.nodes) (a : Word)
      (field : a∈[n.pointer+12,n.pointer+16,n.pointer+64,n.pointer+44]) :=
    allReads a (by simp only [E1M1AimRetryData.cellReads,List.mem_append]; exact Or.inl (Or.inr
      (List.mem_flatMap.mpr ⟨n,member,field⟩)))
  refine ⟨fun i a ha => line i a (List.mem_append_left _ ha),
    fun i => line i _ (List.mem_append_right _ (by simp)),?_,
    fun n hn => node n hn _ (by simp),allReads _ (by simp [E1M1AimRetryData.cellReads]),
    allReads _ (by simp [E1M1AimRetryData.cellReads])⟩
  intro n hn off ho
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
  rcases ho with rfl|rfl|rfl <;> exact node n hn _ (by simp)

theorem traversal (stack : Region) (s : X86Memory.State) (q : Context) (c : Cell)
    (reserve : E1M1AimSetupFootprint.Reserve stack s) (placement : Layout stack q c)
    (before : E1M1QueryImages.Payload s.memory q c) :
    E1M1QueryImages.Payload (E1M1PathMapQuery.traversal s).core.memory q c ∧
    E1M1QueryImages.Protected (E1M1PathMapQuery.traversal s).core q c := by
  exact E1M1AimPreRayMemory.payload s q c before (safe stack s q c reserve placement)

/-- Follow the real outer prologue and query setup from the original payload.
The shooter-angle guard remains explicit; storage placement and encoding are
still hypotheses, not reachable-state allocation facts. -/
theorem controller (stack : Region) (s : X86Memory.State) (f : Option Flags)
    (angle : Angle) (q : Context) (c : Cell)
    (room : stack.lo+124≤(s.regs 4).toNat) (top : (s.regs 4).toNat≤stack.hi)
    (bound : stack.hi≤2^32) (placement : Layout stack q c)
    (value : load32 s.memory (s.regs 0+32)=angle.raw.toBitVec)
    (angleSafe : ∀ b∈OriginalBulletSlope.saveWrites s, Apart (s.regs 0+32) b)
    (before : E1M1QueryImages.Payload s.memory q c) :
    E1M1QueryImages.Payload
      (E1M1PathMapQuery.traversal (E1M1AimControllerEntry.entry s f).core).core.memory q c ∧
    E1M1QueryImages.Protected
      (E1M1PathMapQuery.traversal (E1M1AimControllerEntry.entry s f).core).core q c := by
  have regs := E1M1AimControllerInputs.registers s f angle value angleSafe
  have reserve := E1M1AimSetupFootprint.controller_reserve stack s angle room top bound
  have outerReserve : E1M1AimRegions.StackReserve stack s := ⟨by omega,top,bound⟩
  have entered := E1M1AimControllerInputs.payload q c s f angle regs
    ⟨before,safe stack _ q c reserve placement⟩
    (E1M1AimRegions.safe_reads stack s _ outerReserve (E1M1AimCellRegions.covered stack q c placement))
  exact E1M1AimPreRayMemory.payload _ q c entered.1 entered.2
end Doom.Proofs.E1M1AimCellEntry
