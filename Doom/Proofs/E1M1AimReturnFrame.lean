import Doom.Proofs.E1M1AimCeilingEntry
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1AimReturnFrame
open Verification X86 X86Memory X86Control BlockSummary Collision
attribute [local irreducible] load32 store32

def writes (sp : Word) : List Word := [sp-(28#32),sp-(32#32),sp-(36#32),sp-(40#32),sp-(44#32)] ++
  E1M1NoiseLineProgress.openingGlobals ++ [(0x2c1e4#32),(0x2c1e8#32)]
def slots : List Word := [0,4,8,12,16,20,24]
def Safe (s : X86Memory.State) : Prop :=
  ∀ off∈slots, ∀ a∈E1M1NoiseLineProgress.openingGlobals ++ [(0x2c1e4#32),(0x2c1e8#32)],
    Apart (s.regs 4-off) a

theorem ceiling_sp (s : X86Memory.State) : (E1M1AimCeiling.result s).core.regs 4=s.regs 4 := by
  have h := (OriginalDivMemory.restored_registers (E1M1AimCeiling.call s)).2.2.2.1
  unfold E1M1AimCeiling.result
  split
  · simp [OriginalAimCeiling.gate,OriginalAimCeiling.c3,OriginalAimCeiling.c2,OriginalAimCeiling.c1,put,write]
  · simp only [OriginalAimCeiling.clipped]
    split <;> simp only [OriginalAimCeiling.lowered,E1M1AimCeiling.divided]
    all_goals
      rw [h]
      simp [E1M1AimCeiling.call,E1M1AimCeiling.input,OriginalAimCeiling.called,OriginalAimCeiling.argument,OriginalAimCeiling.distance,OriginalAimCeiling.eye,OriginalAimCeiling.loaded,OriginalAimCeiling.c3,OriginalAimCeiling.c2,OriginalAimCeiling.c1,X86Routine.pushWord,put,write,BitVec.sub_add_cancel]

theorem stack (s : X86Memory.State) (hit : Intercept) (line front back ff fc bf bc : Word)
    (h : E1M1AimMapped.Inputs s hit line front back ff fc bf bc) :
    (E1M1AimCeilingEntry.result s).core.regs 4=s.regs 4-(24#32) := by
  rw [E1M1AimCeilingEntry.result,ceiling_sp]
  exact (E1M1AimClipFrame.floor_regs (E1M1AimFloorEntry.reached s)).2.1.trans
    (E1M1AimFloorEntry.inputs s hit line front back ff fc bf bc h).2.2.2

/-- Preserve protected words relative to the completed prologue, so its saved
register values can survive opening and both clipping branches. -/
theorem frame (s : X86Memory.State) (hit : Intercept) (line front back ff fc bf bc a : Word)
    (h : E1M1AimMapped.Inputs s hit line front back ff fc bf bc)
    (safe : ∀ b∈writes (s.regs 4), Apart a b) :
    load32 (E1M1AimCeilingEntry.result s).core.memory a=load32 (OriginalAimGuard.saved s).memory a := by
  have floorSp := (E1M1AimFloorEntry.inputs s hit line front back ff fc bf bc h).2.2.2
  have ceilingSp : (E1M1AimCeilingEntry.reached s).regs 4=s.regs 4-(24#32) :=
    (E1M1AimClipFrame.floor_regs (E1M1AimFloorEntry.reached s)).2.1.trans floorSp
  unfold E1M1AimCeilingEntry.result
  rw [E1M1AimCeiling.frame]
  · change load32 (E1M1AimFloor.result (E1M1AimFloorEntry.reached s)).core.memory a=_
    rw [E1M1AimClipFrame.floor_frame]
    · rw [E1M1AimFloorEntry.memory]
      change load32 (E1M1NoiseOpening.result (E1M1AimOpeningFrame.helper s)).core.memory a=_
      rw [E1M1AimOpeningFrame.opening_frame]
      · change load32 (store32 (E1M1AimOpeningFrame.caller s).memory
          ((E1M1AimOpeningFrame.caller s).regs 4-(4#32)) (0x2b786#32)) a=_
        rw [(E1M1AimOpeningFrame.stack s).1]
        simp only [BitVec.sub_sub]
        rw [load_store_apart _ _ _ _ (safe _ (by simp [writes]))]
        rfl
      · intro b hb; apply safe b
        simp [E1M1OpeningHeights.saves,(E1M1AimOpeningFrame.stack s).2,BitVec.sub_sub] at hb
        rcases hb with rfl|rfl|rfl|rfl|hb <;> simp_all [writes]
    · intro b hb; apply safe b
      simp [E1M1AimClipFrame.writes,floorSp,BitVec.sub_sub] at hb
      rcases hb with rfl|rfl|rfl|rfl|rfl <;> simp [writes]
  · intro b hb; apply safe b
    simp [E1M1AimCeiling.writes,ceilingSp,BitVec.sub_sub] at hb
    rcases hb with rfl|rfl|rfl|rfl|rfl <;> simp [writes]

theorem stack_apart (sp off other : Word) (member : off∈slots)
    (below : other∈[(28#32),32,36,40,44]) : Apart (sp-off) (sp-other) := by
  have small : Apart (-off) (-other) := by
    simp only [slots,List.mem_cons,List.not_mem_nil,or_false] at member below
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      rcases below with rfl|rfl|rfl|rfl|rfl <;> unfold Apart <;> decide
  simpa only [BitVec.sub_eq_add_neg] using OriginalPathXStep.apart_translate sp (-off) (-other) small

theorem saved_slot (s : X86Memory.State) (hit : Intercept) (line front back ff fc bf bc off : Word)
    (h : E1M1AimMapped.Inputs s hit line front back ff fc bf bc)
    (safe : Safe s) (member : off∈slots) :
    load32 (E1M1AimCeilingEntry.result s).core.memory (s.regs 4-off)=
      load32 (OriginalAimGuard.saved s).memory (s.regs 4-off) := by
  apply frame s hit line front back ff fc bf bc _ h
  intro b hb
  simp only [writes,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with ((rfl|rfl|rfl|rfl|rfl)|hb)|hb
  · exact stack_apart _ off 28 member (by simp)
  · exact stack_apart _ off 32 member (by simp)
  · exact stack_apart _ off 36 member (by simp)
  · exact stack_apart _ off 40 member (by simp)
  · exact stack_apart _ off 44 member (by simp)
  · exact safe off member _ (List.mem_append_left _ hb)
  · exact safe off member _ (by simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false]; exact Or.inr hb)

/-- Values written by the actual six-push callback prologue. -/
theorem saved_values (s : X86Memory.State) :
    load32 (OriginalAimGuard.saved s).memory (s.regs 4-(24#32))=s.regs 5 ∧
    load32 (OriginalAimGuard.saved s).memory (s.regs 4-(20#32))=s.regs 7 ∧
    load32 (OriginalAimGuard.saved s).memory (s.regs 4-(16#32))=s.regs 6 ∧
    load32 (OriginalAimGuard.saved s).memory (s.regs 4-(12#32))=s.regs 2 ∧
    load32 (OriginalAimGuard.saved s).memory (s.regs 4-(8#32))=s.regs 1 ∧
    load32 (OriginalAimGuard.saved s).memory (s.regs 4-(4#32))=s.regs 3 := by
  rw [E1M1AimWall.saved_memory]
  have separate (a b : Word) (small : Apart (-a) (-b)) : Apart (s.regs 4-a) (s.regs 4-b) := by
    simpa only [BitVec.sub_eq_add_neg] using OriginalPathXStep.apart_translate (s.regs 4) (-a) (-b) small
  simp only [show (4 : Word)=(4#32) from rfl, show (8 : Word)=(8#32) from rfl, show (12 : Word)=(12#32) from rfl, show (16 : Word)=(16#32) from rfl, show (20 : Word)=(20#32) from rfl, show (24 : Word)=(24#32) from rfl]
  rw [load_store]
  repeat first
    | rw [load_store]
    | rw [load_store_apart _ _ _ _ (separate _ _ (by unfold Apart; decide))]
  simp
end Doom.Proofs.E1M1AimReturnFrame
