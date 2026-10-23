import Doom.Proofs.E1M1AimFloorEntry
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1AimClipFrame
open Verification X86 X86Memory X86Control BlockSummary
attribute [local irreducible] load32 store32

def writes (sp : Word) : List Word := [sp-(4#32),sp-(8#32),sp-(12#32),sp-(16#32),(0x2c1e4#32)]

/-- Floor clipping preserves the line pointer, stack and saved hit distance,
including across the actual division helper. -/
theorem floor_regs (s : X86Memory.State) :
    (E1M1AimFloor.result s).core.regs 1=s.regs 1 ∧
    (E1M1AimFloor.result s).core.regs 4=s.regs 4 ∧
    (E1M1AimFloor.result s).core.regs 3=s.regs 0 := by
  have regs := OriginalDivMemory.restored_registers (E1M1AimFloor.call s)
  unfold E1M1AimFloor.result
  split
  · simp [OriginalAimFloor.gate,OriginalAimFloor.c4,OriginalAimFloor.c3,OriginalAimFloor.c2,OriginalAimFloor.c1,put,write]
  · simp only [OriginalAimFloor.clipped]
    split <;> simp only [OriginalAimFloor.raised,E1M1AimFloor.divided]
    all_goals
      rw [regs.2.1,regs.2.2.2.1,regs.2.2.1]
      simp [E1M1AimFloor.call,E1M1AimFloor.input,OriginalAimFloor.called,OriginalAimFloor.argument,OriginalAimFloor.c4,OriginalAimFloor.c3,OriginalAimFloor.c2,OriginalAimFloor.c1,X86Routine.pushWord,put,write,BitVec.sub_add_cancel]

/-- A reusable frame for all floor-branch stores, with wrapping addresses. -/
theorem floor_frame (s : X86Memory.State) (a : Word)
    (safe : ∀ b∈writes (s.regs 4), Apart a b) :
    load32 (E1M1AimFloor.result s).core.memory a=load32 s.memory a := by
  have sp : (E1M1AimFloor.call s).regs 4=s.regs 4-(4#32) := by
    simp [E1M1AimFloor.call,E1M1AimFloor.input,OriginalAimFloor.called,OriginalAimFloor.argument,OriginalAimFloor.c4,OriginalAimFloor.c3,OriginalAimFloor.c2,OriginalAimFloor.c1,X86Routine.pushWord,put,write,BitVec.sub_add_cancel]
  have saves : ∀ off∈[(4#32),8,12], Apart a ((E1M1AimFloor.call s).regs 4-off) := by
    intro off member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl <;> rw [sp] <;> apply safe <;> simp [writes,BitVec.sub_sub]
  have division : load32 (E1M1AimFloor.divided s).core.memory a=load32 s.memory a := by
    rw [E1M1AimFloor.divided,OriginalDivMemory.result_frame _ _ saves]
    simp only [E1M1AimFloor.call,OriginalAimFloor.called,X86Routine.pushWord,put]
    rw [load_store_apart]
    · rfl
    · simpa [E1M1AimFloor.input,OriginalAimFloor.argument,OriginalAimFloor.c4,OriginalAimFloor.c3,OriginalAimFloor.c2,OriginalAimFloor.c1,put,write] using safe _ (by simp [writes])
  unfold E1M1AimFloor.result
  split
  · rfl
  · simp only [OriginalAimFloor.clipped]
    split
    · exact division
    · simp only [OriginalAimFloor.raised]
      rw [load_store_apart _ _ _ _ (safe _ (by simp [writes]))]
      exact division
end Doom.Proofs.E1M1AimClipFrame
