import Doom.Proofs.OriginalPathXStep
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.PathXStepFrame
open Verification X86 X86Memory X86Control BlockSummary OriginalPathXStep

/-- Coordinates needed by the next axis survive both real helper calls. -/
theorem div_preserves (s : X86Memory.State) (r : Reg) (h : r∈[1,5,6,7]) :
    (OriginalDivMemory.result s).core.regs r=s.regs r := by
  simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h
  · subst r; exact (OriginalDivMemory.restored_registers s).2.1
  · subst r
    unfold OriginalDivMemory.result OriginalDivMemory.body
    split <;> simp [OriginalDivMemory.restored,OriginalDivMemory.divided,OriginalDivMemory.saturated,
      OriginalDivMemory.guarded,put,write,OriginalDivMemory.saved_reg]
  · subst r; exact (OriginalDivMemory.restored_registers s).1
  · subst r
    unfold OriginalDivMemory.result OriginalDivMemory.body
    split <;> simp [OriginalDivMemory.restored,OriginalDivMemory.divided,OriginalDivMemory.saturated,
      OriginalDivMemory.guarded,put,write,OriginalDivMemory.saved_reg]

theorem input_preserves (right : Bool) (s : X86Memory.State) (f : Option Flags)
    (r : Reg) (h : r∈[1,5,6,7]) : (divisionInput right s f).core.regs r=s.regs r := by
  have h0 : r≠0 := by simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at h; rcases h with rfl|rfl|rfl|rfl <;> decide
  have h2 : r≠2 := by simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at h; rcases h with rfl|rfl|rfl|rfl <;> decide
  have h3 : r≠3 := by simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at h; rcases h with rfl|rfl|rfl|rfl <;> decide
  have h4 : r≠4 := by simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at h; rcases h with rfl|rfl|rfl|rfl <;> decide
  have abs := (OriginalAbs.registers (absCall right s f).core).2.1 r h0 h4
  unfold divisionInput
  have divide : ∀ (s : X86Memory.State) (f : Option Flags), (divideCall right s f).core.regs r=s.regs r := by
    intro s f
    cases right <;> simp [divideCall,rightDivide,rightDivide_7,rightDivide_m6,rightDivide_6,rightDivide_5,rightDivide_v4,rightDivide_4,rightDivide_3,rightDivide_m2,rightDivide_2,rightDivide_m1,rightDivide_1,leftDivide,leftDivide_7,leftDivide_m6,leftDivide_6,leftDivide_v5,leftDivide_5,leftDivide_v4,leftDivide_4,leftDivide_3,leftDivide_m2,leftDivide_2,leftDivide_m1,leftDivide_1,put,write,h0,h2,h3,h4]
  rw [divide,abs]
  cases right <;> simp [absCall,rightCall,rightCall_1,rightCall_m0,leftCall,leftCall_1,leftCall_m0,put,write,h4]

theorem moving_preserves (right : Bool) (s : X86Memory.State) (f : Option Flags)
    (r : Reg) (h : r∈[1,5,6,7]) : (movingResult right s f).core.regs r=s.regs r := by
  have h3 : r≠3 := by simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at h; rcases h with rfl|rfl|rfl|rfl <;> decide
  have tailReg : ∀ (s : X86Memory.State) (f : Option Flags), (tail right s f).core.regs r=s.regs r := by
    intro s f
    cases right <;> simp [tail,rightTail,rightTail_2,rightTail_1,rightTail_v0,leftTail,leftTail_1,put,write,h3]
  unfold movingResult
  rw [tailReg,div_preserves _ r h,input_preserves right s f r h]

theorem registers (s : X86Memory.State) (r : Reg) (h : r∈[1,5,6,7]) :
    (result s).core.regs r=s.regs r := by
  have h0 : r≠0 := by simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at h; rcases h with rfl|rfl|rfl|rfl <;> decide
  have h2 : r≠2 := by simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at h; rcases h with rfl|rfl|rfl|rfl <;> decide
  have h3 : r≠3 := by simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at h; rcases h with rfl|rfl|rfl|rfl <;> decide
  unfold result
  split
  · simp [same,same_4,same_m3,same_3,same_2,same_1,selection,prepare,prepare_4,prepare_v3,prepare_3,prepare_2,prepare_v1,prepare_1,put,write,h0,h2,h3]
  · rw [moving_preserves _ _ _ r h]
    simp [selection,prepare,prepare_4,prepare_v3,prepare_3,prepare_2,prepare_v1,prepare_1,put,write,h0,h3]

theorem stack (s : X86Memory.State) : (result s).core.regs 4=s.regs 4 := by
  unfold result
  split
  · simp [same,same_4,same_m3,same_3,same_2,same_1,selection,prepare,prepare_4,prepare_v3,prepare_3,prepare_2,prepare_v1,prepare_1,put,write]
  · rw [(moving_observe _ _ _).2.2.2]
    simp [selection,prepare,prepare_4,prepare_v3,prepare_3,prepare_2,prepare_v1,prepare_1,put,write]

/-- The complete set of potentially overwritten words, including callee saves. -/
def writes (s : X86Memory.State) : List Word :=
  [s.regs 4,s.regs 4+32,s.regs 4-4,s.regs 4-8,s.regs 4-12,s.regs 4-16]

theorem moving_frame (right : Bool) (s : X86Memory.State) (f : Option Flags) (a : Word)
    (safe : ∀ b, b∈writes s → Apart a b) :
    load32 (movingResult right s f).core.memory a=load32 s.memory a := by
  have tailMem : ∀ (s : X86Memory.State) (f : Option Flags), (tail right s f).core.memory=s.memory := by
    intro s f; cases right <;> rfl
  unfold movingResult
  rw [tailMem,OriginalDivMemory.result_frame]
  · rw [(input_observe right s f).2.2.2.2]
    repeat rw [load_store_apart _ _ _ _ (safe _ (by simp [writes]))]
  · intro off h
    rw [(input_observe right s f).2.2.2.1]
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl <;> simp only [BitVec.sub_sub]
    all_goals exact safe _ (by simp [writes])

theorem frame (s : X86Memory.State) (a : Word)
    (safe : ∀ b, b∈writes s → Apart a b) :
    load32 (result s).core.memory a=load32 s.memory a := by
  unfold result
  split
  · simp only [same,same_4,same_m3,same_3,same_2,same_1,selection,prepare,prepare_4,prepare_v3,prepare_3,prepare_2,prepare_v1,prepare_1,put,write,ite_false]
    exact load_store_apart _ _ _ _ (safe _ (by simp [writes]))
  · rw [moving_frame]
    · rfl
    · simpa [writes,selection,prepare,prepare_4,prepare_v3,prepare_3,prepare_2,prepare_v1,prepare_1,put,write,ite_false] using safe

theorem local_preserved (s : X86Memory.State) (off : Word) (h : off∈[12,16,20,24]) :
    load32 (result s).core.memory (s.regs 4+off)=load32 s.memory (s.regs 4+off) := by
  apply frame
  intro b hb
  simp only [writes,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl|rfl
  · have finite : ∀ i : Word, i∈[12,16,20,24] → Apart i (0#32) := by
      intro i hi
      simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl <;> unfold Apart <;> decide
    simpa [BitVec.sub_eq_add_neg,BitVec.add_zero] using
      OriginalPathXStep.apart_translate (s.regs 4) off (0#32) (finite off h)
  · have finite : ∀ i : Word, i∈[12,16,20,24] → Apart i (32#32) := by
      intro i hi
      simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl <;> unfold Apart <;> decide
    simpa [BitVec.sub_eq_add_neg,BitVec.add_zero] using
      OriginalPathXStep.apart_translate (s.regs 4) off (32#32) (finite off h)
  · have finite : ∀ i : Word, i∈[12,16,20,24] → Apart i (4294967292#32) := by
      intro i hi
      simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl <;> unfold Apart <;> decide
    simpa [BitVec.sub_eq_add_neg,BitVec.add_zero] using
      OriginalPathXStep.apart_translate (s.regs 4) off (4294967292#32) (finite off h)
  · have finite : ∀ i : Word, i∈[12,16,20,24] → Apart i (4294967288#32) := by
      intro i hi
      simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl <;> unfold Apart <;> decide
    simpa [BitVec.sub_eq_add_neg,BitVec.add_zero] using
      OriginalPathXStep.apart_translate (s.regs 4) off (4294967288#32) (finite off h)
  · have finite : ∀ i : Word, i∈[12,16,20,24] → Apart i (4294967284#32) := by
      intro i hi
      simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl <;> unfold Apart <;> decide
    simpa [BitVec.sub_eq_add_neg,BitVec.add_zero] using
      OriginalPathXStep.apart_translate (s.regs 4) off (4294967284#32) (finite off h)
  · have finite : ∀ i : Word, i∈[12,16,20,24] → Apart i (4294967280#32) := by
      intro i hi
      simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl <;> unfold Apart <;> decide
    simpa [BitVec.sub_eq_add_neg,BitVec.add_zero] using
      OriginalPathXStep.apart_translate (s.regs 4) off (4294967280#32) (finite off h)
end Doom.Proofs.PathXStepFrame
