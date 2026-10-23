import Doom.Proofs.E1M1LineIteration
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1LineFrame
open Verification X86 X86Memory X86Control BlockSummary E1M1LineIteration

/-- Exact possible write destinations, including the diagonal CALL and saves.
Separation is byte-wise and permits unaligned and wrapping addresses. -/
structure Protected (a line sp : Word) : Prop where
  words : ∀ off∈[(0#32),4,8,12,26,30,34,38,42,46,50], Apart a (line+off)
  halves : ∀ off∈[(16#32),18,20,22,24], HalfMemory.Separate 4 2 a (line+off)
  stack : ∀ off∈[(4#32),8,12,16], Apart a (sp-off)

def beforeBounds (s : X86Memory.State) : X86Memory.State :=
  if Axis s then (E1M1LineSetup.selected s).core
  else (OriginalLineSetup.classified
    (OriginalDivMemory.result (E1M1LineSetup.selected s).core).core).core

theorem result_eq (s : X86Memory.State) :
    result s=E1M1LineGeometry.result (beforeBounds s) := by
  unfold result beforeBounds; split <;> rfl

@[simp] theorem prepared_reg (s : X86Memory.State) (r : Reg) (h : r∈[1,3,4,5]) :
    (E1M1LineSetup.prepared s).core.regs r=s.regs r := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl
  all_goals simp [E1M1LineSetup.prepared,OriginalLineGeometry.prepared,
    OriginalLineGeometry.delta,OriginalLineGeometry.vertices,put,write]

@[simp] theorem selected_reg (s : X86Memory.State) (r : Reg) (h : r∈[1,3,5]) :
    (E1M1LineSetup.selected s).core.regs r=s.regs r := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl
  all_goals unfold E1M1LineSetup.selected OriginalLineSetup.selected
  all_goals split <;> try split
  all_goals simp [X86Routine.pushWord,put,write,prepared_reg]

@[simp] theorem division_bp (s : X86Memory.State) :
    (OriginalDivMemory.result s).core.regs 5=s.regs 5 := by
  unfold OriginalDivMemory.result OriginalDivMemory.body
  split <;> simp [OriginalDivMemory.restored,OriginalDivMemory.divided,
    OriginalDivMemory.saturated,OriginalDivMemory.guarded,put,write,OriginalDivMemory.saved_reg]

@[simp] theorem before_reg (s : X86Memory.State) (r : Reg) (h : r∈[1,3,5]) :
    (beforeBounds s).regs r=s.regs r := by
  unfold beforeBounds
  split
  · exact selected_reg s r h
  · have regs := OriginalDivMemory.restored_registers (E1M1LineSetup.selected s).core
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl
    · exact regs.2.1.trans (selected_reg s 1 (by simp))
    · exact regs.2.2.1.trans (selected_reg s 3 (by simp))
    · exact (division_bp _).trans (selected_reg s 5 (by simp))

@[simp] theorem before_stack (s : X86Memory.State) : (beforeBounds s).regs 4=s.regs 4 := by
  unfold beforeBounds
  split
  · rename_i axis
    rcases axis with x|y
    · simp [E1M1LineSetup.selected,OriginalLineSetup.selected,x,put,write,prepared_reg]
    · by_cases x : OriginalLineSetup.dx (E1M1LineSetup.prepared s).core=(0#32)
      all_goals simp [E1M1LineSetup.selected,OriginalLineSetup.selected,x,y,put,write,prepared_reg]
  · rename_i axis
    have x : OriginalLineSetup.dx (E1M1LineSetup.prepared s).core≠0 := fun h => axis (Or.inl h)
    have y : OriginalLineSetup.dy (E1M1LineSetup.prepared s).core≠0 := fun h => axis (Or.inr h)
    have call := OriginalLineSetup.diagonal_call (E1M1LineSetup.prepared s).core x y
    change (OriginalDivMemory.result (E1M1LineSetup.selected s).core).core.regs 4=_
    rw [(OriginalDivMemory.restored_registers _).2.2.2.1]
    change (OriginalLineSetup.selected (E1M1LineSetup.prepared s).core).core.regs 4+4=_
    rw [call.2.2.2.1,BitVec.sub_add_cancel,prepared_reg s 4 (by simp)]

/-- Both raw and runtime cursors advance by their real record strides; FixedDiv
restores the loop counter and stack even when its arguments take saturation. -/
theorem progress (s : X86Memory.State) :
    (result s).core.regs 1=s.regs 1+14 ∧
    (result s).core.regs 3=s.regs 3+62 ∧
    (result s).core.regs 5=s.regs 5+1 ∧
    (result s).core.regs 4=s.regs 4 := by
  rw [result_eq]
  have h := OriginalLineLoad.progress (OriginalLineGeometry.bounds (beforeBounds s)).core
  refine ⟨by simpa [E1M1LineGeometry.result] using h.2.1,by simpa [E1M1LineGeometry.result] using h.2.2.1,by simpa [E1M1LineGeometry.result] using h.2.2.2,?_⟩
  simp [E1M1LineGeometry.result,OriginalLineLoad.result,OriginalLineLoad.advanced,
    OriginalLineCache.result,OriginalLineCache.front,put,write]

theorem prepared_frame (s : X86Memory.State) (a : Word) (h : Protected a (s.regs 3) (s.regs 4)) :
    load32 (E1M1LineSetup.prepared s).core.memory a=load32 s.memory a := by
  have reg : (OriginalLineGeometry.vertices (OriginalLineSetup.metadata s)).core.regs 3=s.regs 3 := by
    simp [OriginalLineGeometry.vertices,put,write]
  unfold E1M1LineSetup.prepared OriginalLineGeometry.prepared
  rw [OriginalLineGeometry.delta_frame _ a
    (by rw [reg]; exact h.words 8 (by simp)) (by rw [reg]; exact h.words 12 (by simp))]
  change load32 (store32 (OriginalLineGeometry.firstMemory (OriginalLineSetup.metadata s))
    ((OriginalLineSetup.metadata s).regs 3+4) _) a=_
  rw [load_store_apart _ _ _ _ (by simpa using h.words 4 (by simp))]
  rw [show OriginalLineGeometry.firstMemory (OriginalLineSetup.metadata s)=
    store32 (OriginalLineSetup.metadata s).memory (s.regs 3) (OriginalLineGeometry.v1 (OriginalLineSetup.metadata s)) from by
      simp [OriginalLineGeometry.firstMemory]]
  rw [load_store_apart _ _ _ _ (by simpa using h.words 0 (by simp))]
  exact OriginalLineSetup.metadata_frame s a (fun off mem => h.halves off (by simp only [List.mem_cons,List.not_mem_nil,or_false] at mem ⊢; rcases mem with rfl|rfl|rfl <;> simp) )

theorem before_frame (s : X86Memory.State) (a : Word) (h : Protected a (s.regs 3) (s.regs 4)) :
    load32 (beforeBounds s).memory a=load32 s.memory a := by
  have slope : Apart a ((E1M1LineSetup.prepared s).core.regs 3+42) := by
    simpa using h.words 42 (by simp)
  unfold beforeBounds
  split
  · rename_i axis
    have sel : load32 (E1M1LineSetup.selected s).core.memory a=
        load32 (E1M1LineSetup.prepared s).core.memory a := by
      unfold E1M1LineSetup.selected OriginalLineSetup.selected
      split
      · exact load_store_apart _ _ _ _ slope
      · split
        · exact load_store_apart _ _ _ _ slope
        · rename_i x y
          exact False.elim (axis.elim x y)
    exact sel.trans (prepared_frame s a h)
  · rename_i axis
    have x : OriginalLineSetup.dx (E1M1LineSetup.prepared s).core≠0 := fun h => axis (Or.inl h)
    have y : OriginalLineSetup.dy (E1M1LineSetup.prepared s).core≠0 := fun h => axis (Or.inr h)
    have call := OriginalLineSetup.diagonal_call (E1M1LineSetup.prepared s).core x y
    have sp : (E1M1LineSetup.selected s).core.regs 4=s.regs 4-4 := by
      simpa [E1M1LineSetup.selected] using call.2.2.2.1
    have divframe := OriginalDivMemory.result_frame (E1M1LineSetup.selected s).core a (by
      intro off mem
      simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
      rcases mem with rfl|rfl|rfl
      all_goals rw [sp]
      all_goals simpa [BitVec.sub_sub] using h.stack _ (by simp))
    have line : (OriginalDivMemory.result (E1M1LineSetup.selected s).core).core.regs 3=s.regs 3 :=
      (OriginalDivMemory.restored_registers _).2.2.1.trans (selected_reg s 3 (by simp))
    change load32 (store32 _ (_+42) _) a=_
    rw [load_store_apart _ _ _ _ (by rw [line]; exact h.words 42 (by simp)),divframe]
    have selected : load32 (E1M1LineSetup.selected s).core.memory a=
        load32 (E1M1LineSetup.prepared s).core.memory a := by
      simp only [E1M1LineSetup.selected,OriginalLineSetup.selected,if_neg x,if_neg y,
        X86Routine.pushWord,put,write]
      exact load_store_apart _ _ _ _ (by simpa using h.stack 4 (by simp))
    exact selected.trans (prepared_frame s a h)

/-- Every word outside the iteration's exact write footprint is unchanged. -/
theorem frame (s : X86Memory.State) (a : Word) (h : Protected a (s.regs 3) (s.regs 4)) :
    load32 (result s).core.memory a=load32 s.memory a := by
  rw [result_eq]
  have line : (OriginalLineGeometry.bounds (beforeBounds s)).core.regs 3=s.regs 3 := by simp
  have tail := E1M1LineLoad.frame (OriginalLineGeometry.bounds (beforeBounds s)).core a
    ⟨by rw [line]; exact h.halves 22 (by simp),by rw [line]; exact h.halves 24 (by simp)⟩
    (by rw [line]; exact h.words 46 (by simp)) (by rw [line]; exact h.words 50 (by simp))
  have box := OriginalLineGeometry.bounds_frame (beforeBounds s) a (by
    intro off mem
    rw [before_reg s 3 (by simp)]
    exact h.words off (by simp only [List.mem_cons,List.not_mem_nil,or_false] at mem ⊢; rcases mem with rfl|rfl|rfl|rfl <;> simp))
  exact tail.trans (box.trans (before_frame s a h))
/-- The signed loop branch observes the count after every write, not a cached
pre-state value. The frame theorem supplies stability when storage is separate. -/
theorem exit_pc (s : X86Memory.State) :
    (result s).pc=(if (s.regs 5+1).toInt < (load32 (result s).core.memory 0x2c134).toInt
      then 0x2e29a else 0x2e3c1) := by
  rw [result_eq]
  simp [E1M1LineGeometry.result,OriginalLineLoad.result,OriginalLineLoad.advanced,
    OriginalLineCache.result,OriginalLineCache.front,put,write]

/-- Word preservation also preserves the source halfword at the same address. -/
theorem half_frame (s : X86Memory.State) (a : Word) (h : Protected a (s.regs 3) (s.regs 4)) :
    load16 (result s).core.memory a=load16 s.memory a := by
  have eq := congrArg (fun w : Word => w.extractLsb' 0 16) (frame s a h)
  simpa only [load32,BitVec.extractLsb'_append_eq_right,load16] using eq

end Doom.Proofs.E1M1LineFrame
