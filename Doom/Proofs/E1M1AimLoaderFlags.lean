import Doom.Proofs.E1M1AimInitialPortal
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
namespace Doom.Proofs.E1M1AimLoaderFlags
open Verification X86 X86Memory X86Control BlockSummary

/-- Only writes after metadata are excluded: metadata intentionally writes the
flag itself, so the full-iteration frame cannot be used at this boundary. -/
structure Safe (s : X86Memory.State) (a : Word) : Prop where
  words : ∀ off∈[(0#32),4,8,12,26,30,34,38,42], Apart a (s.regs 3+off)
  stack : ∀ off∈[(4#32),8,12,16], Apart a (s.regs 4-off)

theorem prepared_frame (s : X86Memory.State) (a : Word) (safe : Safe s a) :
    load32 (E1M1LineSetup.prepared s).core.memory a=load32 (OriginalLineSetup.metadata s).memory a := by
  have reg : (OriginalLineGeometry.vertices (OriginalLineSetup.metadata s)).core.regs 3=s.regs 3 := by
    simp [OriginalLineGeometry.vertices,put,write]
  unfold E1M1LineSetup.prepared OriginalLineGeometry.prepared
  rw [OriginalLineGeometry.delta_frame _ a
    (by rw [reg]; exact safe.words 8 (by simp)) (by rw [reg]; exact safe.words 12 (by simp))]
  exact E1M1LineSource.vertices_frame _ a
    (by simpa using safe.words 0 (by simp)) (by simpa using safe.words 4 (by simp))

/-- Includes both axis branches and the real diagonal CALL/FixedDiv/return. -/
theorem before_frame (s : X86Memory.State) (a : Word) (safe : Safe s a) :
    load32 (E1M1LineFrame.beforeBounds s).memory a=load32 (OriginalLineSetup.metadata s).memory a := by
  have slope : Apart a ((E1M1LineSetup.prepared s).core.regs 3+42) := by
    simpa using safe.words 42 (by simp)
  unfold E1M1LineFrame.beforeBounds
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
    exact sel.trans (prepared_frame s a safe)
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
      all_goals simpa [BitVec.sub_sub] using safe.stack _ (by simp))
    have line : (OriginalDivMemory.result (E1M1LineSetup.selected s).core).core.regs 3=s.regs 3 :=
      (OriginalDivMemory.restored_registers _).2.2.1.trans (E1M1LineFrame.selected_reg s 3 (by simp))
    change load32 (store32 _ (_+42) _) a=_
    rw [load_store_apart _ _ _ _ (by rw [line]; exact safe.words 42 (by simp)),divframe]
    have selected : load32 (E1M1LineSetup.selected s).core.memory a=
        load32 (E1M1LineSetup.prepared s).core.memory a := by
      simp only [E1M1LineSetup.selected,OriginalLineSetup.selected,if_neg x,if_neg y,
        X86Routine.pushWord,put,write]
      exact load_store_apart _ _ _ _ (by simpa using safe.stack 4 (by simp))
    exact selected.trans (prepared_frame s a safe)

theorem copy_frame (s : X86Memory.State) (a : Word) (safe : Safe s a) :
    load32 (E1M1LineOutput.copyInput s).memory a=load32 (OriginalLineSetup.metadata s).memory a := by
  have box := OriginalLineGeometry.bounds_frame (E1M1LineFrame.beforeBounds s) a (by
    intro off member
    rw [E1M1LineFrame.before_reg s 3 (by simp)]
    exact safe.words off (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member ⊢
      rcases member with rfl|rfl|rfl|rfl <;> simp))
  exact box.trans (before_frame s a safe)

/-- Exact copied low flag byte, with no assumed two-sided classification.
Line-relative separation is unconditional even for wrapping line addresses. -/
theorem flag_byte (s : X86Memory.State)
    (stack : ∀ off∈[(4#32),8,12,16], Apart (s.regs 3+16) (s.regs 4-off)) :
    (E1M1LineOutput.copyInput s).memory (s.regs 3+16)=s.memory (s.regs 1+4) := by
  have safe : Safe s (s.regs 3+16) := by
    refine ⟨?_,stack⟩
    intro off member
    apply OriginalPathXStep.apart_translate
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> unfold Apart <;> decide
  have kept := E1M1NoiseGraph.byte_of_word (copy_frame s (s.regs 3+16) safe)
  have copied := congrArg (fun w : BitVec 16 => w.extractLsb' 0 8) (OriginalLineSetup.metadata_fields s).1
  simp only [load16,BitVec.extractLsb'_append_eq_right] at copied
  exact kept.trans copied
end Doom.Proofs.E1M1AimLoaderFlags
