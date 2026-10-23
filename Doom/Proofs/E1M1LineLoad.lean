import Doom.Proofs.OriginalLineLoad
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1LineLoad
open Verification X86 X86Memory X86Control BlockSummary OriginalLineLoad HalfMemory

def CopySafe (a line : Word) : Prop :=
  Separate 4 2 a (line+22) ∧ Separate 4 2 a (line+24)

/-- Raw WAD-record inputs, before either copied side index or cached pointer
exists in the runtime line. Physical separation is explicit. -/
structure Source (e : OriginalGroupOutput.Line) (s : X86Memory.State) where
  frontIndex : BitVec 16
  backIndex : BitVec 16
  sides : Word
  line : s.regs 3=e.address
  base : load32 s.memory 0x2c118=sides
  frontRead : load16 s.memory (s.regs 1+10)=frontIndex
  backRead : load16 s.memory (s.regs 1+12)=backIndex
  nextRead : Separate 2 2 (s.regs 1+12) (e.address+22)
  frontSide : E1M1LineCache.target s.memory sides frontIndex=e.front
  backSide : E1M1LineCache.target s.memory sides backIndex=e.back
  copyBase : CopySafe 0x2c118 e.address
  copyFront : frontIndex≠65535 → CopySafe (E1M1NoiseGraph.sideAddress sides frontIndex) e.address
  copyBack : backIndex≠65535 → CopySafe (E1M1NoiseGraph.sideAddress sides backIndex) e.address
  cacheBase : Apart 0x2c118 (e.address+46)
  cacheBack : backIndex≠65535 → Apart (E1M1NoiseGraph.sideAddress sides backIndex) (e.address+46)

theorem target_preserved (s : X86Memory.State) (base : Word) (i : BitVec 16)
    (safe : i≠65535 → CopySafe (E1M1NoiseGraph.sideAddress base i) (s.regs 3)) :
    E1M1LineCache.target (copied s).memory base i=E1M1LineCache.target s.memory base i := by
  simp only [E1M1LineCache.target]
  split
  · rfl
  · rename_i present
    exact copied_frame s _ (safe present).1 (safe present).2

/-- The four original MOVs discharge the preceding proof's copied-index premise. -/
def cache_source (e : OriginalGroupOutput.Line) (s : X86Memory.State) (h : Source e s) :
    E1M1LineCache.Source e (copied s) := by
  have fi : first s=h.frontIndex := h.frontRead
  have bi : second s=h.backIndex := by
    unfold second firstMemory
    rw [HalfMemory.half_frame _ _ _ _ (by simpa only [h.line] using h.nextRead)]
    exact h.backRead
  obtain ⟨front,back⟩ := copied_indices s
  rw [fi,h.line] at front
  rw [bi,h.line] at back
  refine ⟨h.frontIndex,h.backIndex,h.sides,?_,?_,front,back,?_,?_,h.cacheBase,h.cacheBack⟩
  · exact (copied_reg s 3 (by decide)).trans h.line
  · exact (copied_frame s _ (by simpa only [h.line] using h.copyBase.1)
      (by simpa only [h.line] using h.copyBase.2)).trans h.base
  · rw [target_preserved s h.sides h.frontIndex (by simpa only [h.line] using h.copyFront)]
    exact h.frontSide
  · rw [target_preserved s h.sides h.backIndex (by simpa only [h.line] using h.copyBack)]
    exact h.backSide

/-- A single uninterrupted original suffix establishes both cached sector
pointers from raw WAD indices, and advances to the next record or cleanup. -/
theorem establishes (e : OriginalGroupOutput.Line) (s : X86Memory.State) (f : Option Flags)
    (h : Source e s) :
    ∃ out, X86Routine.run program [0x2e29a,0x2e3c1] 26 ⟨s,f,0x2e358⟩=some out ∧
      OriginalGroupOutput.Inputs [e] out.core.memory ∧
      out.core.regs 1=s.regs 1+14 ∧ out.core.regs 3=e.address+62 ∧ out.core.regs 5=s.regs 5+1 := by
  refine ⟨result s,joined_execution s f,?_,(progress s).2.1,?_,(progress s).2.2.2⟩
  · intro l hl
    have eq : l=e := by simpa using hl
    subst l
    rw [(progress s).1]
    have rb := OriginalLineCache.readback (copied s)
    obtain ⟨vf,vb⟩ := E1M1LineCache.source_values e (copied s) (cache_source e s h)
    rw [vf,vb,copied_reg s 3 (by decide),h.line] at rb
    exact rb
  · simpa only [h.line] using (progress s).2.2.1

/-- All earlier initialized line pointers survive the copy, cache and advance. -/
theorem frame (s : X86Memory.State) (a : Word)
    (copy : CopySafe a (s.regs 3))
    (front : Apart a (s.regs 3+46)) (back : Apart a (s.regs 3+50)) :
    load32 (result s).core.memory a=load32 s.memory a := by
  rw [(progress s).1]
  rw [OriginalLineCache.frame (copied s) a
    (by simpa only [copied_reg s 3 (by decide)] using front)
    (by simpa only [copied_reg s 3 (by decide)] using back)]
  exact copied_frame s a copy.1 copy.2

end Doom.Proofs.E1M1LineLoad
