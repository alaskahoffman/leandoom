import Doom.Proofs.OriginalLineCache
import Doom.Proofs.E1M1GroupOutput
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1400000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1LineCache
open Verification X86 X86Memory X86Control BlockSummary OriginalLineCache

/-- A side-table lookup, before the line's cached pointer exists. -/
def target (m : Memory) (base : Word) (i : BitVec 16) : Word :=
  if i=65535 then 0 else load32 m (E1M1NoiseGraph.sideAddress base i)

/-- Inputs originate in copied side indices and the side table. No cached line
pointer is required by this contract. Separation covers the subsequent back read. -/
structure Source (e : OriginalGroupOutput.Line) (s : X86Memory.State) where
  frontIndex : BitVec 16
  backIndex : BitVec 16
  sides : Word
  line : s.regs 3=e.address
  base : load32 s.memory 0x2c118=sides
  frontIndexRead : load16 s.memory (e.address+22)=frontIndex
  backIndexRead : load16 s.memory (e.address+24)=backIndex
  frontSide : target s.memory sides frontIndex=e.front
  backSide : target s.memory sides backIndex=e.back
  keepBase : Apart 0x2c118 (e.address+46)
  keepBack : backIndex≠65535 → Apart (E1M1NoiseGraph.sideAddress sides backIndex) (e.address+46)

private theorem half_frame (m : Memory) (a b v : Word) (h : Apart b a) :
    load16 (store32 m a v) b=load16 m b := by
  have eq := congrArg (fun w : Word => w.extractLsb' 0 16) (load_store_apart m a b v h)
  simpa only [load32,BitVec.extractLsb'_append_eq_right,load16] using eq

private theorem index_apart (p : Word) : Apart (p+24) (p+46) := by
  have h : Apart (24#32) (46#32) := by unfold Apart; decide +kernel
  intro i j eq
  rw [BitVec.add_assoc,BitVec.add_assoc] at eq
  exact h i j ((BitVec.add_right_inj p).mp eq)

theorem source_values (e : OriginalGroupOutput.Line) (s : X86Memory.State) (h : Source e s) :
    value s 22=e.front ∧ value (front s).core 24=e.back := by
  have vf : value s 22=e.front := by
    rw [lookup s 22 h.frontIndex h.sides (by simpa [h.line] using h.frontIndexRead) h.base]
    exact h.frontSide
  have base : load32 (front s).core.memory 0x2c118=h.sides := by
    change load32 (store32 s.memory (s.regs 3+46) (value s 22)) 0x2c118=_
    rw [h.line,load_store_apart _ _ _ _ h.keepBase,h.base]
  have idx : load16 (front s).core.memory ((front s).core.regs 3+24)=h.backIndex := by
    simp only [front,cached_memory,cached_reg s 22 46 0x2e38a 3 (by decide) (by decide),h.line]
    rw [half_frame _ _ _ _ (index_apart _),h.backIndexRead]
  refine ⟨vf,?_⟩
  rw [lookup (front s).core 24 h.backIndex h.sides idx base]
  split
  · rename_i absent
    simpa only [target,if_pos absent] using h.backSide
  · rename_i absent
    change load32 (store32 s.memory (s.regs 3+46) (value s 22)) _=_
    rw [h.line,load_store_apart _ _ _ _ (h.keepBack absent)]
    simpa only [target,if_neg absent] using h.backSide

/-- The original instructions establish exactly the input relation consumed by
P_GroupLines, at this one line. -/
theorem establishes (e : OriginalGroupOutput.Line) (s : X86Memory.State) (f : Option Flags)
    (h : Source e s) :
    ∃ out, X86Routine.run program [0x2e3ac] 16 ⟨s,f,0x2e368⟩=some out ∧
      OriginalGroupOutput.Inputs [e] out.core.memory := by
  refine ⟨result s,joined_execution s f,?_⟩
  intro l hl
  have eq : l=e := by simpa using hl
  subst l
  have rb := readback s
  obtain ⟨vf,vb⟩ := source_values e s h
  rw [vf,vb,h.line] at rb
  exact rb

/-- Loading a new line extends the established set. Earlier pointers cannot be
silently overwritten: byte-level separation is required and used. This lemma
can be iterated when the remaining loader loop and allocation are connected. -/
theorem extend_inputs (e : OriginalGroupOutput.Line) (old : List OriginalGroupOutput.Line)
    (s : X86Memory.State) (f : Option Flags) (h : Source e s)
    (before : OriginalGroupOutput.Inputs old s.memory)
    (safe : ∀ l∈old, ∀ off∈[(46#32),50],
      Apart (l.address+off) (e.address+46) ∧ Apart (l.address+off) (e.address+50)) :
    ∃ out, X86Routine.run program [0x2e3ac] 16 ⟨s,f,0x2e368⟩=some out ∧
      OriginalGroupOutput.Inputs (e::old) out.core.memory := by
  refine ⟨result s,joined_execution s f,?_⟩
  intro l hl
  rcases List.mem_cons.mp hl with eq|member
  · subst l
    obtain ⟨vf,vb⟩ := source_values e s h
    have rb := readback s
    rw [vf,vb,h.line] at rb
    exact rb
  · have a := safe l member 46 (by simp)
    have b := safe l member 50 (by simp)
    have fa := frame s (l.address+46) (by simpa [h.line] using a.1) (by simpa [h.line] using a.2)
    have fb := frame s (l.address+50) (by simpa [h.line] using b.1) (by simpa [h.line] using b.2)
    exact ⟨fa.trans (before l member).1,fb.trans (before l member).2⟩

/-- Specialize the same contract to a relocated line of the pinned E1M1 topology.
Side-table establishment and copied index values remain explicit premises. -/
theorem physical_line (a : E1M1NoiseTopology.Addresses) (e : E1M1NoiseTopology.Line)
    (s : X86Memory.State) (f : Option Flags) (base : Word)
    (line : s.regs 3=a.line e.index)
    (sides : load32 s.memory 0x2c118=base)
    (fi : load16 s.memory (a.line e.index+22)=e.frontIndex)
    (bi : load16 s.memory (a.line e.index+24)=e.backIndex)
    (front : target s.memory base e.frontIndex=a.sector e.front)
    (back : target s.memory base e.backIndex=OriginalGroupLines.backAddress e a)
    (globalSafe : Apart 0x2c118 (a.line e.index+46))
    (sideSafe : e.backIndex≠65535 → Apart (E1M1NoiseGraph.sideAddress base e.backIndex) (a.line e.index+46)) :
    ∃ out, X86Routine.run program [0x2e3ac] 16 ⟨s,f,0x2e368⟩=some out ∧
      OriginalGroupOutput.Inputs [E1M1GroupOutput.physical a e] out.core.memory := by
  exact establishes _ s f ⟨e.frontIndex,e.backIndex,base,line,sides,fi,bi,front,back,globalSafe,sideSafe⟩

end Doom.Proofs.E1M1LineCache
