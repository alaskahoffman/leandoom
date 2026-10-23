import Doom.Proofs.OriginalThingFraction
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.OriginalThingFractionInputs
open Verification X86 X86Memory X86Control BlockSummary
open OriginalThingDiagonal (points)

theorem second_regs (s : X86Memory.State) :
    (OriginalThingSecondSide.result s).core.regs 4=s.regs 4 ∧
    (OriginalThingSecondSide.result s).core.regs 1=s.regs 1 ∧
    (OriginalThingSecondSide.result s).core.regs 5=s.regs 5 ∧
    (OriginalThingSecondSide.result s).core.regs 6=s.regs 6 ∧
    (OriginalThingSecondSide.result s).core.regs 7=s.regs 7 := by
  have r := OriginalDivlineSide.returned (OriginalThingSecondSide.called s none).core
  have e := OriginalThingSecondSide.second_returned s
  have t := OriginalThingSecondSide.tested_observe (OriginalThingSecondSide.second s).core
  refine ⟨t.2.1.trans e.2.1,t.2.2.1.trans e.2.2.1,?_,?_,?_⟩
  all_goals
    unfold OriginalThingSecondSide.result OriginalThingSecondSide.tested
    split <;> simp only [put,write,↓reduceIte]
  all_goals
    first
    | exact r.2.2.2.2.1
    | exact r.2.2.1
    | exact r.2.2.2.1

theorem crossing_regs (s : X86Memory.State) :
    (OriginalThingSecondSide.crossing s).core.regs 4=s.regs 4 ∧
    (OriginalThingSecondSide.crossing s).core.regs 1=s.regs 1 := by
  have a := OriginalThingFirstSide.returned s
  have b := second_regs (OriginalThingFirstSide.result s).core
  exact ⟨b.1.trans a.2.1,b.2.1.trans a.2.2⟩

theorem endpoints (s : X86Memory.State) (trace : Collision.Divline) (thing : Collision.SolidThing)
    (object : Word) (h : OriginalThingFirstSide.Inputs s trace thing object) :
    (OriginalThingSecondSide.crossing s).core.regs 7=(points trace thing).1.raw.toBitVec ∧
    (OriginalThingSecondSide.crossing s).core.regs 6=(points trace thing).2.1.raw.toBitVec ∧
    load32 (OriginalThingSecondSide.crossing s).core.memory (s.regs 4+(20#32))=(points trace thing).2.2.1.raw.toBitVec ∧
    (OriginalThingSecondSide.crossing s).core.regs 5=(points trace thing).2.2.2.raw.toBitVec := by
  have diag := OriginalThingDiagonal.live_diagonal s trace thing object h.diagonal
  have a := OriginalDivlineSide.returned (OriginalThingDiagonal.first s).core
  have b := second_regs (OriginalThingFirstSide.result s).core
  have first := OriginalThingFirstSide.live s trace thing object h
  refine ⟨b.2.2.2.2.trans (a.2.2.2.1.trans diag.1),
    b.2.2.2.1.trans (a.2.2.1.trans diag.2.1),?_,b.2.2.1.trans first.2.2.2.2⟩
  have keep := OriginalThingSecondSide.frame (OriginalThingFirstSide.result s).core (s.regs 4+(20#32)) (by
    rw [(OriginalThingFirstSide.returned s).2.1]
    constructor
    · exact OriginalThingSecondSide.apart _ _ _ (by unfold Apart; decide)
    · intro off ho
      have sep : Apart (20#32) (-off) := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
        rcases ho with rfl|rfl|rfl|rfl|rfl <;> unfold Apart <;> decide
      simpa only [BitVec.sub_eq_add_neg] using OriginalThingSecondSide.apart (s.regs 4) (20#32) (-off) sep)
  apply keep.trans
  have saved := OriginalThingFirstSide.second_endpoint s
  apply saved.1.trans
  have eq := diag.2.2.2
  rw [(OriginalThingDiagonal.diagonal_observe s).2.2.2.2.2,load_store] at eq
  exact eq

theorem inputs (s : X86Memory.State) (trace : Collision.Divline) (thing : Collision.SolidThing)
    (object : Word) (h : OriginalThingFirstSide.Inputs s trace thing object)
    (scratch : ∀ a∈OriginalThingFraction.traceReads, Apart a (s.regs 4+(16#32)))
    (safe : ∀ a∈OriginalThingFraction.traceReads, OriginalThingFraction.Safe (s.regs 4) a) :
    OriginalThingFraction.Inputs (OriginalThingSecondSide.crossing s).core trace thing := by
  have sp := (crossing_regs s).1
  have e := endpoints s trace thing object h
  have keep (a : Word) (ha : a∈OriginalThingFraction.traceReads) :
      load32 (OriginalThingSecondSide.crossing s).core.memory a=load32 s.memory a := by
    have ha' : a∈[(0x2ba10#32),0x2ba14,0x2ba18,0x2ba1c] := ha
    exact (OriginalThingSecondSide.frame _ a (OriginalThingSecondSide.side_safe s a (h.safe a ha') (scratch a ha))).trans
      (OriginalThingFirstSide.frame s a (h.safe a ha'))
  refine ⟨e.1,e.2.1,?_,e.2.2.2,?_,?_,?_,?_,?_⟩
  · rw [sp]; exact e.2.2.1
  · exact (keep _ (by simp [OriginalThingFraction.traceReads])).trans h.traceX
  · exact (keep _ (by simp [OriginalThingFraction.traceReads])).trans h.traceY
  · exact (keep _ (by simp [OriginalThingFraction.traceReads])).trans h.diagonal.traceDX
  · exact (keep _ (by simp [OriginalThingFraction.traceReads])).trans h.diagonal.traceDY
  · rw [sp]; exact safe
end Doom.Proofs.OriginalThingFractionInputs
