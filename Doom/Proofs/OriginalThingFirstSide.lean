import Doom.Proofs.OriginalThingDiagonal
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.OriginalThingFirstSide
open Verification X86 X86Memory X86Control BlockSummary
open OriginalThingDiagonal (points)

def program : X86Routine.Program := fun pc =>
  match OriginalThingDiagonal.program pc with
  | some op => some op
  | none => OriginalDivlineSide.program pc

theorem contains_diagonal (pc : Nat) (h : OriginalThingDiagonal.program pc≠none) :
    program pc=OriginalThingDiagonal.program pc := by
  unfold program
  cases eq : OriginalThingDiagonal.program pc <;> simp_all

theorem contains_side (pc : Nat) (h : OriginalDivlineSide.program pc≠none) :
    program pc=OriginalDivlineSide.program pc := by
  have range : 0x2c1e0≤pc ∧ pc<0x2c2a7 := by
    by_cases r : 0x2c1e0≤pc ∧ pc<0x2c2a7
    · exact r
    · simp [OriginalDivlineSide.program,OriginalDivlineSide.bytesProgram,r] at h
  have absent : OriginalThingDiagonal.program pc=none := by
    simp [OriginalThingDiagonal.program,OriginalThingDiagonal.bytesProgram,show ¬(0x2c72b≤pc ∧ pc<0x2c78d) by omega]
  simp [program,absent]

def result (s : X86Memory.State) := OriginalDivlineSide.result (OriginalThingDiagonal.first s).core

theorem execution (s : X86Memory.State) (f : Option Flags) :
    ∃ n≤67, X86Routine.Prefix program [] n ⟨s,f,0x2c72b⟩ (result s) := by
  obtain ⟨n,hn,a⟩ := OriginalThingDiagonal.first_execution s f
  obtain ⟨m,hm,b⟩ := OriginalDivlineSide.execution (OriginalThingDiagonal.first s).core none
  exact ⟨n+m,by omega,OriginalGroupBounds.prefix_join
    (a.transfer program [] contains_diagonal (by simp)) (b.transfer program [] contains_side (by simp))⟩

def Safe (s : X86Memory.State) (a : Word) : Prop :=
  Apart a (s.regs 4+(20#32)) ∧ ∀ off∈[(4#32),8,12,16,20], Apart a (s.regs 4-off)

theorem helper_safe (s : X86Memory.State) (a : Word) (safe : Safe s a) :
    ∀ off∈[(4#32),8,12,16], Apart a ((OriginalThingDiagonal.first s).core.regs 4-off) := by
  rw [(OriginalThingDiagonal.first_observe s).2.2.2.2.1]
  intro off ho
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
  rcases ho with rfl|rfl|rfl|rfl
  · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe.2 (8#32) (by simp)
  · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe.2 (12#32) (by simp)
  · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe.2 (16#32) (by simp)
  · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe.2 (20#32) (by simp)

theorem frame (s : X86Memory.State) (a : Word) (safe : Safe s a) :
    load32 (result s).core.memory a=load32 s.memory a := by
  exact (OriginalDivlineSide.frame _ a (helper_safe s a safe)).trans
    (OriginalThingDiagonal.first_frame s a safe.1 (safe.2 4 (by simp)))

theorem returned (s : X86Memory.State) :
    (result s).pc=0x2c78d ∧ (result s).core.regs 4=s.regs 4 ∧ (result s).core.regs 1=s.regs 1 := by
  have ret := OriginalDivlineSide.returned (OriginalThingDiagonal.first s).core
  have call := OriginalThingDiagonal.first_observe s
  refine ⟨ret.2.2.2.2.2.trans (congrArg BitVec.toNat call.2.2.2.2.2),?_,?_⟩
  · apply ret.1.trans
    rw [call.2.2.2.2.1]
    simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  · exact ret.2.1.trans (OriginalThingDiagonal.diagonal_observe s).2.2.2.1

/-- Preserve the second endpoint needed by the next point-side CALL. -/
theorem second_endpoint (s : X86Memory.State) :
    load32 (result s).core.memory (s.regs 4+(20#32))=OriginalThingDiagonal.x s+OriginalThingDiagonal.radius s ∧
    (result s).core.regs 5=OriginalThingDiagonal.y2 s := by
  have apart (off : Word) (h : Apart (20#32) (-off)) : Apart (s.regs 4+(20#32)) (s.regs 4-off) := by
    simpa only [BitVec.sub_eq_add_neg] using OriginalPathXStep.apart_translate (s.regs 4) (20#32) (-off) h
  have keep := OriginalDivlineSide.frame (OriginalThingDiagonal.first s).core (s.regs 4+(20#32)) (by
    rw [(OriginalThingDiagonal.first_observe s).2.2.2.2.1]
    intro off ho
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
    rcases ho with rfl|rfl|rfl|rfl
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using apart (8#32) (by unfold Apart; decide)
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using apart (12#32) (by unfold Apart; decide)
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using apart (16#32) (by unfold Apart; decide)
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using apart (20#32) (by unfold Apart; decide))
  refine ⟨keep.trans ?_,(OriginalDivlineSide.returned (OriginalThingDiagonal.first s).core).2.2.2.2.1.trans
    (OriginalThingDiagonal.diagonal_observe s).2.2.1⟩
  change load32 (store32 (OriginalThingDiagonal.diagonal s).memory
    ((OriginalThingDiagonal.diagonal s).regs 4-(4#32)) _) (s.regs 4+(20#32))=_
  rw [(OriginalThingDiagonal.diagonal_observe s).2.2.2.2.1,
    load_store_apart _ _ _ _ (apart (4#32) (by unfold Apart; decide)),
    (OriginalThingDiagonal.diagonal_observe s).2.2.2.2.2,load_store]

structure Inputs (s : X86Memory.State) (trace : Collision.Divline)
    (thing : Collision.SolidThing) (object : Word) : Prop where
  diagonal : OriginalThingDiagonal.Inputs s trace thing object
  traceX : load32 s.memory (0x2ba10#32)=trace.x.raw.toBitVec
  traceY : load32 s.memory (0x2ba14#32)=trace.y.raw.toBitVec
  safe : ∀ a∈[(0x2ba10#32),0x2ba14,0x2ba18,0x2ba1c], Safe s a

theorem helper_inputs (s : X86Memory.State) (trace : Collision.Divline)
    (thing : Collision.SolidThing) (object : Word) (h : Inputs s trace thing object) :
    OriginalDivlineSide.Inputs (OriginalThingDiagonal.first s).core trace
      (points trace thing).1 (points trace thing).2.1 0x2ba10 := by
  have d := OriginalThingDiagonal.live_diagonal s trace thing object h.diagonal
  have a := OriginalThingDiagonal.first_observe s
  have keep (p : Word) (hp : p∈[(0x2ba10#32),0x2ba14,0x2ba18,0x2ba1c]) :=
    OriginalThingDiagonal.first_frame s p (h.safe p hp).1 ((h.safe p hp).2 4 (by simp))
  constructor
  · exact a.2.1.trans ((OriginalThingDiagonal.diagonal_observe s).1.symm.trans d.1)
  · exact a.2.2.1.trans ((OriginalThingDiagonal.diagonal_observe s).2.1.symm.trans d.2.1)
  · exact a.2.2.2.1
  · exact (keep _ (by simp)).trans h.traceX
  · exact (keep _ (by simp)).trans h.traceY
  · exact (keep _ (by simp)).trans h.diagonal.traceDX
  · exact (keep _ (by simp)).trans h.diagonal.traceDY
  · intro p hp
    exact helper_safe s p (h.safe p (by simpa using hp))

theorem live (s : X86Memory.State) (trace : Collision.Divline)
    (thing : Collision.SolidThing) (object : Word) (h : Inputs s trace thing object) :
    (result s).core.regs 0=OriginalDivlineSide.bit (trace.pointSide (points trace thing).1 (points trace thing).2.1) ∧
    (result s).pc=0x2c78d ∧ (result s).core.regs 4=s.regs 4 ∧
    (result s).core.regs 1=object ∧
    (result s).core.regs 5=(points trace thing).2.2.2.raw.toBitVec := by
  have side := OriginalDivlineSide.live _ trace _ _ 0x2ba10 (helper_inputs s trace thing object h)
  have ret := OriginalDivlineSide.returned (OriginalThingDiagonal.first s).core
  have call := OriginalThingDiagonal.first_observe s
  have d := OriginalThingDiagonal.diagonal_observe s
  have live := OriginalThingDiagonal.live_diagonal s trace thing object h.diagonal
  refine ⟨side,?_,?_,?_,?_⟩
  · exact ret.2.2.2.2.2.trans (congrArg BitVec.toNat call.2.2.2.2.2)
  · apply ret.1.trans
    rw [call.2.2.2.2.1]
    simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  · exact ret.2.1.trans (d.2.2.2.1.trans h.diagonal.objectArg)
  · exact ret.2.2.2.2.1.trans live.2.2.1
end Doom.Proofs.OriginalThingFirstSide
