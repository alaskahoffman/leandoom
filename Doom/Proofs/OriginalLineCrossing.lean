import Doom.Proofs.E1M1LineTail
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.OriginalLineCrossing
open Verification X86 X86Memory X86Control BlockSummary
abbrev program := OriginalLineTail.program
abbrev first := E1M1LineSecondPoint.firstReturn
def tested (s : X86Memory.State) := E1M1LineSecondPoint.continueTest (first s)
def result (s : X86Memory.State) := OriginalLineTail.result (tested s).core

def SideSafe (s : X86Memory.State) (a : Word) : Prop :=
  ∀ off∈[(4#32),8,12,16,20,40,44,48,52,56], Apart a (s.regs 4-off)
def ScratchSafe (s : X86Memory.State) (a : Word) : Prop :=
  ∀ off∈OriginalLineTail.stackOffsets, Apart a (s.regs 4-(36#32)+off)
def Protected (s : X86Memory.State) (a : Word) : Prop :=
  SideSafe s a ∧ ScratchSafe s a ∧ OriginalLineTail.RecordSafe s a

/-- Geometry and crossing are supplied at callback entry, before both side calls. -/
structure Inputs (s : X86Memory.State) (trace : Collision.Divline) (line : Collision.Line)
    (p v w : Word) : Prop where
  entry : OriginalLineInterceptEntry.Inputs s trace line p v
  data : E1M1LineSecondPoint.LineData s line p v w
  crosses : OriginalLineSecondPoint.firstSide trace line≠OriginalLineSecondPoint.lastSide trace line

variable (s : X86Memory.State) (trace : Collision.Divline) (line : Collision.Line)
  (p v w : Word) (h : Inputs s trace line p v w)

include h

theorem tested_form : tested s =
    ⟨(OriginalLineSecondPoint.second trace.usesDivlineTest (first s).core).core,
      some (compare32 ((OriginalLineSecondPoint.second trace.usesDivlineTest (first s).core).core.regs 6)
        ((OriginalLineSecondPoint.second trace.usesDivlineTest (first s).core).core.regs 0)),0x2c691⟩ := by
  rw [tested,E1M1LineSecondPoint.at_return _ _ (E1M1LineSecondPoint.first_return_regs s trace line p v h.entry).2.2,
    OriginalLineSecondPoint.live _ trace line p v w (E1M1LineSecondPoint.entry_inputs s trace line p v w h.entry h.data),if_neg h.crosses]

theorem tested_regs : (tested s).pc=0x2c691 ∧ (tested s).core.regs 4=s.regs 4-(36#32) ∧
    (tested s).core.regs 1=p := by
  rw [tested_form s trace line p v w h]
  have a := OriginalLineSecondPoint.second_saved trace.usesDivlineTest (first s).core
  have b := E1M1LineSecondPoint.first_return_regs s trace line p v h.entry
  exact ⟨rfl,a.1.trans b.1,a.2.1.trans b.2.1⟩

theorem tested_frame (a : Word) (safe : SideSafe s a) :
    load32 (tested s).core.memory a=load32 s.memory a := by
  rw [tested_form s trace line p v w h]
  have inner : ∀ off∈[(4#32),8,12,16,20], Apart a ((first s).core.regs 4-off) := by
    rw [(E1M1LineSecondPoint.first_return_regs s trace line p v h.entry).1]
    intro off ho
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
    rcases ho with rfl|rfl|rfl|rfl|rfl
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe 40 (by simp)
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe 44 (by simp)
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe 48 (by simp)
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe 52 (by simp)
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe 56 (by simp)
  exact (OriginalLineSecondPoint.second_frame _ _ a inner).trans
    (E1M1LineSecondPoint.first_return_frame s trace line p v h.entry a safe)

theorem fraction_inputs
    (safe : ∀ a∈OriginalLineFraction.reads p v, ScratchSafe s a) :
    OriginalLineFraction.Inputs (tested s).core trace line p v := by
  have keep (a : Word) (ha : a∈OriginalLineFraction.reads p v) :
      load32 (tested s).core.memory a=load32 s.memory a := by
    apply tested_frame s trace line p v w h a
    apply h.data.safe a
    simp only [OriginalLineFraction.reads,List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp [OriginalLineSecondPoint.reads]
  refine ⟨(tested_regs s trace line p v w h).2.2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [keep _ (by simp [OriginalLineFraction.reads])]; exact h.entry.vertex
  · rw [keep _ (by simp [OriginalLineFraction.reads])]; exact h.entry.vertexX
  · rw [keep _ (by simp [OriginalLineFraction.reads])]; exact h.entry.vertexY
  · rw [keep _ (by simp [OriginalLineFraction.reads])]; exact h.data.dx
  · rw [keep _ (by simp [OriginalLineFraction.reads])]; exact h.data.dy
  · rw [keep _ (by simp [OriginalLineFraction.reads])]; exact h.entry.traceX
  · rw [keep _ (by simp [OriginalLineFraction.reads])]; exact h.entry.traceY
  · rw [keep _ (by simp [OriginalLineFraction.reads])]; exact h.entry.traceDX
  · rw [keep _ (by simp [OriginalLineFraction.reads])]; exact h.entry.traceDY
  · intro a ha off ho
    rw [(tested_regs s trace line p v w h).2.1]
    apply safe a ha off
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
    rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp [OriginalLineTail.stackOffsets]

theorem tail_inputs (frac : Fixed) (flags : Nat)
    (computed : Collision.interceptVector trace ⟨line.x,line.y,line.dx,line.dy⟩=.ok frac)
    (safe : ∀ a∈OriginalLineFraction.reads p v, ScratchSafe s a)
    (active : load32 s.memory (0x2c024#32)≠0 ↔ flags &&& 4≠0)
    (back : load32 s.memory (p+(50#32))=0 ↔ line.back.isNone=true)
    (activeSafe : SideSafe s (0x2c024#32) ∧ ScratchSafe s (0x2c024#32))
    (backSafe : SideSafe s (p+(50#32)) ∧ ScratchSafe s (p+(50#32))) :
    OriginalLineTail.Inputs (tested s).core trace line frac flags p v := by
  refine ⟨fraction_inputs s trace line p v w h safe,computed,?_,?_,?_,?_⟩
  · rw [tested_frame s trace line p v w h _ activeSafe.1]; exact active
  · rw [tested_frame s trace line p v w h _ backSafe.1]; exact back
  · intro off ho; rw [(tested_regs s trace line p v w h).2.1]; exact activeSafe.2 off ho
  · intro off ho; rw [(tested_regs s trace line p v w h).2.1]; exact backSafe.2 off ho

theorem tail_protected (a : Word) (cursor : SideSafe s (0x2c028#32)) (safe : Protected s a) :
    OriginalLineTail.Protected (tested s).core a := by
  constructor
  · intro off ho; rw [(tested_regs s trace line p v w h).2.1]; exact safe.2.1 off ho
  · have eq : OriginalLineFinish.cursor (tested s).core=OriginalLineFinish.cursor s :=
      tested_frame s trace line p v w h _ cursor
    simpa only [OriginalLineTail.RecordSafe,eq] using safe.2.2

theorem frame (a : Word) (cursor : SideSafe s (0x2c028#32) ∧ ScratchSafe s (0x2c028#32))
    (safe : Protected s a) : load32 (result s).core.memory a=load32 s.memory a := by
  have cs : OriginalLineTail.StackSafe (tested s).core (0x2c028#32) := by
    intro off ho; rw [(tested_regs s trace line p v w h).2.1]; exact cursor.2 off ho
  exact (OriginalLineTail.frame _ a cs (tail_protected s trace line p v w h a cursor.1 safe)).trans
    (tested_frame s trace line p v w h a safe.1)


/-- The caller's cursor is saved by the prologue, not assumed in later memory. -/
theorem saved_cursor : load32 (tested s).core.memory (s.regs 4-(12#32))=s.regs 2 := by
  have apart (x y : Word) (hy : Apart (-x) (-y)) := OriginalLineSide.slots_apart (s.regs 4) x y hy
  have sp := (OriginalLineInterceptEntry.gate_preserves (OriginalLineInterceptEntry.prepared s)).2.2.trans
    (OriginalLineInterceptEntry.prepared_regs s).2.1
  have callKeep : load32 (OriginalLineInterceptEntry.first s).core.memory (s.regs 4-(12#32))=s.regs 2 := by
    unfold OriginalLineInterceptEntry.first
    rw [OriginalLineInterceptEntry.call_frame]
    · rw [(OriginalLineInterceptEntry.gate_preserves (OriginalLineInterceptEntry.prepared s)).1,
        OriginalLineInterceptEntry.prepared_memory]
      unfold OriginalLineInterceptEntry.saved
      change load32 (store32 (store32 (store32 _ (s.regs 4-(12#32)) (s.regs 2))
        (s.regs 4-(16#32)) _) (s.regs 4-(20#32)) _) (s.regs 4-(12#32))=s.regs 2
      rw [load_store_apart _ _ _ _ (apart (12#32) (20#32) (by unfold Apart; decide)),
        load_store_apart _ _ _ _ (apart (12#32) (16#32) (by unfold Apart; decide)),load_store]
    · rw [sp]
      simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using apart 12 40 (by unfold Apart; decide)
  have helperSafe : ∀ off∈[(4#32),8,12,16],
      Apart (s.regs 4-(12#32)) ((OriginalLineInterceptEntry.first s).core.regs 4-off) := by
    rw [(OriginalLineInterceptEntry.live s trace line p v h.entry).stack]
    intro off ho
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
    rcases ho with rfl|rfl|rfl|rfl
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using apart 12 44 (by unfold Apart; decide)
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using apart 12 48 (by unfold Apart; decide)
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using apart 12 52 (by unfold Apart; decide)
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using apart 12 56 (by unfold Apart; decide)
  have firstKeep : load32 (first s).core.memory (s.regs 4-(12#32))=s.regs 2 := by
    rw [first,E1M1LineSecondPoint.first_return_form s trace line p v h.entry]
    split
    · exact (OriginalDivlineSide.frame _ _ helperSafe).trans callKeep
    · exact (OriginalLineSide.frame _ _ helperSafe).trans callKeep
  rw [tested_form s trace line p v w h]
  apply (OriginalLineSecondPoint.second_frame _ _ _ ?_).trans firstKeep
  rw [(E1M1LineSecondPoint.first_return_regs s trace line p v h.entry).1]
  intro off ho
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
  rcases ho with rfl|rfl|rfl|rfl|rfl
  · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using apart 12 40 (by unfold Apart; decide)
  · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using apart 12 44 (by unfold Apart; decide)
  · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using apart 12 48 (by unfold Apart; decide)
  · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using apart 12 52 (by unfold Apart; decide)
  · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using apart 12 56 (by unfold Apart; decide)

omit h

theorem return_side_safe : SideSafe s (s.regs 4) := by
  intro off ho
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
  rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simpa only [BitVec.sub_zero] using OriginalLineSide.slots_apart (s.regs 4) (0#32) _ (by unfold Apart; decide)

theorem saved_scratch_safe (offset : Word) (ho : offset∈[(0#32),12]) :
    ScratchSafe s (s.regs 4-offset) := by
  intro off hm
  have base : Apart (-offset) (-(36#32)+off) := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
    simp only [OriginalLineTail.stackOffsets,List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases ho with rfl|rfl <;> rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> unfold Apart <;> decide
  simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using OriginalPathXStep.apart_translate (s.regs 4) (-offset) (-(36#32)+off) base

include h

theorem tail_layout (cursor : SideSafe s (0x2c028#32) ∧ ScratchSafe s (0x2c028#32))
    (retSafe : OriginalLineTail.RecordSafe s (s.regs 4)) : OriginalLineTail.Layout (tested s).core := by
  constructor
  · intro off ho; rw [(tested_regs s trace line p v w h).2.1]; exact cursor.2 off ho
  · rw [(tested_regs s trace line p v w h).2.1]
    have addr : s.regs 4-(36#32)+(36#32)=s.regs 4 := by bv_decide
    rw [addr]
    apply tail_protected s trace line p v w h _ cursor.1
    exact ⟨return_side_safe s,by simpa using saved_scratch_safe s 0 (by simp),retSafe⟩

theorem tail_return (ret : load32 s.memory (s.regs 4)=(0x2c578#32)) :
    load32 (tested s).core.memory ((tested s).core.regs 4+(36#32))=(0x2c578#32) := by
  rw [(tested_regs s trace line p v w h).2.1]
  have addr : s.regs 4-(36#32)+(36#32)=s.regs 4 := by bv_decide
  rw [addr,tested_frame s trace line p v w h _ (return_side_safe s),ret]

omit h

/-- Transfer the unchanged original byte programs into the existing firing program. -/
theorem contains_tests (pc : Nat) (hn : E1M1LineSecondPoint.program pc≠none) :
    program pc=E1M1LineSecondPoint.program pc := E1M1LineTail.contains_prior pc hn

theorem tests_execution (f : Option Flags) :
    ∃ n≤162, X86Routine.Prefix program [] n ⟨s,f,0x2c5f0⟩ (tested s) := by
  obtain ⟨n,hn,a⟩ := OriginalLineInterceptEntry.first_execution s f
  have intoEntry := a.transfer E1M1LineInterceptEntry.program [] E1M1LineInterceptEntry.contains_entry (by simp)
  have intoLine := intoEntry.transfer E1M1LineSide.program [] E1M1LineSide.contains_prior (by simp)
  obtain ⟨m,hm,b⟩ := E1M1LineSide.continue_execution (OriginalLineInterceptEntry.first s)
  have ab := (OriginalGroupBounds.prefix_join intoLine b).transfer E1M1DivlineSide.program [] E1M1DivlineSide.contains_prior (by simp)
  obtain ⟨k,hk,c⟩ := E1M1DivlineSide.continue_execution (E1M1LineSide.continueSide (OriginalLineInterceptEntry.first s))
  have abc := (OriginalGroupBounds.prefix_join ab c).transfer E1M1LineSecondPoint.program [] E1M1LineSecondPoint.contains_prior (by simp)
  obtain ⟨j,hj,d⟩ := E1M1LineSecondPoint.continue_execution (first s)
  exact ⟨n+m+k+j,by omega,(OriginalGroupBounds.prefix_join abc d).transfer program [] contains_tests (by simp)⟩


/-- Tail requirements expressed entirely in callback-entry memory. -/
structure TailData (s : X86Memory.State) (trace : Collision.Divline) (line : Collision.Line)
    (frac : Fixed) (flags : Nat) (p v : Word) : Prop where
  computed : Collision.interceptVector trace ⟨line.x,line.y,line.dx,line.dy⟩=.ok frac
  geometrySafe : ∀ a∈OriginalLineFraction.reads p v, ScratchSafe s a
  active : load32 s.memory (0x2c024#32)≠0 ↔ flags &&& 4≠0
  back : load32 s.memory (p+(50#32))=0 ↔ line.back.isNone=true
  activeSafe : SideSafe s (0x2c024#32) ∧ ScratchSafe s (0x2c024#32)
  backSafe : SideSafe s (p+(50#32)) ∧ ScratchSafe s (p+(50#32))
  cursor : SideSafe s (0x2c028#32) ∧ ScratchSafe s (0x2c028#32)
  ret : load32 s.memory (s.regs 4)=(0x2c578#32)
  returnSafe : OriginalLineTail.RecordSafe s (s.regs 4)

include h
variable (frac : Fixed) (flags : Nat) (data : TailData s trace line frac flags p v)
include data

theorem ready : OriginalLineTail.Inputs (tested s).core trace line frac flags p v :=
  tail_inputs s trace line p v w h frac flags data.computed data.geometrySafe
    data.active data.back data.activeSafe data.backSafe

theorem execution (f : Option Flags) :
    ∃ n≤270, X86Routine.Prefix program [] n ⟨s,f,0x2c5f0⟩ (result s) := by
  obtain ⟨n,hn,a⟩ := tests_execution s f
  obtain ⟨m,hm,b⟩ := OriginalLineTail.execution (tested s).core (tested s).flags
    (OriginalLineTail.arithmetic _ trace line frac flags p v (ready s trace line p v w h frac flags data))
    (tail_layout s trace line p v w h data.cursor data.returnSafe)
    (tail_return s trace line p v w h data.ret)
  rw [OriginalPathXStep.at_pc _ _ (tested_regs s trace line p v w h).1] at b
  exact ⟨n+m,by omega,OriginalGroupBounds.prefix_join a b⟩

theorem continued (savedSafe : OriginalLineTail.RecordSafe s (s.regs 4-(12#32)))
    (keepGoing : frac.raw<0 ∨ (flags &&& 4 != 0 && frac.raw<65536 && line.back.isNone)=false) :
    (result s).pc=0x2c57f ∧ (result s).core.regs 2=s.regs 2+(2#32) ∧
    (result s).core.regs 4=s.regs 4+(4#32) := by
  have addr : (tested s).core.regs 4+(24#32)=s.regs 4-(12#32) := by
    rw [(tested_regs s trace line p v w h).2.1]; bv_decide
  have protect : OriginalLineTail.Protected (tested s).core ((tested s).core.regs 4+(24#32)) := by
    rw [addr]
    constructor
    · intro off ho
      rw [(tested_regs s trace line p v w h).2.1]
      exact saved_scratch_safe s 12 (by simp) off ho
    · have eq : OriginalLineFinish.cursor (tested s).core=OriginalLineFinish.cursor s :=
        tested_frame s trace line p v w h _ data.cursor.1
      simpa only [OriginalLineTail.RecordSafe,eq] using savedSafe
  have k := OriginalLineTail.live_continued (tested s).core trace line frac flags p v (s.regs 2)
    (ready s trace line p v w h frac flags data) (tail_layout s trace line p v w h data.cursor data.returnSafe)
    (by rw [addr]; exact saved_cursor s trace line p v w h) protect keepGoing
  refine ⟨k.1,k.2.1,?_⟩
  rw [result,k.2.2,(tested_regs s trace line p v w h).2.1]
  bv_decide

/-- Both side tests and the fraction helper preserve the initial ordered array;
the actual DOS writes agree with the production append and cursor advance. -/
theorem live_append (r : Collision.PathResult) (id : Nat) (base : Word)
    (resolve : Collision.Intercept → Word)
    (nonnegative : ¬frac.raw<0) (clear : (flags &&& 4 != 0 && frac.raw<65536 && line.back.isNone)=false)
    (capacity : r.collected.size<128)
    (encoded : OriginalLineFinish.Encodes s.memory base resolve r.collected)
    (atEnd : OriginalLineFinish.cursor s=base+BitVec.ofNat 32 (12*r.collected.size))
    (pointer : resolve ⟨frac,true,id⟩=p)
    (newSafe : ∀ off∈[(0#32),4,8], Apart (OriginalLineFinish.cursor s+off) (0x2c028#32))
    (oldSafe : ∀ i<r.collected.size, ∀ off∈[(0#32),4,8], Protected s (base+BitVec.ofNat 32 (12*i)+off)) :
    Collision.appendIntercept r ⟨frac,true,id⟩=.ok {r with collected:=r.collected.push ⟨frac,true,id⟩} ∧
    OriginalLineFinish.Encodes (result s).core.memory base resolve (r.collected.push ⟨frac,true,id⟩) ∧
    load32 (result s).core.memory (0x2c028#32)=base+BitVec.ofNat 32 (12*(r.collected.size+1)) := by
  have cur : OriginalLineFinish.cursor (tested s).core=OriginalLineFinish.cursor s :=
    tested_frame s trace line p v w h _ data.cursor.1
  apply OriginalLineTail.live_append (tested s).core trace line frac flags p v base
    (ready s trace line p v w h frac flags data) r id resolve
  · intro off ho; rw [(tested_regs s trace line p v w h).2.1]; exact data.cursor.2 off ho
  · exact nonnegative
  · exact clear
  · exact capacity
  · intro i hi
    have keep (off : Word) (ho : off∈[(0#32),4,8]) :=
      tested_frame s trace line p v w h _ (oldSafe i hi off ho).1
    have old := encoded i hi
    unfold OriginalLineFinish.RecordAt at old ⊢
    rw [show load32 (tested s).core.memory (base+BitVec.ofNat 32 (12*i))=load32 s.memory (base+BitVec.ofNat 32 (12*i)) by simpa using keep 0 (by simp),
      keep (4#32) (by simp),keep (8#32) (by simp)]
    exact old
  · rw [cur]; exact atEnd
  · exact pointer
  · simpa only [cur] using newSafe
  · intro i hi off ho
    exact tail_protected s trace line p v w h _ data.cursor.1 (oldSafe i hi off ho)

end Doom.Proofs.OriginalLineCrossing
