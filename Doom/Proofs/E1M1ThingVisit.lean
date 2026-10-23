import Doom.Proofs.E1M1ThingFinish
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1ThingVisit
open Verification X86 X86Memory X86Control BlockSummary
open OriginalLineMixedInvariant (ArraySafe)
open OriginalThingSecondSide (firstSide lastSide)
abbrev program := E1M1ThingReturn.program

theorem contains_first (pc : Nat) (h : OriginalThingFirstSide.program pc≠none) :
    program pc=OriginalThingFirstSide.program pc := by
  have h0 := E1M1ThingFirstSide.contains_first_side pc h
  have h1 := E1M1ThingCrossing.contains_prior pc (by rw [h0]; exact h)
  have h1 := h1.trans h0
  have h2 := E1M1ThingFraction.contains_prior pc (by rw [h1]; exact h)
  have h2 := h2.trans h1
  have h3 := E1M1ThingReturn.contains_prior pc (by rw [h2]; exact h)
  have h3 := h3.trans h2
  exact h3

theorem contains_second (pc : Nat) (h : OriginalThingSecondSide.program pc≠none) :
    program pc=OriginalThingSecondSide.program pc := by
  have h0 := E1M1ThingCrossing.contains_second pc h
  have h1 := E1M1ThingFraction.contains_prior pc (by rw [h0]; exact h)
  have h1 := h1.trans h0
  have h2 := E1M1ThingReturn.contains_prior pc (by rw [h1]; exact h)
  have h2 := h2.trans h1
  exact h2

theorem contains_callback (pc : Nat) (h : OriginalThingCallback.program pc≠none) :
    program pc=OriginalThingCallback.program pc := by
  have h0 := E1M1ThingCallback.contains_callback pc h
  have h1 := E1M1ThingFirstSide.contains_prior pc (by rw [h0]; exact h)
  have h1 := h1.trans h0
  have h2 := E1M1ThingCrossing.contains_prior pc (by rw [h1]; exact h)
  have h2 := h2.trans h1
  have h3 := E1M1ThingFraction.contains_prior pc (by rw [h2]; exact h)
  have h3 := h3.trans h2
  have h4 := E1M1ThingReturn.contains_prior pc (by rw [h3]; exact h)
  have h4 := h4.trans h3
  exact h4

theorem contains_iterator (pc : Nat) (h : OriginalThingEntry.program pc≠none) :
    program pc=OriginalThingEntry.program pc := by
  have h0 := E1M1ThingEntry.contains_thing pc h
  have h1 := E1M1ThingCallback.contains_prior pc (by rw [h0]; exact h)
  have h1 := h1.trans h0
  have h2 := E1M1ThingFirstSide.contains_prior pc (by rw [h1]; exact h)
  have h2 := h2.trans h1
  have h3 := E1M1ThingCrossing.contains_prior pc (by rw [h2]; exact h)
  have h3 := h3.trans h2
  have h4 := E1M1ThingFraction.contains_prior pc (by rw [h3]; exact h)
  have h4 := h4.trans h3
  have h5 := E1M1ThingReturn.contains_prior pc (by rw [h4]; exact h)
  have h5 := h5.trans h4
  exact h5

/-- Stack-relative protection is independent of which list node is visited. -/
structure ReadSafe (sp a : Word) : Prop where
  enter : ∀ off∈[(4#32),8,12,16,20,24,28], Apart a (sp-off)
  first : Apart a (sp-(52#32)+(20#32)) ∧
    ∀ off∈[(4#32),8,12,16,20], Apart a (sp-(52#32)-off)
  second : Apart a (sp-(52#32)+(16#32))
  fraction : OriginalThingFraction.Safe (sp-(52#32)) a
  array : ArraySafe 0x2ba20 a

structure StackSafe (sp : Word) : Prop where
  enter : E1M1ThingCallback.StackSafe sp 0x2ba20
  first : E1M1ThingFirstSide.StackSafe (sp-(52#32)) 0x2ba20
  second : E1M1ThingCrossing.StackSafe (sp-(52#32)) 0x2ba20
  fraction : E1M1ThingFraction.StackSafe (sp-(52#32)) 0x2ba20
  saved : ∀ off∈[(36#32),48], ArraySafe 0x2ba20 (sp-(52#32)+off)

structure Geometry (memory : Memory) (trace : Collision.Divline)
    (object : Word) (target : Collision.SolidThing) : Prop where
  x : load32 memory (0x2ba10#32)=trace.x.raw.toBitVec
  y : load32 memory (0x2ba14#32)=trace.y.raw.toBitVec
  dx : load32 memory (0x2ba18#32)=trace.dx.raw.toBitVec
  dy : load32 memory (0x2ba1c#32)=trace.dy.raw.toBitVec
  ox : load32 memory (object+(12#32))=target.x.raw.toBitVec
  oy : load32 memory (object+(16#32))=target.y.raw.toBitVec
  radius : load32 memory (object+(64#32))=target.radius.raw.toBitVec

def reads (object : Word) : List Word :=
  [0x2ba10,0x2ba14,0x2ba18,0x2ba1c,object+12,object+16,object+64]

def entry (s : X86Control.State) := OriginalThingCallback.entered s.core s.flags
def result (s : X86Control.State) := E1M1ThingReturn.resumed (entry s).core

structure Inputs (s : X86Control.State) (trace : Collision.Divline)
    (target : Collision.SolidThing) : Prop where
  callback : load32 s.core.memory (s.core.regs 4)=(0x2c720#32)
  geometry : Geometry s.core.memory trace (s.core.regs 2) target
  safe : ∀ a∈reads (s.core.regs 2), ReadSafe (s.core.regs 4) a
  stack : StackSafe (s.core.regs 4)
  computed : firstSide trace target≠lastSide trace target →
    ∃ frac, Collision.interceptVector trace (OriginalThingFraction.diagonal trace target)=.ok frac

theorem entry_inputs (s : X86Control.State) (trace : Collision.Divline)
    (target : Collision.SolidThing) (h : Inputs s trace target) :
    OriginalThingFirstSide.Inputs (entry s).core trace target (s.core.regs 2) := by
  have obs := OriginalThingCallback.enter_observe s.core s.flags
  change (entry s).core.regs 1=_ ∧ (entry s).core.regs 2=_ ∧ (entry s).core.regs 4=_ ∧ _ at obs
  have keep (a : Word) (ha : a∈reads (s.core.regs 2)) :=
    OriginalThingCallback.enter_frame s.core s.flags a (h.safe a ha).enter
  refine ⟨⟨obs.1,?_,?_,?_,?_,?_⟩,?_,?_,?_⟩
  · exact (keep _ (by simp [reads])).trans h.geometry.dx
  · exact (keep _ (by simp [reads])).trans h.geometry.dy
  · exact (keep _ (by simp [reads])).trans h.geometry.ox
  · exact (keep _ (by simp [reads])).trans h.geometry.oy
  · exact (keep _ (by simp [reads])).trans h.geometry.radius
  · exact (keep _ (by simp [reads])).trans h.geometry.x
  · exact (keep _ (by simp [reads])).trans h.geometry.y
  · intro a ha
    change Apart a ((entry s).core.regs 4+(20#32)) ∧ _
    rw [obs.2.2.1]
    exact (h.safe a (by simp only [reads,List.mem_cons,List.not_mem_nil,or_false] at ha ⊢; rcases ha with rfl|rfl|rfl|rfl <;> simp)).first

/-- Reuse both side proofs and the arithmetic proof at any callback body entry. -/
theorem body (s : X86Control.State) (trace : Collision.Divline)
    (target : Collision.SolidThing) (h : Inputs s trace target) :
    (∃ n≤200, X86Routine.Prefix program [] n (entry s) (E1M1ThingReturn.view (entry s).core)) ∧
    E1M1ThingFraction.Outcome (E1M1ThingReturn.view (entry s).core) trace target := by
  let e := (entry s).core
  have sp : e.regs 4=s.core.regs 4-(52#32) := (OriginalThingCallback.enter_observe s.core s.flags).2.2.1
  have geometry := entry_inputs s trace target h
  have scratch (a : Word) (ha : a∈OriginalThingFraction.traceReads) : Apart a (e.regs 4+(16#32)) := by
    rw [sp]
    exact (h.safe a (by simp only [OriginalThingFraction.traceReads,reads,List.mem_cons,List.not_mem_nil,or_false] at ha ⊢; rcases ha with rfl|rfl|rfl|rfl <;> simp)).second
  have traceSafe (a : Word) (ha : a∈OriginalThingFraction.traceReads) : OriginalThingFraction.Safe (e.regs 4) a := by
    rw [sp]
    exact (h.safe a (by simp only [OriginalThingFraction.traceReads,reads,List.mem_cons,List.not_mem_nil,or_false] at ha ⊢; rcases ha with rfl|rfl|rfl|rfl <;> simp)).fraction
  obtain ⟨n,hn,a⟩ := OriginalThingFirstSide.execution e (entry s).flags
  obtain ⟨m,hm,b⟩ := OriginalThingSecondSide.execution (OriginalThingFirstSide.result e).core (OriginalThingFirstSide.result e).flags
  rw [OriginalPathXStep.at_pc _ _ (OriginalThingFirstSide.returned e).1] at b
  have live := OriginalThingSecondSide.live e trace target (s.core.regs 2) geometry scratch
  have fi := OriginalThingFractionInputs.inputs e trace target (s.core.regs 2) geometry scratch traceSafe
  obtain ⟨⟨k,hk,c⟩,outcome⟩ := E1M1ThingFraction.continue_live (OriginalThingSecondSide.crossing e) trace target live.1 live.2 fi h.computed
  refine ⟨⟨n+m+k,by omega,?_⟩,outcome⟩
  exact OriginalGroupBounds.prefix_join
    (OriginalGroupBounds.prefix_join (a.transfer program [] contains_first (by simp))
      (b.transfer program [] contains_second (by simp)))
    (c.transfer program [] E1M1ThingReturn.contains_prior (by simp))

/-- The pre-existing ordered collection survives all geometry scratch writes. -/
theorem body_collection (s : X86Control.State) (trace : Collision.Divline)
    (target : Collision.SolidThing) (h : Inputs s trace target)
    (resolve : Collision.Intercept → Word) (r : Collision.PathResult)
    (tracked : OriginalLineCollection.Tracks s.core 0x2ba20 resolve r.collected 0) :
    OriginalLineCollection.Tracks (E1M1ThingReturn.view (entry s).core).core 0x2ba20 resolve r.collected 0 := by
  have sp : (entry s).core.regs 4=s.core.regs 4-(52#32) := (OriginalThingCallback.enter_observe s.core s.flags).2.2.1
  have a := E1M1ThingCallback.collection s.core s.flags 0x2ba20 resolve r.collected 0 tracked h.stack.enter
  have b := E1M1ThingFirstSide.collection (entry s).core 0x2ba20 resolve r.collected 0 a (by rw [sp]; exact h.stack.first)
  have c := E1M1ThingCrossing.collection (OriginalThingFirstSide.result (entry s).core).core 0x2ba20 resolve r.collected 0 b (by
    rw [(OriginalThingFirstSide.returned (entry s).core).2.1,sp]; exact h.stack.second)
  exact E1M1ThingFraction.collection (OriginalThingSecondSide.crossing (entry s).core) 0x2ba20 resolve r.collected 0 c (by
    rw [(OriginalThingFractionInputs.crossing_regs (entry s).core).1,sp]; exact h.stack.fraction)

set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] load32 OriginalDivlineSide.result OriginalThingSecondSide.result OriginalThingFraction.result

/-- A complete visit, including indirect CALL, live geometry, optional append,
RET and the next-link decision. No hit or reached-state outcome is assumed. -/
theorem execution (s : X86Control.State) (trace : Collision.Divline)
    (target : Collision.SolidThing) (h : Inputs s trace target) (pc : s.pc=0x2c5d2)
    (resolve : Collision.Intercept → Word) (id : Nat) (r : Collision.PathResult)
    (pointer : ∀ frac, resolve ⟨frac,false,id⟩=s.core.regs 2)
    (tracked : OriginalLineCollection.Tracks s.core 0x2ba20 resolve r.collected 0)
    (capacity : r.collected.size<128) :
    (∃ n≤230, X86Routine.Prefix program [] n s (result s)) ∧
    (result s).core.regs 4=s.core.regs 4 ∧
    (result s).core.regs 2=load32 (result s).core.memory (s.core.regs 2+(44#32)) ∧
    (result s).pc=(if (result s).core.regs 2=(0#32) then 0x2c5e2 else 0x2c5d2) ∧
    (∃ next, E1M1ThingFinish.collect trace target id r=.ok next ∧
      OriginalLineCollection.Tracks (result s).core 0x2ba20 resolve next.collected 0) := by
  have started := OriginalThingCallback.enter_execution s.core s.flags h.callback
  rw [OriginalPathXStep.at_pc _ _ pc] at started
  have obs := OriginalThingCallback.enter_observe s.core s.flags
  have sp : (entry s).core.regs 4=s.core.regs 4-(52#32) := obs.2.2.1
  obtain ⟨⟨n,hn,run⟩,outcome⟩ := body s trace target h
  have collection := body_collection s trace target h resolve r tracked
  have cursor : OriginalThingFinish.cursor (E1M1ThingReturn.view (entry s).core).core=
      0x2ba20+BitVec.ofNat 32 (12*r.collected.size) := collection.cursor
  have safe : E1M1ThingReturn.ReturnSafe (entry s).core := by
    intro off ho w hw
    rw [cursor] at hw
    rw [sp]
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl|rfl|rfl|rfl
    · simpa only [OriginalLineCollection.slot,BitVec.add_zero] using (h.stack.saved off ho).1 r.collected.size capacity (0#32) (by simp)
    · exact (h.stack.saved off ho).1 r.collected.size capacity (4#32) (by simp)
    · exact (h.stack.saved off ho).1 r.collected.size capacity (8#32) (by simp)
    · exact (h.stack.saved off ho).2
  have ret : load32 (entry s).core.memory ((entry s).core.regs 4+(48#32))=(0x2c5d7#32) := by
    rw [sp]
    simpa [entry,BitVec.sub_eq_add_neg,BitVec.add_assoc] using obs.2.2.2.2
  have saved : load32 (entry s).core.memory ((entry s).core.regs 4+(36#32))=s.core.regs 2 := by
    rw [sp]
    simpa [entry,BitVec.sub_eq_add_neg,BitVec.add_assoc] using obs.2.2.2.1
  obtain ⟨⟨m,hm,tail⟩,memory,stackOut,next,pcOut⟩ := E1M1ThingReturn.execution (entry s).core trace target outcome safe ret
  have arg := (E1M1ThingReturn.view_regs (entry s).core).2.trans obs.1
  obtain ⟨after,production,encoded⟩ := E1M1ThingFinish.finish_collect (E1M1ThingReturn.view (entry s).core)
    trace target id r resolve (s.core.regs 2) outcome arg pointer collection capacity
  refine ⟨⟨10+n+m,by omega,OriginalGroupBounds.prefix_join
    (OriginalGroupBounds.prefix_join (started.transfer program [] contains_callback (by simp)) run) tail⟩,?_,?_,pcOut,after,production,?_⟩
  · exact stackOut.trans (by rw [sp]; simp [BitVec.sub_eq_add_neg,BitVec.add_assoc])
  · rw [saved] at next
    apply next.trans
    change load32 (E1M1ThingReturn.finished (entry s).core).core.memory _=
      load32 (E1M1ThingReturn.resumed (entry s).core).core.memory _
    rw [memory]
  · refine ⟨?_,?_,encoded.room⟩
    · change OriginalLineFinish.Encodes (E1M1ThingReturn.resumed (entry s).core).core.memory 0x2ba20 resolve after.collected
      rw [memory]; exact encoded.encoded
    · change load32 (E1M1ThingReturn.resumed (entry s).core).core.memory (0x2c028#32)=_
      rw [memory]; exact encoded.cursor

/-- Non-aliasing reads are transported through every write in a complete visit. -/
theorem frame (s : X86Control.State) (trace : Collision.Divline)
    (target : Collision.SolidThing) (h : Inputs s trace target)
    (resolve : Collision.Intercept → Word) (r : Collision.PathResult)
    (tracked : OriginalLineCollection.Tracks s.core 0x2ba20 resolve r.collected 0)
    (capacity : r.collected.size<128) (a : Word) (safe : ReadSafe (s.core.regs 4) a) :
    load32 (result s).core.memory a=load32 s.core.memory a := by
  have sp : (entry s).core.regs 4=s.core.regs 4-(52#32) := (OriginalThingCallback.enter_observe s.core s.flags).2.2.1
  have firstSafe : OriginalThingFirstSide.Safe (entry s).core a := by
    change Apart a ((entry s).core.regs 4+(20#32)) ∧ _
    rw [sp]; exact safe.first
  have one := OriginalThingFirstSide.frame (entry s).core a firstSafe
  have two := OriginalThingSecondSide.frame (OriginalThingFirstSide.result (entry s).core).core a (by
    rw [(OriginalThingFirstSide.returned (entry s).core).2.1,sp]; exact ⟨safe.second,safe.first.2⟩)
  have fraction : load32 (E1M1ThingReturn.view (entry s).core).core.memory a=load32 (entry s).core.memory a := by
    unfold E1M1ThingReturn.view E1M1ThingFraction.continueFraction
    split
    · apply (OriginalThingFraction.frame _ a ?_).trans (two.trans one)
      change OriginalThingFraction.Safe ((OriginalThingSecondSide.crossing (entry s).core).core.regs 4) a
      rw [(OriginalThingFractionInputs.crossing_regs (entry s).core).1,sp]
      exact safe.fraction
    · exact two.trans one
  have trackedView := body_collection s trace target h resolve r tracked
  have cursor : OriginalThingFinish.cursor (E1M1ThingReturn.view (entry s).core).core=
      0x2ba20+BitVec.ofNat 32 (12*r.collected.size) := trackedView.cursor
  have finish := OriginalThingFinish.frame (E1M1ThingReturn.view (entry s).core) a (by
    intro w hw
    rw [cursor] at hw
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl|rfl|rfl|rfl
    · simpa only [OriginalLineCollection.slot,BitVec.add_zero] using safe.array.1 r.collected.size capacity (0#32) (by simp)
    · exact safe.array.1 r.collected.size capacity (4#32) (by simp)
    · exact safe.array.1 r.collected.size capacity (8#32) (by simp)
    · exact safe.array.2)
  have enter := OriginalThingCallback.enter_frame s.core s.flags a safe.enter
  change load32 (OriginalThingCallback.resumed (E1M1ThingReturn.finished (entry s).core).core).core.memory a=_
  rw [(OriginalThingCallback.resumed_observe (E1M1ThingReturn.finished (entry s).core).core).1]
  exact finish.trans (fraction.trans enter)
end Doom.Proofs.E1M1ThingVisit
