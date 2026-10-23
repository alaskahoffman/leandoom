import Doom.Proofs.OriginalLineNoInsert
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.OriginalLineMixedInvariant
open Verification X86 X86Memory X86Control BlockSummary
open OriginalLineCollection (slot Tracks)
abbrev program := OriginalLineDispatch.program
abbrev address := OriginalLineInvariant.address
abbrev atIndex := OriginalLineInvariant.atIndex

theorem crossing_inputs (s t : X86Memory.State) (trace : Collision.Divline)
    (line : Collision.Line) (p v w : Word) (h : OriginalLineCrossing.Inputs s trace line p v w)
    (arg : t.regs 0=s.regs 0) (sp : t.regs 4=s.regs 4)
    (memory : ∀ a∈OriginalLineSecondPoint.reads p v w, load32 t.memory a=load32 s.memory a) :
    OriginalLineCrossing.Inputs t trace line p v w := by
  refine ⟨?_,?_,h.crosses⟩
  · refine ⟨arg.trans h.entry.lineArg,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · rw [memory _ (by simp [OriginalLineSecondPoint.reads])]; exact h.entry.traceX
    · rw [memory _ (by simp [OriginalLineSecondPoint.reads])]; exact h.entry.traceY
    · rw [memory _ (by simp [OriginalLineSecondPoint.reads])]; exact h.entry.traceDX
    · rw [memory _ (by simp [OriginalLineSecondPoint.reads])]; exact h.entry.traceDY
    · rw [memory _ (by simp [OriginalLineSecondPoint.reads])]; exact h.entry.vertex
    · rw [memory _ (by simp [OriginalLineSecondPoint.reads])]; exact h.entry.vertexX
    · rw [memory _ (by simp [OriginalLineSecondPoint.reads])]; exact h.entry.vertexY
    · rw [sp]; exact h.entry.safeReads
  · refine ⟨?_,?_,?_,?_,?_,?_⟩
    · rw [memory _ (by simp [OriginalLineSecondPoint.reads])]; exact h.data.vertex2
    · rw [memory _ (by simp [OriginalLineSecondPoint.reads])]; exact h.data.x2
    · rw [memory _ (by simp [OriginalLineSecondPoint.reads])]; exact h.data.y2
    · rw [memory _ (by simp [OriginalLineSecondPoint.reads])]; exact h.data.dx
    · rw [memory _ (by simp [OriginalLineSecondPoint.reads])]; exact h.data.dy
    · rw [sp]; exact h.data.safe

structure Candidate where
  trace : Collision.Divline
  line : Collision.Line
  p : Word
  v : Word
  w : Word
  frac : Fixed
  flags : Nat
  id : Nat
  crosses : Bool

def Candidate.hit (c : Candidate) : Collision.Intercept := ⟨c.frac,true,c.id⟩
def Candidate.reads (c : Candidate) : List Word :=
  OriginalLineSecondPoint.reads c.p c.v c.w ++ [c.p+(50#32),(0x2c024#32)]

def Candidate.early (c : Candidate) : Bool :=
  c.flags &&& 4 != 0 && c.frac.raw<65536 && c.line.back.isNone
def Candidate.Continues (c : Candidate) : Prop := c.frac.raw<0 ∨ c.early=false

structure Crossing (s : X86Memory.State) (c : Candidate) : Prop where
  geometry : OriginalLineCrossing.Inputs (OriginalLineDispatch.view s) c.trace c.line c.p c.v c.w
  computed : Collision.interceptVector c.trace ⟨c.line.x,c.line.y,c.line.dx,c.line.dy⟩=.ok c.frac
  active : load32 s.memory (0x2c024#32)≠0 ↔ c.flags &&& 4≠0
  back : load32 s.memory (c.p+(50#32))=0 ↔ c.line.back.isNone=true

/-- Protection from every possible bounded record write, independent of the
current number of collected hits. -/
def ArraySafe (base a : Word) : Prop :=
  (∀ k<128, ∀ off∈[(0#32),4,8], Apart a (slot base k off)) ∧ Apart a (0x2c028#32)

/-- All premises refer to initial memory and a finite candidate prefix. Crossing
fractions may be negative, append, or stop. No sentinel or suffix is assumed. -/
structure Initial (s : X86Memory.State) (n : Nat) (base : Word) (resolve : Collision.Intercept → Word) where
  candidates : Nat → Candidate
  words : List Word
  listWords : ∀ i≤n, address s i∈words
  fixedWords : ∀ a∈[s.regs 4,(0x13580#32),0x2c120], a∈words
  target : load32 s.memory (s.regs 4)=(0x2c5f0#32)
  nonlast : ∀ i<n, OriginalLineCell.itemWord (atIndex s i)≠(0xffffffff#32)
  reads : ∀ i<n, ∀ a∈(candidates i).reads, a∈words
  rejection : ∀ i<n, (candidates i).crosses=false → OriginalLineReject.Inputs
    (OriginalLineDispatch.view (atIndex s i)) (candidates i).trace (candidates i).line
      (candidates i).p (candidates i).v (candidates i).w
  crossing : ∀ i<n, (candidates i).crosses=true → Crossing (atIndex s i) (candidates i)
  pointer : ∀ i<n, (candidates i).crosses=true → resolve (candidates i).hit=(candidates i).p
  separated : ∀ i<n, ∀ a∈words,
    OriginalLineDispatch.Safe (atIndex s i) a ∧
    OriginalLineCrossing.SideSafe (OriginalLineDispatch.view (atIndex s i)) a ∧
    OriginalLineCrossing.ScratchSafe (OriginalLineDispatch.view (atIndex s i)) a
  arrayWords : ∀ a∈words, ArraySafe base a
  cursorSafe : ∀ i<n, OriginalLineDispatch.Safe (atIndex s i) (0x2c028#32) ∧
    OriginalLineCrossing.SideSafe (OriginalLineDispatch.view (atIndex s i)) (0x2c028#32) ∧
    OriginalLineCrossing.ScratchSafe (OriginalLineDispatch.view (atIndex s i)) (0x2c028#32)
  stackArray : ∀ a∈[s.regs 4-(4#32),s.regs 4-(16#32)], ArraySafe base a
  stampSafe : ∀ i<n, Apart (OriginalLineDispatch.stamp (atIndex s i)) (s.regs 4-(4#32))
  storage : ∀ i<n, OriginalLineCollection.Layout (atIndex s i) base

structure Stable (initial : X86Memory.State) {n : Nat} {base : Word} {resolve : Collision.Intercept → Word}
    (h : Initial initial n base resolve) (i : Nat) (s : X86Control.State) (r : Collision.PathResult) : Prop where
  pc : s.pc=0x2c57f
  cursor : s.core.regs 2=address initial i
  stack : s.core.regs 4=initial.regs 4
  memory : ∀ a∈h.words, load32 s.core.memory a=load32 initial.memory a
  collection : Tracks s.core base resolve r.collected (n-i)

variable (initial : X86Memory.State) (n : Nat) (base : Word) (resolve : Collision.Intercept → Word)
  (h : Initial initial n base resolve) (i : Nat) (s : X86Control.State) (r : Collision.PathResult)
  (inv : Stable initial h i s r)
include inv

theorem item (hi : i≤n) : OriginalLineCell.item s.core=load16 initial.memory (address initial i) := by
  have half := congrArg (fun x : Word => x.extractLsb' 0 16) (inv.memory _ (h.listWords i hi))
  rw [SectorDispatch.load_half,SectorDispatch.load_half] at half
  simpa only [OriginalLineCell.item,inv.cursor] using half

theorem pointer (hi : i≤n) : OriginalLineDispatch.pointer s.core=OriginalLineDispatch.pointer (atIndex initial i) := by
  simp only [OriginalLineDispatch.pointer,OriginalLineCell.itemWord,item initial n base resolve h i s r inv hi]
  rw [inv.memory _ (h.fixedWords _ (by simp))]
  rfl

theorem view_stack : (OriginalLineDispatch.view s.core).regs 4=
    (OriginalLineDispatch.view (atIndex initial i)).regs 4 := by
  change (OriginalLineDispatch.entry s.core).core.regs 4=(OriginalLineDispatch.entry (atIndex initial i)).core.regs 4
  rw [(OriginalLineDispatch.entry_regs _).2.2,(OriginalLineDispatch.entry_regs _).2.2,inv.stack]
  rfl

theorem dispatch_safe (hi : i≤n) (a : Word) (safe : OriginalLineDispatch.Safe (atIndex initial i) a) :
    OriginalLineDispatch.Safe s.core a := by
  unfold OriginalLineDispatch.Safe OriginalLineDispatch.stamp
  rw [pointer initial n base resolve h i s r inv hi,inv.stack]
  exact safe

theorem side_safe (a : Word) (safe : OriginalLineCrossing.SideSafe (OriginalLineDispatch.view (atIndex initial i)) a) :
    OriginalLineCrossing.SideSafe (OriginalLineDispatch.view s.core) a := by
  unfold OriginalLineCrossing.SideSafe
  rw [view_stack initial n base resolve h i s r inv]
  exact safe

theorem scratch_safe (a : Word) (safe : OriginalLineCrossing.ScratchSafe (OriginalLineDispatch.view (atIndex initial i)) a) :
    OriginalLineCrossing.ScratchSafe (OriginalLineDispatch.view s.core) a := by
  unfold OriginalLineCrossing.ScratchSafe
  rw [view_stack initial n base resolve h i s r inv]
  exact safe

theorem protection (hi : i<n) (a : Word) (ha : a∈h.words) :
    OriginalLineDispatch.Safe s.core a ∧ OriginalLineCrossing.SideSafe (OriginalLineDispatch.view s.core) a ∧
    OriginalLineCrossing.ScratchSafe (OriginalLineDispatch.view s.core) a := by
  have safe := h.separated i hi a ha
  exact ⟨dispatch_safe initial n base resolve h i s r inv (by omega) a safe.1,
    side_safe initial n base resolve h i s r inv a safe.2.1,
    scratch_safe initial n base resolve h i s r inv a safe.2.2⟩

theorem metadata (hi : i<n) : OriginalLineDispatch.Safe s.core (0x2c028#32) ∧
    OriginalLineCrossing.SideSafe (OriginalLineDispatch.view s.core) (0x2c028#32) ∧
    OriginalLineCrossing.ScratchSafe (OriginalLineDispatch.view s.core) (0x2c028#32) := by
  have safe := h.cursorSafe i hi
  exact ⟨dispatch_safe initial n base resolve h i s r inv (by omega) _ safe.1,
    side_safe initial n base resolve h i s r inv _ safe.2.1,
    scratch_safe initial n base resolve h i s r inv _ safe.2.2⟩

theorem storage (hi : i<n) : OriginalLineCollection.Layout s.core base := by
  have old := h.storage i hi
  exact ⟨fun k hk off ho => dispatch_safe initial n base resolve h i s r inv (by omega) _ (old.dispatch k hk off ho),
    fun k hk off ho => side_safe initial n base resolve h i s r inv _ (old.side k hk off ho),
    fun k hk off ho => scratch_safe initial n base resolve h i s r inv _ (old.scratch k hk off ho),old.metadata⟩

theorem record_safe (hi : i<n) (a : Word) (safe : ArraySafe base a) :
    OriginalLineTail.RecordSafe (OriginalLineDispatch.view s.core) a := by
  have cap : r.collected.size<128 := by have room := inv.collection.room; omega
  intro addr ha
  change addr∈[OriginalLineFinish.cursor s.core,OriginalLineFinish.cursor s.core+(4#32),
    OriginalLineFinish.cursor s.core+(8#32),(0x2c028#32)] at ha
  rw [inv.collection.cursor] at ha
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl
  · simpa only [slot,BitVec.add_zero] using safe.1 r.collected.size cap (0#32) (by simp)
  · exact safe.1 r.collected.size cap (4#32) (by simp)
  · exact safe.1 r.collected.size cap (8#32) (by simp)
  · exact safe.2

theorem fresh (hi : i<n) (unseen : ¬OriginalLineCell.already (OriginalLineCell.header s.core).core) :
    OriginalLineDispatch.Fresh s.core := by
  have eq : OriginalLineCell.itemWord s.core=OriginalLineCell.itemWord (atIndex initial i) := by
    simp only [OriginalLineCell.itemWord,item initial n base resolve h i s r inv (by omega)]; rfl
  refine ⟨?_,unseen,?_,?_,?_⟩
  · rw [eq]; exact h.nonlast i hi
  · rw [inv.stack,inv.memory _ (h.fixedWords _ (by simp))]; exact h.target
  · rw [inv.stack]; exact (protection initial n base resolve h i s r inv hi _ (h.fixedWords _ (by simp))).1.1
  · unfold OriginalLineDispatch.stamp
    rw [pointer initial n base resolve h i s r inv (by omega),inv.stack]; exact h.stampSafe i hi

theorem argument (hi : i≤n) : (OriginalLineDispatch.view s.core).regs 0=
    (OriginalLineDispatch.view (atIndex initial i)).regs 0 :=
  (OriginalLineDispatch.entry_regs s.core).1.trans
    ((pointer initial n base resolve h i s r inv hi).trans (OriginalLineDispatch.entry_regs _).1.symm)

omit inv in
theorem geometry_read (hi : i<n) (a : Word) (ha : a∈OriginalLineSecondPoint.reads
    (h.candidates i).p (h.candidates i).v (h.candidates i).w) : a∈h.words :=
  h.reads i hi a (List.mem_append_left _ ha)

theorem reject_ready (hi : i<n) (unseen : ¬OriginalLineCell.already (OriginalLineCell.header s.core).core)
    (reject : (h.candidates i).crosses=false) : OriginalLineReject.Ready s.core
      (h.candidates i).trace (h.candidates i).line (h.candidates i).p (h.candidates i).v (h.candidates i).w := by
  refine ⟨fresh initial n base resolve h i s r inv hi unseen,?_,?_⟩
  · exact OriginalLineInvariant.reject_inputs _ _ _ _ _ _ _ (h.rejection i hi reject)
      (argument initial n base resolve h i s r inv (by omega)) (view_stack initial n base resolve h i s r inv)
      (fun a ha => inv.memory a (geometry_read initial n base resolve h i hi a ha))
  · intro a ha
    exact (protection initial n base resolve h i s r inv hi a (geometry_read initial n base resolve h i hi a ha)).1

theorem crossing_ready (hi : i<n) (unseen : ¬OriginalLineCell.already (OriginalLineCell.header s.core).core)
    (append : (h.candidates i).crosses=true) : OriginalLineDispatch.Ready s.core
      (h.candidates i).trace (h.candidates i).line (h.candidates i).frac (h.candidates i).flags
      (h.candidates i).p (h.candidates i).v (h.candidates i).w := by
  have old := h.crossing i hi append
  have reads := geometry_read initial n base resolve h i hi
  have active : (0x2c024#32)∈h.words := h.reads i hi _ (by simp [Candidate.reads])
  have back : (h.candidates i).p+(50#32)∈h.words := h.reads i hi _ (by simp [Candidate.reads])
  have cursor := metadata initial n base resolve h i s r inv hi
  have protect := protection initial n base resolve h i s r inv hi
  refine ⟨fresh initial n base resolve h i s r inv hi unseen,?_,?_,?_⟩
  · exact crossing_inputs _ _ _ _ _ _ _ old.geometry
      (argument initial n base resolve h i s r inv (by omega)) (view_stack initial n base resolve h i s r inv)
      (fun a ha => inv.memory a (reads a ha))
  · exact fun a ha => (protect a (reads a ha)).1
  · refine ⟨old.computed,?_,?_,?_,(protect _ active).2,(protect _ back).2,cursor.2,?_,?_⟩
    · intro a ha
      apply (protect a (reads a ?_)).2.2
      simp only [OriginalLineFraction.reads,List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp [OriginalLineSecondPoint.reads]
    · rw [inv.memory _ active]; exact old.active
    · rw [inv.memory _ back]; exact old.back
    · apply record_safe initial n base resolve h i s r inv hi
      change ArraySafe base ((OriginalLineDispatch.entry s.core).core.regs 4)
      rw [(OriginalLineDispatch.entry_regs _).2.2,inv.stack]
      exact h.stackArray _ (by simp)
    · intro a ha
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl
      · exact (protect _ active).1
      · exact (protect _ back).1
      · exact cursor.1

theorem saved_cursor (hi : i<n) : OriginalLineTail.RecordSafe (OriginalLineDispatch.view s.core)
    ((OriginalLineDispatch.view s.core).regs 4-(12#32)) := by
  apply record_safe initial n base resolve h i s r inv hi
  change ArraySafe base ((OriginalLineDispatch.entry s.core).core.regs 4-(12#32))
  rw [(OriginalLineDispatch.entry_regs _).2.2,inv.stack]
  have eq : initial.regs 4-(4#32)-(12#32)=initial.regs 4-(16#32) := by bv_decide
  rw [eq]; exact h.stackArray _ (by simp)


omit inv in
def step (c : Candidate) (s : X86Memory.State) (r : Collision.PathResult) : X86Control.State × Collision.PathResult :=
  if OriginalLineCell.already (OriginalLineCell.header s).core then (OriginalLineCell.visit s,r)
  else if c.crosses then (OriginalLineDispatch.result s,
    if c.frac.raw<0 then r else if c.early then {r with completed:=false} else {r with collected:=r.collected.push c.hit})
  else (OriginalLineReject.result s,r)

omit inv in
def run (candidates : Nat → Candidate) : Nat → Nat → X86Control.State → Collision.PathResult → X86Control.State × Collision.PathResult
  | 0,_,s,r => (s,r)
  | k+1,i,s,r => let next := step (candidates i) s.core r
    run candidates k (i+1) next.1 next.2

/-- Every branch re-establishes the full invariant. No reached-state geometry,
array encoding, capacity or separation premises are supplied by the caller. -/
theorem advance (hi : i<n)
    (keep : ¬OriginalLineCell.already (OriginalLineCell.header s.core).core →
      (h.candidates i).crosses=true → (h.candidates i).Continues) :
    let next := step (h.candidates i) s.core r
    Stable initial h (i+1) next.1 next.2 ∧
    (∃ steps≤281, X86Routine.Prefix program [] steps s next.1) ∧
    (∀ out k, OriginalLineTraversal.Runs next.1 out k → OriginalLineTraversal.Runs s out (k+1)) := by
  have last : OriginalLineCell.itemWord s.core≠(0xffffffff#32) := by
    have eq : OriginalLineCell.itemWord s.core=OriginalLineCell.itemWord (atIndex initial i) := by
      simp only [OriginalLineCell.itemWord,item initial n base resolve h i s r inv (by omega)]; rfl
    rw [eq]; exact h.nonlast i hi
  have cursor (t : X86Control.State) (eq : t.core.regs 2=s.core.regs 2+(2#32)) :
      t.core.regs 2=address initial (i+1) := by
    rw [eq,inv.cursor]
    simp only [address,OriginalLineInvariant.address,Nat.mul_add,BitVec.ofNat_add]
    bv_decide
  have collection := inv.collection
  rw [show n-i=n-(i+1)+1 by omega] at collection
  by_cases seen : OriginalLineCell.already (OriginalLineCell.header s.core).core
  · simp only [step,if_pos seen]
    have obs := OriginalLineCell.skip_observe s.core last seen
    have more := OriginalLineResume.skip_observe 1 s ⟨last,seen,trivial⟩
    simp only [OriginalLineResume.skipMany] at more
    obtain ⟨a,ha,path⟩ := OriginalLineResume.skip_execution 1 s inv.pc ⟨last,seen,trivial⟩
    refine ⟨⟨obs.2.2,cursor _ obs.2.1,more.2.2.trans inv.stack,?_,
      OriginalLineCollection.duplicate s.core base resolve r.collected _ collection last seen⟩,
      ⟨a,by omega,path.transfer program [] E1M1LineResume.contains_resume (by simp)⟩,?_⟩
    · intro a ha; rw [obs.1]; exact inv.memory a ha
    · intro out k tail; exact .duplicate s out k inv.pc last seen tail
  · by_cases app : (h.candidates i).crosses=true
    · simp only [step,if_neg seen,if_pos app]
      have ready := crossing_ready initial n base resolve h i s r inv hi seen app
      have facts := h.crossing i hi app
      have saved := saved_cursor initial n base resolve h i s r inv hi
      have continues := keep seen app
      have obs := OriginalLineDispatch.continued _ _ _ _ _ _ _ _ ready saved continues
      obtain ⟨a,ha,path⟩ := OriginalLineDispatch.execution _ _ _ _ _ _ _ _ ready s.flags
      rw [OriginalPathXStep.at_pc _ _ inv.pc] at path
      have preserved : ∀ a∈h.words, load32 (OriginalLineDispatch.result s.core).core.memory a=load32 initial.memory a := by
        intro a ha
        have safe := protection initial n base resolve h i s r inv hi a ha
        exact (OriginalLineDispatch.frame _ _ _ _ _ _ _ _ ready a safe.1
          ⟨safe.2.1,safe.2.2,record_safe initial n base resolve h i s r inv hi a (h.arrayWords a ha)⟩).trans (inv.memory a ha)
      have lift : ∀ out k, OriginalLineTraversal.Runs (OriginalLineDispatch.result s.core) out k → OriginalLineTraversal.Runs s out (k+1) :=
        fun out k tail => .crossing s out k inv.pc _ _ _ _ _ _ _ ready saved continues tail
      by_cases neg : (h.candidates i).frac.raw<0
      · simp only [if_pos neg]
        exact ⟨⟨obs.1,cursor _ obs.2.1,obs.2.2.trans inv.stack,preserved,
          OriginalLineNoInsert.collection _ _ _ _ _ _ _ _ ready (Or.inl neg) base resolve r.collected _ collection
            (storage initial n base resolve h i s r inv hi)⟩,⟨a,ha,path⟩,lift⟩
      · have clear : (h.candidates i).early=false := continues.resolve_left neg
        simp only [if_neg neg,clear,Bool.false_eq_true,if_false]
        exact ⟨⟨obs.1,cursor _ obs.2.1,obs.2.2.trans inv.stack,preserved,
          (OriginalLineCollection.append _ _ _ _ _ _ _ _ ready r (h.candidates i).id base resolve _
            collection (storage initial n base resolve h i s r inv hi) neg clear (h.pointer i hi app)).2⟩,⟨a,ha,path⟩,lift⟩
    · have reject : (h.candidates i).crosses=false := by cases eq : (h.candidates i).crosses <;> simp_all
      simp only [step,if_neg seen,if_neg app]
      have ready := reject_ready initial n base resolve h i s r inv hi seen reject
      have obs := OriginalLineReject.continued _ _ _ _ _ _ ready
      obtain ⟨a,ha,path⟩ := OriginalLineReject.execution _ _ _ _ _ _ ready s.flags
      rw [OriginalPathXStep.at_pc _ _ inv.pc] at path
      refine ⟨⟨obs.1,cursor _ obs.2.1,obs.2.2.1.trans inv.stack,?_,?_⟩,⟨a,by omega,path⟩,?_⟩
      · intro a ha
        have safe := protection initial n base resolve h i s r inv hi a ha
        exact (OriginalLineReject.frame _ _ _ _ _ _ ready a safe.1 safe.2.1).trans (inv.memory a ha)
      · have cursorProtection := metadata initial n base resolve h i s r inv hi
        exact OriginalLineCollection.rejected _ _ _ _ _ _ ready base resolve r.collected _ collection
          (storage initial n base resolve h i s r inv hi) ⟨cursorProtection.1,cursorProtection.2.1⟩
      · intro out k tail; exact .rejected s out k inv.pc _ _ _ _ _ ready tail

theorem walk (k : Nat) (hi : i+k≤n)
    (keep : ∀ j, i≤j → j<i+k → (h.candidates j).crosses=true → (h.candidates j).Continues) :
    let final := run h.candidates k i s r
    Stable initial h (i+k) final.1 final.2 ∧
    (∃ steps≤281*k, X86Routine.Prefix program [] steps s final.1) ∧
    (∀ out m, OriginalLineTraversal.Runs final.1 out m → OriginalLineTraversal.Runs s out (k+m)) := by
  induction k generalizing i s r with
  | zero => exact ⟨inv,⟨0,by omega,.nil s⟩,fun _ _ tail => by simpa only [run,Nat.zero_add] using tail⟩
  | succ k ih =>
    obtain ⟨next,⟨a,ha,path⟩,lift⟩ := advance initial n base resolve h i s r inv (by omega) (fun _ app => keep i (by omega) (by omega) app)
    obtain ⟨final,⟨b,hb,rest⟩,liftRest⟩ := ih (i+1) (step (h.candidates i) s.core r).1 (step (h.candidates i) s.core r).2 next (by omega) (fun j lo hi => keep j (by omega) (by omega))
    refine ⟨?_,⟨a+b,by omega,OriginalGroupBounds.prefix_join path rest⟩,?_⟩
    · simpa only [run,show i+1+k=i+(k+1) by omega] using final
    · intro out m tail
      have all := lift out (k+m) (liftRest out m tail)
      simpa only [show k+m+1=k+1+m by omega] using all

omit inv in
theorem start (f : Option Flags) (collected : Tracks initial base resolve r.collected n) :
    Stable initial h 0 ⟨initial,f,0x2c57f⟩ r :=
  ⟨rfl,by simp [address,OriginalLineInvariant.address],rfl,fun _ _ => rfl,collected⟩

omit inv in
def finished (initial : X86Memory.State) (n : Nat) (base : Word) (resolve : Collision.Intercept → Word)
    (h : Initial initial n base resolve) (f : Option Flags) (r : Collision.PathResult) : X86Control.State × Collision.PathResult :=
  let final := run h.candidates n 0 ⟨initial,f,0x2c57f⟩ r
  (OriginalLineBounds.returned (OriginalLineCell.header final.1.core).core,final.2)

omit inv in
/-- One initial contract now establishes the entire continuing mixed scan and
its sentinel return, including the final ordered collection and protected memory. -/
theorem through_sentinel (f : Option Flags) (collected : Tracks initial base resolve r.collected n)
    (keep : ∀ j<n, (h.candidates j).crosses=true → (h.candidates j).Continues)
    (sentinel : load16 initial.memory (address initial n)=(0xffff#16)) :
    let out := finished initial n base resolve h f r
    (∃ steps≤281*n+7, X86Routine.Prefix program [] steps ⟨initial,f,0x2c57f⟩ out.1) ∧
    OriginalLineTraversal.Runs ⟨initial,f,0x2c57f⟩ out.1 n ∧
    Tracks out.1.core base resolve out.2.collected 0 ∧
    (∀ a∈h.words, load32 out.1.core.memory a=load32 initial.memory a) := by
  obtain ⟨inv,⟨a,ha,path⟩,lift⟩ := walk initial n base resolve h 0 ⟨initial,f,0x2c57f⟩ r
    (start initial n base resolve h r f collected) n (by omega) (fun j _ hj => keep j (by omega))
  simp only [Nat.zero_add] at inv
  have last : OriginalLineCell.item (run h.candidates n 0 ⟨initial,f,0x2c57f⟩ r).1.core=(0xffff#16) :=
    (item initial n base resolve h n _ _ inv (by omega)).trans sentinel
  have tail := OriginalLineResume.sentinel_execution _ (run h.candidates n 0 ⟨initial,f,0x2c57f⟩ r).1.flags last
  rw [OriginalPathXStep.at_pc _ _ inv.pc] at tail
  refine ⟨⟨a+7,by omega,OriginalGroupBounds.prefix_join path
    (tail.transfer program [] E1M1LineResume.contains_resume (by simp))⟩,
    lift _ 0 (.sentinel _ inv.pc last),?_,inv.memory⟩
  have tracked := inv.collection
  simp only [Nat.sub_self] at tracked
  exact ⟨tracked.encoded,tracked.cursor,tracked.room⟩

omit inv in
theorem parent_return (f : Option Flags) (collected : Tracks initial base resolve r.collected n)
    (keep : ∀ j<n, (h.candidates j).crosses=true → (h.candidates j).Continues)
    (saved : initial.regs 4+(4#32)∈h.words) (ret : initial.regs 4+(8#32)∈h.words) :
    let out := (finished initial n base resolve h f r).1
    out.core.regs 0=(1#32) ∧ out.core.regs 4=initial.regs 4+(12#32) ∧
    out.core.regs 7=load32 initial.memory (initial.regs 4+(4#32)) ∧
    out.pc=(load32 initial.memory (initial.regs 4+(8#32))).toNat := by
  have inv := (walk initial n base resolve h 0 ⟨initial,f,0x2c57f⟩ r
    (start initial n base resolve h r f collected) n (by omega) (fun j _ hj => keep j (by omega))).1
  simp only [finished,OriginalLineBounds.returned,OriginalLineBounds.r3,OriginalLineBounds.r2,
    OriginalLineBounds.r1,OriginalLineCell.header,OriginalLineCell.h1,put,write]
  simp [inv.stack,inv.memory _ saved,inv.memory _ ret]

end Doom.Proofs.OriginalLineMixedInvariant
