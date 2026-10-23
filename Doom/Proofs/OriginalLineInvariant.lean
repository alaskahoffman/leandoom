import Doom.Proofs.OriginalLineTraversal
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.OriginalLineInvariant
open Verification X86 X86Memory X86Control BlockSummary
abbrev program := OriginalLineTraversal.program

/-- Geometry transport only needs the actual read footprint, argument and SP.
It is independent of how earlier entries changed visited stamps. -/
theorem reject_inputs (s t : X86Memory.State) (trace : Collision.Divline)
    (line : Collision.Line) (p v w : Word) (h : OriginalLineReject.Inputs s trace line p v w)
    (arg : t.regs 0=s.regs 0) (sp : t.regs 4=s.regs 4)
    (memory : ∀ a∈OriginalLineSecondPoint.reads p v w, load32 t.memory a=load32 s.memory a) :
    OriginalLineReject.Inputs t trace line p v w := by
  refine ⟨?_,?_,h.same⟩
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

def address (s : X86Memory.State) (i : Nat) : Word := s.regs 2+BitVec.ofNat 32 (2*i)
def atIndex (s : X86Memory.State) (i : Nat) := put s 2 (address s i)

/-- A contract entirely over the initial list image. Every non-sentinel entry
is geometrically rejected if fresh. `words` protects geometry, list words and
fixed globals, but need not protect mutable visited stamps. -/
structure Initial (s : X86Memory.State) (n : Nat) where
  words : List Word
  listWords : ∀ i≤n, address s i∈words
  fixedWords : ∀ a∈[s.regs 4,(0x13580#32),0x2c120], a∈words
  target : load32 s.memory (s.regs 4)=(0x2c5f0#32)
  nonlast : ∀ i<n, OriginalLineCell.itemWord (atIndex s i)≠(0xffffffff#32)
  last : load16 s.memory (address s n)=(0xffff#16)
  geometry : ∀ i<n, ∃ (trace : Collision.Divline) (line : Collision.Line) (p v w : Word),
    OriginalLineReject.Inputs (OriginalLineDispatch.view (atIndex s i)) trace line p v w ∧
    (∀ a∈OriginalLineSecondPoint.reads p v w, a∈words)
  separated : ∀ i<n, ∀ a∈words,
    OriginalLineDispatch.Safe (atIndex s i) a ∧
    OriginalLineCrossing.SideSafe (OriginalLineDispatch.view (atIndex s i)) a
  stampSafe : ∀ i<n, Apart (OriginalLineDispatch.stamp (atIndex s i)) (s.regs 4-(4#32))

/-- The invariant has no claim about the stamp contents. Branch selection reads
current memory on every iteration. -/
structure Stable (initial : X86Memory.State) {n : Nat} (h : Initial initial n)
    (i : Nat) (s : X86Control.State) : Prop where
  pc : s.pc=0x2c57f
  cursor : s.core.regs 2=address initial i
  stack : s.core.regs 4=initial.regs 4
  memory : ∀ a∈h.words, load32 s.core.memory a=load32 initial.memory a

theorem start (s : X86Memory.State) (n : Nat) (h : Initial s n) (f : Option Flags) :
    Stable s h 0 ⟨s,f,0x2c57f⟩ := ⟨rfl,by simp [address],rfl,fun _ _ => rfl⟩

theorem item (initial : X86Memory.State) (n : Nat) (h : Initial initial n)
    (i : Nat) (s : X86Control.State) (inv : Stable initial h i s) (hi : i≤n) :
    OriginalLineCell.item s.core=load16 initial.memory (address initial i) := by
  have half := congrArg (fun x : Word => x.extractLsb' 0 16) (inv.memory _ (h.listWords i hi))
  rw [SectorDispatch.load_half,SectorDispatch.load_half] at half
  simpa only [OriginalLineCell.item,inv.cursor] using half

theorem pointer (initial : X86Memory.State) (n : Nat) (h : Initial initial n)
    (i : Nat) (s : X86Control.State) (inv : Stable initial h i s) (hi : i≤n) :
    OriginalLineDispatch.pointer s.core=OriginalLineDispatch.pointer (atIndex initial i) := by
  simp only [OriginalLineDispatch.pointer,OriginalLineCell.itemWord,item initial n h i s inv hi]
  rw [inv.memory _ (h.fixedWords _ (by simp))]
  rfl

theorem view_stack (initial : X86Memory.State) (n : Nat) (h : Initial initial n)
    (i : Nat) (s : X86Control.State) (inv : Stable initial h i s) :
    (OriginalLineDispatch.view s.core).regs 4=
      (OriginalLineDispatch.view (atIndex initial i)).regs 4 := by
  change (OriginalLineDispatch.entry s.core).core.regs 4=(OriginalLineDispatch.entry (atIndex initial i)).core.regs 4
  rw [(OriginalLineDispatch.entry_regs _).2.2,(OriginalLineDispatch.entry_regs _).2.2,inv.stack]
  rfl

theorem protection (initial : X86Memory.State) (n : Nat) (h : Initial initial n)
    (i : Nat) (s : X86Control.State) (inv : Stable initial h i s) (hi : i<n)
    (a : Word) (ha : a∈h.words) :
    OriginalLineDispatch.Safe s.core a ∧ OriginalLineCrossing.SideSafe (OriginalLineDispatch.view s.core) a := by
  obtain ⟨dispatch,side⟩ := h.separated i hi a ha
  constructor
  · unfold OriginalLineDispatch.Safe OriginalLineDispatch.stamp
    rw [pointer initial n h i s inv (by omega),inv.stack]
    exact dispatch
  · unfold OriginalLineCrossing.SideSafe
    rw [view_stack initial n h i s inv]
    exact side

/-- All fresh-entry premises now follow from initial data plus the invariant;
no geometry or callback target is re-assumed at this reached state. -/
theorem ready (initial : X86Memory.State) (n : Nat) (h : Initial initial n)
    (i : Nat) (s : X86Control.State) (inv : Stable initial h i s) (hi : i<n)
    (unseen : ¬OriginalLineCell.already (OriginalLineCell.header s.core).core) :
    ∃ (trace : Collision.Divline) (line : Collision.Line) (p v w : Word),
      OriginalLineReject.Ready s.core trace line p v w := by
  obtain ⟨trace,line,p,v,w,geometry,reads⟩ := h.geometry i hi
  have ptr := pointer initial n h i s inv (by omega)
  have sp := view_stack initial n h i s inv
  have last : OriginalLineCell.itemWord s.core=OriginalLineCell.itemWord (atIndex initial i) := by
    simp only [OriginalLineCell.itemWord,item initial n h i s inv (by omega)]
    rfl
  refine ⟨trace,line,p,v,w,⟨?_,?_,?_⟩⟩
  · refine ⟨?_,unseen,?_,?_,?_⟩
    · rw [last]; exact h.nonlast i hi
    · rw [inv.stack,inv.memory _ (h.fixedWords _ (by simp))]; exact h.target
    · rw [inv.stack]; exact (protection initial n h i s inv hi _ (h.fixedWords _ (by simp))).1.1
    · unfold OriginalLineDispatch.stamp
      rw [ptr,inv.stack]; exact h.stampSafe i hi
  · refine reject_inputs (OriginalLineDispatch.view (atIndex initial i)) (OriginalLineDispatch.view s.core)
      trace line p v w geometry ?_ sp ?_
    · exact (OriginalLineDispatch.entry_regs s.core).1.trans (ptr.trans (OriginalLineDispatch.entry_regs _).1.symm)
    · intro a ha
      exact inv.memory a (reads a ha)
  · intro a ha
    exact (protection initial n h i s inv hi a (reads a ha)).1

def step (s : X86Memory.State) : X86Control.State :=
  if OriginalLineCell.already (OriginalLineCell.header s).core then OriginalLineCell.visit s
  else OriginalLineReject.result s

def run : Nat → X86Control.State → X86Control.State
  | 0,s => s
  | k+1,s => run k (step s.core)

/-- Establish preservation using the real duplicate or rejection execution. -/
theorem advance (initial : X86Memory.State) (n : Nat) (h : Initial initial n)
    (i : Nat) (s : X86Control.State) (inv : Stable initial h i s) (hi : i<n) :
    Stable initial h (i+1) (step s.core) ∧
    (∃ steps≤178, X86Routine.Prefix program [] steps s (step s.core)) ∧
    (∀ out k, OriginalLineTraversal.Runs (step s.core) out k → OriginalLineTraversal.Runs s out (k+1)) := by
  have last : OriginalLineCell.itemWord s.core≠(0xffffffff#32) := by
    have eq : OriginalLineCell.itemWord s.core=OriginalLineCell.itemWord (atIndex initial i) := by
      simp only [OriginalLineCell.itemWord,item initial n h i s inv (by omega)]; rfl
    rw [eq]; exact h.nonlast i hi
  have cursor (t : X86Control.State) (eq : t.core.regs 2=s.core.regs 2+(2#32)) :
      t.core.regs 2=address initial (i+1) := by
    rw [eq,inv.cursor]
    simp only [address,Nat.mul_add,BitVec.ofNat_add]
    bv_decide
  by_cases seen : OriginalLineCell.already (OriginalLineCell.header s.core).core
  · have eq : step s.core=OriginalLineCell.visit s.core := if_pos seen
    rw [eq]
    have obs := OriginalLineCell.skip_observe s.core last seen
    have more := OriginalLineResume.skip_observe 1 s ⟨last,seen,trivial⟩
    simp only [OriginalLineResume.skipMany] at more
    obtain ⟨a,ha,path⟩ := OriginalLineResume.skip_execution 1 s inv.pc ⟨last,seen,trivial⟩
    refine ⟨⟨obs.2.2,cursor _ obs.2.1,more.2.2.trans inv.stack,?_⟩,
      ⟨a,by omega,path.transfer program [] E1M1LineResume.contains_resume (by simp)⟩,?_⟩
    · intro a ha; rw [obs.1]; exact inv.memory a ha
    · intro out k tail; exact .duplicate s out k inv.pc last seen tail
  · have eq : step s.core=OriginalLineReject.result s.core := if_neg seen
    rw [eq]
    obtain ⟨trace,line,p,v,w,inputs⟩ := ready initial n h i s inv hi seen
    have obs := OriginalLineReject.continued s.core trace line p v w inputs
    obtain ⟨a,ha,path⟩ := OriginalLineReject.execution s.core trace line p v w inputs s.flags
    rw [OriginalPathXStep.at_pc _ _ inv.pc] at path
    refine ⟨⟨obs.1,cursor _ obs.2.1,obs.2.2.1.trans inv.stack,?_⟩,⟨a,ha,path⟩,?_⟩
    · intro a ha
      obtain ⟨dispatch,side⟩ := protection initial n h i s inv hi a ha
      exact (OriginalLineReject.frame s.core trace line p v w inputs a dispatch side).trans (inv.memory a ha)
    · intro out k tail; exact .rejected s out k inv.pc trace line p v w inputs tail

theorem walk (initial : X86Memory.State) (n : Nat) (h : Initial initial n)
    (k i : Nat) (s : X86Control.State) (inv : Stable initial h i s) (hi : i+k≤n) :
    Stable initial h (i+k) (run k s) ∧
    (∃ steps≤178*k, X86Routine.Prefix program [] steps s (run k s)) ∧
    (∀ out m, OriginalLineTraversal.Runs (run k s) out m → OriginalLineTraversal.Runs s out (k+m)) := by
  induction k generalizing i s with
  | zero => exact ⟨inv,⟨0,by omega,.nil s⟩,fun _ _ tail => by simpa only [run,Nat.zero_add] using tail⟩
  | succ k ih =>
    obtain ⟨next,⟨a,ha,path⟩,lift⟩ := advance initial n h i s inv (by omega)
    obtain ⟨final,⟨b,hb,rest⟩,liftRest⟩ := ih (i+1) (step s.core) next (by omega)
    refine ⟨?_,⟨a+b,by omega,OriginalGroupBounds.prefix_join path rest⟩,?_⟩
    · simpa only [run,show i+1+k=i+(k+1) by omega] using final
    · intro out m tail
      have all := lift out (k+m) (liftRest out m tail)
      simpa only [show k+m+1=k+1+m by omega] using all

def finished (n : Nat) (s : X86Control.State) :=
  OriginalLineBounds.returned (OriginalLineCell.header (run n s).core).core

/-- The sentinel is derived from initial list memory, not postulated at the end. -/
theorem through_sentinel (s : X86Memory.State) (n : Nat) (h : Initial s n) (f : Option Flags) :
    (∃ steps≤178*n+7, X86Routine.Prefix program [] steps ⟨s,f,0x2c57f⟩ (finished n ⟨s,f,0x2c57f⟩)) ∧
    OriginalLineTraversal.Runs ⟨s,f,0x2c57f⟩ (finished n ⟨s,f,0x2c57f⟩) n := by
  obtain ⟨inv,⟨a,ha,path⟩,lift⟩ := walk s n h n 0 ⟨s,f,0x2c57f⟩ (start s n h f) (by omega)
  simp only [Nat.zero_add] at inv
  have last : OriginalLineCell.item (run n ⟨s,f,0x2c57f⟩).core=(0xffff#16) :=
    (item s n h n _ inv (by omega)).trans h.last
  have tail := OriginalLineResume.sentinel_execution _ (run n ⟨s,f,0x2c57f⟩).flags last
  rw [OriginalPathXStep.at_pc _ _ inv.pc] at tail
  exact ⟨⟨a+7,by omega,OriginalGroupBounds.prefix_join path
    (tail.transfer program [] E1M1LineResume.contains_resume (by simp))⟩,
    lift _ 0 (.sentinel _ inv.pc last)⟩

/-- Every protected initial word survives the entire scan and sentinel return. -/
theorem frame (s : X86Memory.State) (n : Nat) (h : Initial s n) (f : Option Flags)
    (a : Word) (ha : a∈h.words) :
    load32 (finished n ⟨s,f,0x2c57f⟩).core.memory a=load32 s.memory a := by
  have inv := (walk s n h n 0 ⟨s,f,0x2c57f⟩ (start s n h f) (by omega)).1
  exact inv.memory a ha

/-- Parent-frame preservation is checked once against the initial layout. -/
theorem parent_return (s : X86Memory.State) (n : Nat) (h : Initial s n) (f : Option Flags)
    (saved : s.regs 4+(4#32)∈h.words) (ret : s.regs 4+(8#32)∈h.words) :
    (finished n ⟨s,f,0x2c57f⟩).core.regs 0=(1#32) ∧
    (finished n ⟨s,f,0x2c57f⟩).core.regs 4=s.regs 4+(12#32) ∧
    (finished n ⟨s,f,0x2c57f⟩).core.regs 7=load32 s.memory (s.regs 4+(4#32)) ∧
    (finished n ⟨s,f,0x2c57f⟩).pc=(load32 s.memory (s.regs 4+(8#32))).toNat := by
  have inv := (walk s n h n 0 ⟨s,f,0x2c57f⟩ (start s n h f) (by omega)).1
  simp only [finished,OriginalLineBounds.returned,OriginalLineBounds.r3,
    OriginalLineBounds.r2,OriginalLineBounds.r1,OriginalLineCell.header,OriginalLineCell.h1,put,write]
  simp [inv.stack,inv.memory _ saved,inv.memory _ ret]

end Doom.Proofs.OriginalLineInvariant
