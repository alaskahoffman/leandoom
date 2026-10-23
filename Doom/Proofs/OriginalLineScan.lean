import Doom.Proofs.OriginalLineMixedInvariant
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.OriginalLineScan
open Verification X86 X86Memory X86Control BlockSummary
open OriginalLineCollection (Tracks)
open OriginalLineMixedInvariant

abbrev Halts (c : Candidate) (s : X86Memory.State) : Prop :=
  ¬OriginalLineCell.already (OriginalLineCell.header s).core ∧ c.crosses=true ∧
    ¬c.frac.raw<0 ∧ c.early=true

structure Result where
  machine : X86Control.State
  path : Collision.PathResult
  visits : Nat
  stopped : Bool

/-- A stop is terminal: the recursive suffix is not evaluated. Exhausting the
candidate prefix is distinct from returning through a sentinel. -/
def scan (candidates : Nat → Candidate) : Nat → Nat → X86Control.State → Collision.PathResult → Result
  | 0,_,s,r => ⟨s,r,0,false⟩
  | k+1,i,s,r =>
    let next := step (candidates i) s.core r
    if Halts (candidates i) s.core then ⟨next.1,next.2,1,true⟩
    else let rest := scan candidates k (i+1) next.1 next.2
      {rest with visits:=rest.visits+1}

structure Terminal (initial : X86Memory.State) {n : Nat} {base : Word} {resolve : Collision.Intercept → Word}
    (h : Initial initial n base resolve) (i : Nat) (s : X86Control.State) (r : Collision.PathResult) : Prop where
  value : s.core.regs 0=(0#32)
  stack : s.core.regs 4=initial.regs 4+(12#32)
  saved : s.core.regs 7=load32 s.core.memory (initial.regs 4+(4#32))
  returned : s.pc=(load32 s.core.memory (initial.regs 4+(8#32))).toNat
  memory : ∀ a∈h.words, load32 s.core.memory a=load32 initial.memory a
  collection : Tracks s.core base resolve r.collected (n-i)
  completed : r.completed=false

variable (initial : X86Memory.State) (n : Nat) (base : Word) (resolve : Collision.Intercept → Word)
  (h : Initial initial n base resolve) (i : Nat) (s : X86Control.State) (r : Collision.PathResult)
  (inv : Stable initial h i s r)
include inv

theorem stopped_step (hi : i<n) (halt : Halts (h.candidates i) s.core) :
    let next := step (h.candidates i) s.core r
    Terminal initial h (i+1) next.1 next.2 ∧
    OriginalLineTraversal.Runs s next.1 1 ∧
    (∃ steps≤281, X86Routine.Prefix program [] steps s next.1) := by
  obtain ⟨unseen,crossed,nonnegative,early⟩ := halt
  have ready := crossing_ready initial n base resolve h i s r inv hi unseen crossed
  have stop : OriginalLineStop.Stops (h.candidates i).frac (h.candidates i).flags (h.candidates i).line := ⟨nonnegative,early⟩
  have obs := OriginalLineStop.observed _ _ _ _ _ _ _ _ ready stop
  have tracked := inv.collection
  rw [show n-i=n-(i+1)+1 by omega] at tracked
  obtain ⟨a,ha,path⟩ := OriginalLineDispatch.execution _ _ _ _ _ _ _ _ ready s.flags
  rw [OriginalPathXStep.at_pc _ _ inv.pc] at path
  simp only [step,if_neg unseen,if_pos crossed,if_neg nonnegative,early,ite_true]
  refine ⟨⟨obs.1,obs.2.1.trans (congrArg (fun x : Word => x+(12#32)) inv.stack),?_,?_,?_,?_,rfl⟩,
    .stopped s inv.pc _ _ _ _ _ _ _ ready stop,⟨a,ha,path⟩⟩
  · simpa only [inv.stack] using obs.2.2.1
  · simpa only [inv.stack] using obs.2.2.2
  · intro a ha
    have safe := protection initial n base resolve h i s r inv hi a ha
    exact (OriginalLineNoInsert.frame _ _ _ _ _ _ _ _ ready (Or.inr stop) a safe.1 safe.2.1 safe.2.2).trans (inv.memory a ha)
  · exact OriginalLineNoInsert.collection _ _ _ _ _ _ _ _ ready (Or.inr stop) base resolve r.collected _ tracked
      (storage initial n base resolve h i s r inv hi)

/-- All callback outcomes close under the same initial-memory invariant. A
stopped prefix has an actual returned execution; a continuing prefix can be
composed with any admitted suffix. No sentinel is needed for this theorem. -/
theorem scan_correct (k : Nat) (hi : i+k≤n) :
    let out := scan h.candidates k i s r
    out.visits≤k ∧
    (∃ steps≤281*out.visits, X86Routine.Prefix program [] steps s out.machine) ∧
    (if out.stopped then
      Terminal initial h (i+out.visits) out.machine out.path ∧ OriginalLineTraversal.Runs s out.machine out.visits
    else out.visits=k ∧ Stable initial h (i+k) out.machine out.path ∧
      ∀ final m, OriginalLineTraversal.Runs out.machine final m → OriginalLineTraversal.Runs s final (out.visits+m)) := by
  induction k generalizing i s r with
  | zero =>
    simp only [scan,Bool.false_eq_true,if_false,Nat.add_zero]
    exact ⟨by omega,⟨0,by omega,.nil s⟩,trivial,inv,fun _ _ tail => by simpa using tail⟩
  | succ k ih =>
    by_cases halt : Halts (h.candidates i) s.core
    · simp only [scan,if_pos halt]
      obtain ⟨term,runs,path⟩ := stopped_step initial n base resolve h i s r inv (by omega) halt
      exact ⟨by omega,path,term,runs⟩
    · have keep : ¬OriginalLineCell.already (OriginalLineCell.header s.core).core →
          (h.candidates i).crosses=true → (h.candidates i).Continues := by
        intro unseen crossed
        by_cases neg : (h.candidates i).frac.raw<0
        · exact Or.inl neg
        · right
          cases eq : (h.candidates i).early
          · rfl
          · exact False.elim (halt ⟨unseen,crossed,neg,eq⟩)
      obtain ⟨next,⟨a,ha,path⟩,lift⟩ := advance initial n base resolve h i s r inv (by omega) keep
      have rest := ih (i+1) (step (h.candidates i) s.core r).1 (step (h.candidates i) s.core r).2 next (by omega)
      obtain ⟨bound,⟨b,hb,restpath⟩,result⟩ := rest
      simp only [scan,if_neg halt]
      refine ⟨by omega,⟨a+b,by omega,OriginalGroupBounds.prefix_join path restpath⟩,?_⟩
      by_cases done : (scan h.candidates k (i+1) (step (h.candidates i) s.core r).1 (step (h.candidates i) s.core r).2).stopped=true
      · simp only [done,if_true] at result ⊢
        exact ⟨by simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using result.1,
          lift _ _ result.2⟩
      · simp only [done] at result ⊢
        obtain ⟨count,stable,tail⟩ := result
        refine ⟨by omega,?_,?_⟩
        · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using stable
        · intro final m suffix
          have joined := lift final _ (tail final m suffix)
          simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using joined

omit inv in
/-- A dynamically stopped prefix needs no sentinel or suffix contract. -/
theorem stopping_prefix (f : Option Flags) (collected : Tracks initial base resolve r.collected n)
    (halt : (scan h.candidates n 0 ⟨initial,f,0x2c57f⟩ r).stopped=true) :
    let out := scan h.candidates n 0 ⟨initial,f,0x2c57f⟩ r
    out.visits≤n ∧
    (∃ steps≤281*out.visits, X86Routine.Prefix program [] steps ⟨initial,f,0x2c57f⟩ out.machine) ∧
    Terminal initial h out.visits out.machine out.path ∧
    OriginalLineTraversal.Runs ⟨initial,f,0x2c57f⟩ out.machine out.visits := by
  have checked := scan_correct initial n base resolve h 0 ⟨initial,f,0x2c57f⟩ r
    (start initial n base resolve h r f collected) n (by omega)
  simpa only [halt,if_true,Nat.zero_add] using checked

omit inv in
def complete (candidates : Nat → Candidate) (n : Nat) (s : X86Control.State) (r : Collision.PathResult) : Result :=
  let out := scan candidates n 0 s r
  if out.stopped then out
  else {out with machine:=OriginalLineBounds.returned (OriginalLineCell.header out.machine.core).core}

omit inv in
/-- A sentinel is used only when the entire candidate prefix continues. All
crossing outcomes are selected dynamically; none needs a reached-state contract. -/
theorem through_scan (f : Option Flags) (collected : Tracks initial base resolve r.collected n)
    (sentinel : load16 initial.memory (address initial n)=(0xffff#16)) :
    let out := complete h.candidates n ⟨initial,f,0x2c57f⟩ r
    out.visits≤n ∧
    (∃ steps≤281*n+7, X86Routine.Prefix program [] steps ⟨initial,f,0x2c57f⟩ out.machine) ∧
    OriginalLineTraversal.Runs ⟨initial,f,0x2c57f⟩ out.machine out.visits ∧
    Tracks out.machine.core base resolve out.path.collected (n-out.visits) ∧
    (∀ a∈h.words, load32 out.machine.core.memory a=load32 initial.memory a) ∧
    out.machine.core.regs 0=(if out.stopped then (0#32) else (1#32)) ∧
    out.machine.core.regs 4=initial.regs 4+(12#32) := by
  obtain ⟨bound,⟨a,ha,path⟩,result⟩ := scan_correct initial n base resolve h 0 ⟨initial,f,0x2c57f⟩ r
    (start initial n base resolve h r f collected) n (by omega)
  simp only [Nat.zero_add] at result
  by_cases stopped : (scan h.candidates n 0 ⟨initial,f,0x2c57f⟩ r).stopped=true
  · simp only [stopped,if_true] at result
    simp only [complete,stopped,if_true]
    exact ⟨bound,⟨a,by omega,path⟩,result.2,result.1.collection,result.1.memory,result.1.value,result.1.stack⟩
  · simp only [stopped,Bool.false_eq_true,if_false] at result
    obtain ⟨count,stable,lift⟩ := result
    have last : OriginalLineCell.item (scan h.candidates n 0 ⟨initial,f,0x2c57f⟩ r).machine.core=(0xffff#16) :=
      (item initial n base resolve h n _ _ stable (by omega)).trans sentinel
    have tail := OriginalLineResume.sentinel_execution _ (scan h.candidates n 0 ⟨initial,f,0x2c57f⟩ r).machine.flags last
    rw [OriginalPathXStep.at_pc _ _ stable.pc] at tail
    have runs := lift _ 0 (.sentinel _ stable.pc last)
    have tracked := stable.collection
    simp only [complete,stopped,Bool.false_eq_true,if_false]
    refine ⟨bound,⟨a+7,by omega,OriginalGroupBounds.prefix_join path
      (tail.transfer program [] E1M1LineResume.contains_resume (by simp))⟩,?_,?_,stable.memory,?_,?_⟩
    · simpa only [Nat.add_zero] using runs
    · rw [count]
      exact ⟨tracked.encoded,tracked.cursor,tracked.room⟩
    · simp [OriginalLineBounds.returned,OriginalLineBounds.r3,OriginalLineBounds.r2,OriginalLineBounds.r1,put,write]
    · simp [OriginalLineBounds.returned,OriginalLineBounds.r3,OriginalLineBounds.r2,OriginalLineBounds.r1,
        OriginalLineCell.header,OriginalLineCell.h1,put,write,stable.stack]

omit inv in
/-- Protected parent-frame words also identify the concrete early return. -/
theorem stopped_parent (out : X86Control.State) (path : Collision.PathResult) (visits : Nat)
    (term : Terminal initial h visits out path)
    (saved : initial.regs 4+(4#32)∈h.words) (ret : initial.regs 4+(8#32)∈h.words) :
    out.core.regs 7=load32 initial.memory (initial.regs 4+(4#32)) ∧
    out.pc=(load32 initial.memory (initial.regs 4+(8#32))).toNat := by
  exact ⟨term.saved.trans (term.memory _ saved),term.returned.trans (congrArg BitVec.toNat (term.memory _ ret))⟩

end Doom.Proofs.OriginalLineScan
