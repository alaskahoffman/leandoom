import Doom.Proofs.E1M1ScanMemory
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.OriginalLineVisits
open Verification X86 X86Memory X86Control BlockSummary
open OriginalLineMixedInvariant

def stamp (lines : Word) (id : Nat) : Word := BitVec.ofNat 32 id*62+lines+54

/-- The original 62-byte line stride keeps distinct stamp words disjoint,
even when the line-array base wraps around the address space. -/
theorem stamps_apart (lines : Word) (i j : Nat) (hi : i<32768) (hj : j<32768) (ne : i≠j) :
    Apart (stamp lines i) (stamp lines j) := by
  intro x y eq
  have normalized : BitVec.ofNat 32 (62*i+x.val)=BitVec.ofNat 32 (62*j+y.val) := by
    have cancel (k : Nat) (z : Fin 4) : stamp lines k+BitVec.ofNat 32 z.val-(lines+54)=
        BitVec.ofNat 32 (62*k+z.val) := by
      have reorder : stamp lines k+BitVec.ofNat 32 z.val=
          BitVec.ofNat 32 (62*k+z.val)+(lines+54) := by
        simp only [stamp,BitVec.ofNat_add,BitVec.ofNat_mul]
        rw [BitVec.mul_comm (BitVec.ofNat 32 k)]
        change (62#32)*BitVec.ofNat 32 k+lines+(54#32)+BitVec.ofNat 32 z.val=
          (62#32)*BitVec.ofNat 32 k+BitVec.ofNat 32 z.val+(lines+(54#32))
        ac_rfl
      rw [reorder,BitVec.add_sub_cancel]
    exact (cancel i x).symm.trans ((congrArg (fun v : Word => v-(lines+54)) eq).trans (cancel j y))
  have num := congrArg BitVec.toNat normalized
  have hx := x.isLt
  have hy := y.isLt
  rw [BitVec.toNat_ofNat,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega)] at num
  omega

/-- Match the live Boolean array used by P_PathTraverse. Initial bits may be
nonempty here; specializing the runtime's all-false array requires freshness. -/
def Represents (memory : Memory) (lines epoch : Word) (seen : Array Bool) : Prop :=
  load32 memory 0x13580=epoch ∧
  ∀ j<seen.size, (load32 memory (stamp lines j)=epoch ↔ seen[j]! = true)

theorem set_already (seen : Array Bool) (id : Nat) (bound : id<seen.size) (yes : seen[id]! = true) :
    seen.set! id true=seen := by
  apply Array.ext
  · simp
  · intro j hj hk
    rw [←getElem!_pos _ j hj,←getElem!_pos _ j hk]
    by_cases eq : j=id
    · subst j
      rw [Array.getElem!_set!_self seen id true bound,yes]
    · exact Array.getElem!_set!_ne seen id j true (Ne.symm eq)

/-- A single stamp update has precisely the meaning of the production set!.
No injectivity or separation premise is hidden in this representation lemma. -/
theorem represents_update (before after : Memory) (lines epoch : Word) (seen : Array Bool)
    (id : Nat) (bound : id<seen.size) (h : Represents before lines epoch seen)
    (epochKept : load32 after 0x13580=epoch)
    (writes : ∀ j<seen.size, load32 after (stamp lines j)=
      if j=id then epoch else load32 before (stamp lines j)) :
    Represents after lines epoch (seen.set! id true) := by
  refine ⟨epochKept,?_⟩
  intro j hj
  have hj' : j<seen.size := by simpa using hj
  rw [writes j hj']
  by_cases eq : j=id
  · subst j
    rw [Array.getElem!_set!_self seen id true bound]
    simp
  · rw [if_neg eq,Array.getElem!_set!_ne seen id j true (Ne.symm eq)]
    exact h.2 j hj'

/-- Additional *initial-state* layout for mutable stamps. They are deliberately
not put in Initial.words, whose invariant requires unchanged contents. -/
structure Layout (initial : X86Memory.State) {n : Nat} {base : Word}
    {resolve : Collision.Intercept → Word} (h : Initial initial n base resolve)
    (lines : Word) (count : Nat) : Prop where
  countBound : count≤32768
  ids : ∀ i<n, (h.candidates i).id<count
  pointers : ∀ i<n, OriginalLineDispatch.pointer (atIndex initial i)=
    BitVec.ofNat 32 (h.candidates i).id*62+lines
  call : ∀ j<count, Apart (stamp lines j) (initial.regs 4-(4#32))
  side : ∀ i<n, ∀ j<count, OriginalLineCrossing.SideSafe (OriginalLineDispatch.view (atIndex initial i)) (stamp lines j)
  scratch : ∀ i<n, ∀ j<count, OriginalLineCrossing.ScratchSafe (OriginalLineDispatch.view (atIndex initial i)) (stamp lines j)
  records : ∀ j<count, ArraySafe base (stamp lines j)

/-- Exactly the condition needed to relate DOS stamps to the production
all-false array. In particular, counter wraparound does not imply freshness. -/
theorem fresh_represents (memory : Memory) (lines epoch : Word) (count : Nat)
    (counter : load32 memory 0x13580=epoch)
    (fresh : ∀ j<count, load32 memory (stamp lines j)≠epoch) :
    Represents memory lines epoch (Array.replicate count false) := by
  refine ⟨counter,?_⟩
  intro j hj
  have bound : j<count := by simpa using hj
  rw [getElem!_pos _ j hj,Array.getElem_replicate]
  simp only [Bool.false_eq_true,iff_false]
  exact fresh j bound

/-- The earlier firing proof supplies the initial stamp/bit relation from the
common post-sound boundary. It does not assume a reached scan memory image. -/
theorem firing_represents (gun : Fire.Gun) (s : X86Memory.State) (actor : Word)
    (thing : Collision.SolidThing) (angle : Angle) (ox oy : Fixed)
    (geometry : E1M1FiringGeometry.Inputs gun s actor thing angle ox oy)
    (before : E1M1ScanMemory.BeforeInit gun s (0x13580#32))
    (after : E1M1PathMapSetup.StackSafe (s.regs 4-(112#32)) (0x13580#32))
    (lines : Word) (seen : Array Bool)
    (safe : ∀ j<seen.size, E1M1PathMapFiring.Safe gun s (stamp lines j))
    (bits : ∀ j<seen.size, (load32 s.memory (stamp lines j)=load32 s.memory 0x13580+1 ↔ seen[j]! = true)) :
    Represents (E1M1ScanMemory.firstScan gun s).core.memory lines (load32 s.memory 0x13580+1) seen := by
  refine ⟨E1M1ScanMemory.firing_epoch gun s actor thing angle ox oy geometry before after,?_⟩
  intro j hj
  rw [E1M1ScanMemory.firing_frame gun s actor thing angle ox oy geometry _ (safe j hj)]
  exact bits j hj

variable (initial : X86Memory.State) (n : Nat) (base : Word) (resolve : Collision.Intercept → Word)
  (h : Initial initial n base resolve) (lines : Word) (count : Nat) (layout : Layout initial h lines count)
  (i : Nat) (s : X86Control.State) (r : Collision.PathResult) (inv : Stable initial h i s r) (hi : i<n)
include inv hi layout

theorem selected_stamp : OriginalLineDispatch.stamp s.core=stamp lines (h.candidates i).id := by
  unfold OriginalLineDispatch.stamp stamp
  rw [pointer initial n base resolve h i s r inv (by omega),layout.pointers i hi]
  rfl

theorem stamp_protected (j : Nat) (hj : j<count) :
    OriginalLineCrossing.Protected (OriginalLineDispatch.view s.core) (stamp lines j) :=
  ⟨side_safe initial n base resolve h i s r inv _ (layout.side i hi j hj),
    scratch_safe initial n base resolve h i s r inv _ (layout.scratch i hi j hj),
    record_safe initial n base resolve h i s r inv hi _ (layout.records j hj)⟩

/-- Stamping precedes the indirect callback. For all other IDs the initial
stride proof and current stack relation supply the dispatch frame contract. -/
theorem entry_word (fresh : OriginalLineDispatch.Fresh s.core) (j : Nat) (hj : j<count) :
    load32 (OriginalLineDispatch.entry s.core).core.memory (stamp lines j)=
      if j=(h.candidates i).id then load32 s.core.memory 0x13580 else load32 s.core.memory (stamp lines j) := by
  by_cases eq : j=(h.candidates i).id
  · rw [if_pos eq,eq,←selected_stamp initial n base resolve h lines count layout i s r inv hi]
    exact (OriginalLineDispatch.entry_observe s.core fresh).2.2
  · rw [if_neg eq]
    apply OriginalLineDispatch.entry_frame
    constructor
    · rw [selected_stamp initial n base resolve h lines count layout i s r inv hi]
      exact stamps_apart lines j _ (by have := layout.countBound; omega)
        (by have := layout.ids i hi; have := layout.countBound; omega) eq
    · rw [inv.stack]; exact layout.call j hj

/-- Every fresh callback outcome keeps the mark, including same-side rejection,
negative fraction and early stop. Duplicate visits do not write memory. -/
theorem step_stamps (j : Nat) (hj : j<count) :
    load32 (step (h.candidates i) s.core r).1.core.memory (stamp lines j)=
      if OriginalLineCell.already (OriginalLineCell.header s.core).core then load32 s.core.memory (stamp lines j)
      else if j=(h.candidates i).id then load32 s.core.memory 0x13580 else load32 s.core.memory (stamp lines j) := by
  by_cases seen : OriginalLineCell.already (OriginalLineCell.header s.core).core
  · simp only [step,if_pos seen]
    have last : OriginalLineCell.itemWord s.core≠(0xffffffff#32) := by
      have eq : OriginalLineCell.itemWord s.core=OriginalLineCell.itemWord (atIndex initial i) := by
        simp only [OriginalLineCell.itemWord,item initial n base resolve h i s r inv (by omega)]; rfl
      rw [eq]; exact h.nonlast i hi
    rw [(OriginalLineCell.skip_observe s.core last seen).1]
  · have mark := entry_word initial n base resolve h lines count layout i s r inv hi
      (fresh initial n base resolve h i s r inv hi seen) j hj
    have safe := stamp_protected initial n base resolve h lines count layout i s r inv hi j hj
    by_cases crosses : (h.candidates i).crosses=true
    · have ready := crossing_ready initial n base resolve h i s r inv hi seen crosses
      simp only [step,if_neg seen,if_pos crosses]
      exact (OriginalLineDispatch.callback_frame _ _ _ _ _ _ _ _ ready _ safe).trans mark
    · have no : (h.candidates i).crosses=false := by cases e : (h.candidates i).crosses <;> simp_all
      have ready := reject_ready initial n base resolve h i s r inv hi seen no
      simp only [step,if_neg seen,if_neg crosses]
      change load32 (OriginalLineResume.result _).core.memory _=_
      rw [OriginalLineResume.memory]
      exact (OriginalLineReject.tested_frame _ _ _ _ _ _
        (OriginalLineReject.entry_inputs _ _ _ _ _ _ ready.geometry ready.geometrySafe) _ safe.1).trans mark

omit layout in
/-- The epoch is a protected fixed word of the existing scan invariant. This
also applies to the final step of an early-stopping scan. -/
theorem step_epoch : load32 (step (h.candidates i) s.core r).1.core.memory 0x13580=load32 s.core.memory 0x13580 := by
  have protect :=  protection initial n base resolve h i s r inv hi (0x13580#32) (h.fixedWords _ (by simp))
  have array := record_safe initial n base resolve h i s r inv hi (0x13580#32) (h.arrayWords _ (h.fixedWords _ (by simp)))
  by_cases seen : OriginalLineCell.already (OriginalLineCell.header s.core).core
  · simp only [step,if_pos seen]
    have last : OriginalLineCell.itemWord s.core≠(0xffffffff#32) := by
      have eq : OriginalLineCell.itemWord s.core=OriginalLineCell.itemWord (atIndex initial i) := by
        simp only [OriginalLineCell.itemWord,item initial n base resolve h i s r inv (by omega)]; rfl
      rw [eq]; exact h.nonlast i hi
    rw [(OriginalLineCell.skip_observe s.core last seen).1]
  · by_cases crosses : (h.candidates i).crosses=true
    · simp only [step,if_neg seen,if_pos crosses]
      exact OriginalLineDispatch.frame _ _ _ _ _ _ _ _
        (crossing_ready initial n base resolve h i s r inv hi seen crosses) _ protect.1
        ⟨protect.2.1,protect.2.2,array⟩
    · have no : (h.candidates i).crosses=false := by cases e : (h.candidates i).crosses <;> simp_all
      simp only [step,if_neg seen,if_neg crosses]
      exact OriginalLineReject.frame _ _ _ _ _ _
        (reject_ready initial n base resolve h i s r inv hi seen no) _ protect.1 protect.2.1

/-- The branch reads the same bit as the production seen array. -/
theorem duplicate_iff (epoch : Word) (seen : Array Bool) (size : seen.size=count)
    (represented : Represents s.core.memory lines epoch seen) :
    OriginalLineCell.already (OriginalLineCell.header s.core).core ↔ seen[(h.candidates i).id]! = true := by
  change load32 s.core.memory 0x13580=load32 s.core.memory (OriginalLineDispatch.stamp s.core) ↔ _
  rw [selected_stamp initial n base resolve h lines count layout i s r inv hi,represented.1]
  exact eq_comm.trans (represented.2 _ (by rw [size]; exact layout.ids i hi))

/-- Setting an already-set bit is harmless; fresh lines are marked before any
geometric outcome, including a terminal early-out. -/
theorem step_represents (epoch : Word) (seen : Array Bool) (size : seen.size=count)
    (represented : Represents s.core.memory lines epoch seen) :
    Represents (step (h.candidates i) s.core r).1.core.memory lines epoch
      (seen.set! (h.candidates i).id true) := by
  have bound : (h.candidates i).id<seen.size := by rw [size]; exact layout.ids i hi
  have epochKept := (step_epoch initial n base resolve h i s r inv hi).trans represented.1
  by_cases duplicate : OriginalLineCell.already (OriginalLineCell.header s.core).core
  · rw [set_already seen _ bound ((duplicate_iff initial n base resolve h lines count layout i s r inv hi epoch seen size represented).mp duplicate)]
    refine ⟨epochKept,?_⟩
    intro j hj
    rw [step_stamps initial n base resolve h lines count layout i s r inv hi j (by rw [←size]; exact hj),if_pos duplicate]
    exact represented.2 j hj
  · apply represents_update s.core.memory _ lines epoch seen _ bound represented epochKept
    intro j hj
    rw [step_stamps initial n base resolve h lines count layout i s r inv hi j (by rw [←size]; exact hj),if_neg duplicate,represented.1]

omit inv hi layout in
/-- Update precisely the visited prefix; a stopping scan never marks its suffix. -/
def markPrefix (candidates : Nat → Candidate) : Nat → Nat → Array Bool → Array Bool
  | 0,_,seen => seen
  | k+1,i,seen => markPrefix candidates k (i+1) (seen.set! (candidates i).id true)

omit hi in
/-- All mutable-stamp facts are derived from one initial layout and the existing
scan invariant. No per-callback stamp or post-state assumption is supplied. -/
theorem scan_represents (k : Nat) (bound : i+k≤n) (epoch : Word) (seen : Array Bool)
    (size : seen.size=count) (represented : Represents s.core.memory lines epoch seen) :
    let out := OriginalLineScan.scan h.candidates k i s r
    Represents out.machine.core.memory lines epoch (markPrefix h.candidates out.visits i seen) := by
  induction k generalizing i s r seen with
  | zero => exact represented
  | succ k ih =>
    have next := step_represents initial n base resolve h lines count layout i s r inv (by omega) epoch seen size represented
    by_cases halt : OriginalLineScan.Halts (h.candidates i) s.core
    · simpa only [OriginalLineScan.scan,if_pos halt,markPrefix] using next
    · have keep : ¬OriginalLineCell.already (OriginalLineCell.header s.core).core →
          (h.candidates i).crosses=true → (h.candidates i).Continues := by
        intro unseen crossed
        by_cases neg : (h.candidates i).frac.raw<0
        · exact Or.inl neg
        · right
          cases e : (h.candidates i).early
          · rfl
          · exact False.elim (halt ⟨unseen,crossed,neg,e⟩)
      have advanced := (advance initial n base resolve h i s r inv (by omega) keep).1
      have tail := ih (i+1) (step (h.candidates i) s.core r).1 (step (h.candidates i) s.core r).2 advanced
        (by omega) (seen.set! (h.candidates i).id true) (by simpa using size) next
      simpa only [OriginalLineScan.scan,if_neg halt,markPrefix] using tail

omit inv hi in
/-- The array relation accompanies the already-proved original instruction
execution, including dynamic stops and repeated IDs. -/
theorem scan_execution (f : Option Flags) (r : Collision.PathResult)
    (collected : OriginalLineCollection.Tracks initial base resolve r.collected n)
    (epoch : Word) (seen : Array Bool) (size : seen.size=count)
    (represented : Represents initial.memory lines epoch seen) :
    let out := OriginalLineScan.scan h.candidates n 0 ⟨initial,f,0x2c57f⟩ r
    out.visits≤n ∧
    (∃ steps≤281*out.visits, X86Routine.Prefix OriginalLineMixedInvariant.program [] steps
      ⟨initial,f,0x2c57f⟩ out.machine) ∧
    Represents out.machine.core.memory lines epoch (markPrefix h.candidates out.visits 0 seen) := by
  have inv := start initial n base resolve h r f collected
  have run := OriginalLineScan.scan_correct initial n base resolve h 0 ⟨initial,f,0x2c57f⟩ r inv n (by omega)
  exact ⟨run.1,run.2.1,scan_represents initial n base resolve h lines count layout 0 _ r inv n (by omega)
    epoch seen size represented⟩

end Doom.Proofs.OriginalLineVisits
