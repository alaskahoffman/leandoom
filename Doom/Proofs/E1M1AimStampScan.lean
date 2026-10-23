import Doom.Proofs.E1M1AimStampImage
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimStampScan
open Verification X86 X86Memory X86Control BlockSummary
open OriginalLineMixedInvariant
open OriginalLineVisits (stamp Represents markPrefix)
open E1M1AimStampImage (Image)
attribute [local irreducible] load32 store32

/-- The existing exact stamp write strengthens the Boolean visited invariant.
Duplicate, rejected, accepted and stopping callbacks all use this same rule. -/
theorem step_image (initial : X86Memory.State) (n : Nat) (base : Word)
    (resolve : Collision.Intercept → Word) (h : Initial initial n base resolve)
    (lines : Word) (count : Nat) (layout : OriginalLineVisits.Layout initial h lines count)
    (i : Nat) (s : X86Control.State) (r : Collision.PathResult) (inv : Stable initial h i s r) (hi : i<n)
    (origin : Memory) (epoch : Word) (seen : Array Bool) (size : seen.size=count)
    (represented : Represents s.core.memory lines epoch seen)
    (image : Image origin s.core.memory lines epoch seen) :
    Image origin (step (h.candidates i) s.core r).1.core.memory lines epoch
      (seen.set! (h.candidates i).id true) := by
  have bound : (h.candidates i).id<seen.size := by rw [size]; exact layout.ids i hi
  have counter := (OriginalLineVisits.step_epoch initial n base resolve h i s r inv hi).trans image.counter
  by_cases duplicate : OriginalLineCell.already (OriginalLineCell.header s.core).core
  · rw [OriginalLineVisits.set_already seen _ bound
      ((OriginalLineVisits.duplicate_iff initial n base resolve h lines count layout i s r inv hi
        epoch seen size represented).mp duplicate)]
    refine ⟨counter,?_⟩
    intro j hj
    rw [OriginalLineVisits.step_stamps initial n base resolve h lines count layout i s r inv hi
      j (by rw [←size]; exact hj),if_pos duplicate]
    exact image.stamps j hj
  · refine ⟨counter,?_⟩
    intro j hj
    have oldBound : j<seen.size := by simpa using hj
    rw [OriginalLineVisits.step_stamps initial n base resolve h lines count layout i s r inv hi
      j (by rw [←size]; exact oldBound),if_neg duplicate,image.counter]
    by_cases eq : j=(h.candidates i).id
    · subst j
      rw [if_pos rfl,Array.getElem!_set!_self seen _ true bound]
      rfl
    · rw [if_neg eq,Array.getElem!_set!_ne seen _ j true (Ne.symm eq)]
      exact image.stamps j oldBound

/-- An early-stopping scan retains exactly the visited prefix's stamp image;
the suffix is not marked. No post-scan memory fact is supplied. -/
theorem scan_image (initial : X86Memory.State) (n : Nat) (base : Word)
    (resolve : Collision.Intercept → Word) (h : Initial initial n base resolve)
    (lines : Word) (count : Nat) (layout : OriginalLineVisits.Layout initial h lines count)
    (i : Nat) (s : X86Control.State) (r : Collision.PathResult) (inv : Stable initial h i s r)
    (k : Nat) (bound : i+k≤n) (origin : Memory) (epoch : Word) (seen : Array Bool)
    (size : seen.size=count) (represented : Represents s.core.memory lines epoch seen)
    (image : Image origin s.core.memory lines epoch seen) :
    let out := OriginalLineScan.scan h.candidates k i s r
    Image origin out.machine.core.memory lines epoch (markPrefix h.candidates out.visits i seen) := by
  induction k generalizing i s r seen with
  | zero => exact image
  | succ k ih =>
    have next := step_image initial n base resolve h lines count layout i s r inv (by omega)
      origin epoch seen size represented image
    have rep := OriginalLineVisits.step_represents initial n base resolve h lines count layout i s r inv
      (by omega) epoch seen size represented
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
      have tail := ih (i+1) (step (h.candidates i) s.core r).1 (step (h.candidates i) s.core r).2
        advanced (by omega) (seen.set! (h.candidates i).id true) (by simpa using size) rep next
      simpa only [OriginalLineScan.scan,if_neg halt,markPrefix] using tail

/-- The continuing scan used by aiming preserves the same exact stamp image. -/
theorem run_image (initial : X86Memory.State) (n : Nat) (base : Word)
    (resolve : Collision.Intercept → Word) (h : Initial initial n base resolve)
    (lines : Word) (count : Nat) (layout : OriginalLineVisits.Layout initial h lines count)
    (i : Nat) (s : X86Control.State) (r : Collision.PathResult) (inv : Stable initial h i s r)
    (k : Nat) (bound : i+k≤n)
    (keep : ∀ j, i≤j → j<i+k → (h.candidates j).crosses=true → (h.candidates j).Continues)
    (origin : Memory) (epoch : Word) (seen : Array Bool) (size : seen.size=count)
    (represented : Represents s.core.memory lines epoch seen)
    (image : Image origin s.core.memory lines epoch seen) :
    Image origin (run h.candidates k i s r).1.core.memory lines epoch
      (markPrefix h.candidates k i seen) := by
  induction k generalizing i s r seen with
  | zero => exact image
  | succ k ih =>
    have updated := step_image initial n base resolve h lines count layout i s r inv (by omega)
      origin epoch seen size represented image
    have rep := OriginalLineVisits.step_represents initial n base resolve h lines count layout i s r inv
      (by omega) epoch seen size represented
    have next := (advance initial n base resolve h i s r inv (by omega)
      (fun _ crossed => keep i (by omega) (by omega) crossed)).1
    exact ih (i+1) (step (h.candidates i) s.core r).1 (step (h.candidates i) s.core r).2 next
      (by omega) (fun j lo hi => keep j (by omega) (by omega))
      (seen.set! (h.candidates i).id true) (by simpa using size) rep updated

/-- Sentinel dispatch and iterator return do not alter memory. -/
theorem finished_image (initial : X86Memory.State) (n : Nat) (base : Word)
    (resolve : Collision.Intercept → Word) (h : Initial initial n base resolve)
    (lines : Word) (count : Nat) (layout : OriginalLineVisits.Layout initial h lines count)
    (f : Option Flags) (r : Collision.PathResult)
    (tracked : OriginalLineCollection.Tracks initial base resolve r.collected n)
    (keep : ∀ j<n, (h.candidates j).crosses=true → (h.candidates j).Continues)
    (origin : Memory) (epoch : Word) (seen : Array Bool) (size : seen.size=count)
    (represented : Represents initial.memory lines epoch seen)
    (image : Image origin initial.memory lines epoch seen) :
    Image origin (finished initial n base resolve h f r).1.core.memory lines epoch
      (markPrefix h.candidates n 0 seen) :=
  run_image initial n base resolve h lines count layout 0 ⟨initial,f,0x2c57f⟩ r
    (start initial n base resolve h r f tracked) n (by omega)
    (fun j _ hj => keep j (by omega)) origin epoch seen size represented image
end Doom.Proofs.E1M1AimStampScan
