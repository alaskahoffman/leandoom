import Doom.Proofs.OriginalLineVisits
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.OriginalLineVisitedRun
open Verification X86 X86Memory X86Control BlockSummary
open OriginalLineMixedInvariant
open OriginalLineVisits (Represents markPrefix)

/-- Marking never changes the represented line count, including repeated IDs. -/
theorem mark_size (cs : Nat → Candidate) (k i : Nat) (seen : Array Bool) :
    (markPrefix cs k i seen).size=seen.size := by
  induction k generalizing i seen with
  | zero => rfl
  | succ k ih => simpa only [markPrefix,Array.size_set!] using ih (i+1) (seen.set! (cs i).id true)

/-- Later candidates never clear a bit, regardless of duplicate IDs. -/
theorem mark_keeps (cs : Nat → Candidate) (k i : Nat) (seen : Array Bool)
    (j : Nat) (bound : j<seen.size) (marked : seen[j]! =true) :
    (markPrefix cs k i seen)[j]! =true := by
  induction k generalizing i seen with
  | zero => exact marked
  | succ k ih =>
    apply ih (i+1) (seen.set! (cs i).id true) (by simpa using bound)
    by_cases eq : (cs i).id=j
    · rw [eq,Array.getElem!_set!_self seen j true bound]
    · rw [Array.getElem!_set!_ne seen (cs i).id j true eq]
      exact marked

/-- A valid first candidate is marked even if its geometry produces no hit. -/
theorem first_marked (cs : Nat → Candidate) (k i : Nat) (seen : Array Bool)
    (bound : (cs i).id<seen.size) :
    (markPrefix cs (k+1) i seen)[(cs i).id]! =true := by
  exact mark_keeps cs k (i+1) (seen.set! (cs i).id true) (cs i).id
    (by simpa using bound) (Array.getElem!_set!_self seen (cs i).id true bound)

/-- The continuing scan used by aiming marks exactly its candidate prefix.
The per-line duplicate/crossing behavior reuses the existing stamp proof. -/
theorem run_represents (initial : X86Memory.State) (n : Nat) (base : Word)
    (resolve : Collision.Intercept → Word) (h : Initial initial n base resolve)
    (lines : Word) (count : Nat) (layout : OriginalLineVisits.Layout initial h lines count)
    (i : Nat) (s : X86Control.State) (r : Collision.PathResult) (inv : Stable initial h i s r)
    (k : Nat) (bound : i+k≤n)
    (keep : ∀ j, i≤j → j<i+k → (h.candidates j).crosses=true → (h.candidates j).Continues)
    (epoch : Word) (seen : Array Bool) (size : seen.size=count)
    (represented : Represents s.core.memory lines epoch seen) :
    Represents (run h.candidates k i s r).1.core.memory lines epoch
      (markPrefix h.candidates k i seen) := by
  induction k generalizing i s r seen with
  | zero => exact represented
  | succ k ih =>
    have updated := OriginalLineVisits.step_represents initial n base resolve h lines count layout i s r inv
      (by omega) epoch seen size represented
    have next := (advance initial n base resolve h i s r inv (by omega)
      (fun _ crossed => keep i (by omega) (by omega) crossed)).1
    exact ih (i+1) (step (h.candidates i) s.core r).1 (step (h.candidates i) s.core r).2 next
      (by omega) (fun j lo hi => keep j (by omega) (by omega))
      (seen.set! (h.candidates i).id true) (by simpa using size) updated

/-- The sentinel header and real iterator return do not write memory, so the
visited set accompanies the exact finished state used by the firing proof. -/
theorem finished_represents (initial : X86Memory.State) (n : Nat) (base : Word)
    (resolve : Collision.Intercept → Word) (h : Initial initial n base resolve)
    (lines : Word) (count : Nat) (layout : OriginalLineVisits.Layout initial h lines count)
    (f : Option Flags) (r : Collision.PathResult)
    (tracked : OriginalLineCollection.Tracks initial base resolve r.collected n)
    (keep : ∀ j<n, (h.candidates j).crosses=true → (h.candidates j).Continues)
    (epoch : Word) (seen : Array Bool) (size : seen.size=count)
    (represented : Represents initial.memory lines epoch seen) :
    Represents (finished initial n base resolve h f r).1.core.memory lines epoch
      (markPrefix h.candidates n 0 seen) := by
  exact run_represents initial n base resolve h lines count layout 0 ⟨initial,f,0x2c57f⟩ r
    (start initial n base resolve h r f tracked) n (by omega)
    (fun j _ hj => keep j (by omega)) epoch seen size represented
end Doom.Proofs.OriginalLineVisitedRun
