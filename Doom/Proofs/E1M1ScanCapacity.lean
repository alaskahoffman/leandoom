import Doom.Proofs.E1M1ThingTraversal
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace Doom.Proofs.E1M1ScanCapacity
open Verification X86 X86Memory X86Control BlockSummary

theorem step_size (c : OriginalLineMixedInvariant.Candidate) (s : X86Memory.State)
    (r : Collision.PathResult) :
    (OriginalLineMixedInvariant.step c s r).2.collected.size≤r.collected.size+1 := by
  unfold OriginalLineMixedInvariant.step
  split
  · simp
  · split
    · split
      · simp
      · split <;> simp
    · simp

theorem run_size (candidates : Nat → OriginalLineMixedInvariant.Candidate) (n i : Nat)
    (s : X86Control.State) (r : Collision.PathResult) :
    (OriginalLineMixedInvariant.run candidates n i s r).2.collected.size≤r.collected.size+n := by
  induction n generalizing i s r with
  | zero => simp [OriginalLineMixedInvariant.run]
  | succ n ih =>
    have tail := ih (i+1) (OriginalLineMixedInvariant.step (candidates i) s.core r).1
      (OriginalLineMixedInvariant.step (candidates i) s.core r).2
    have one := step_size (candidates i) s.core r
    change (OriginalLineMixedInvariant.run candidates n (i+1) _ _).2.collected.size≤_
    omega

/-- Skipped, negative, and early-stop candidates add no records. Counting all
candidates is a conservative bound that can be supplied before the scan runs. -/
theorem finished_size (initial : X86Memory.State) (n : Nat) (base : Word)
    (resolve : Collision.Intercept → Word) (h : OriginalLineMixedInvariant.Initial initial n base resolve)
    (f : Option Flags) (trace : Collision.Divline) :
    (OriginalLineMixedInvariant.finished initial n base resolve h f {trace:=trace}).2.collected.size≤n := by
  simpa [OriginalLineMixedInvariant.finished] using run_size h.candidates n 0 ⟨initial,f,0x2c57f⟩ {trace:=trace}
end Doom.Proofs.E1M1ScanCapacity
