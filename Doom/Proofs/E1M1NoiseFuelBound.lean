import Doom.Proofs.E1M1NoiseLineProgress
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1NoiseFuelBound
open Verification X86 X86Memory X86Control E1M1NoiseRecursive E1M1NoisePreservation
open E1M1NoiseAccounting E1M1NoiseLedger E1M1NoiseLineProgress

/-- Line-progress annotations on the existing trace, not a new evaluator.
The entry bound and decreases still need justification for reachable map states;
`skip_remaining` and `child_remaining` supply the local machine-level steps. -/
inductive LoopGuards (limit : Nat) : {layout : List Word} → {phase : Phase} →
    {s t : X86Control.State} → {w : List Word} → {n : Nat} →
    CheckedTrace layout phase s t w n → Prop
  | sectorDone {layout} (s done safe) :
      LoopGuards limit (CheckedTrace.sectorDone (layout:=layout) s done safe)
  | sectorMore {layout} (s t w n more safe) (body : CheckedTrace layout .lines (startLines s) t w n)
      (entry : remaining (startLines s)≤limit) (loops : LoopGuards limit body) :
      LoopGuards limit (CheckedTrace.sectorMore s t w n more safe body)
  | lineDone {layout} (s opening skip done safe) :
      LoopGuards limit (CheckedTrace.lineDone (layout:=layout) s opening skip done safe)
  | lineMore {layout} (s t w n opening skip more safe)
      (body : CheckedTrace layout .lines (advance (dispatch s)) t w n)
      (progress : remaining (advance (dispatch s))<remaining s) (loops : LoopGuards limit body) :
      LoopGuards limit (CheckedTrace.lineMore s t w n opening skip more safe body)
  | childDone {layout} (s u w n opening call safe)
      (child : CheckedTrace layout .sector (dispatch s) u w n) (ret done)
      (active : 0<remaining s) (loops : LoopGuards limit child) :
      LoopGuards limit (CheckedTrace.childDone s u w n opening call safe child ret done)
  | childMore {layout} (s u t w v n m opening call safe)
      (child : CheckedTrace layout .sector (dispatch s) u w n) (ret more)
      (body : CheckedTrace layout .lines (advance u) t v m)
      (progress : remaining (advance u)<remaining s)
      (childLoops : LoopGuards limit child) (bodyLoops : LoopGuards limit body) :
      LoopGuards limit (CheckedTrace.childMore s u t w v n m opening call safe child ret more body)

def allowance (limit : Nat) (phase : Phase) (n : Nat) (s : X86Control.State) : Nat :=
  n*(limit+1)+(match phase with | .sector => 0 | .lines => remaining s)+1

/-- An explicit bound for a supplied finite trace, including pruned child calls.
This does not assume that the evaluator already succeeds with the stated fuel. -/
theorem bounded_fuel {limit layout phase s t w n} {h : CheckedTrace layout phase s t w n}
    (loops : LoopGuards limit h) :
    ∃ k, k≤allowance limit phase n s ∧ eval k phase s=some t := by
  induction loops with
  | sectorDone s done safe =>
    refine ⟨1,by simp [allowance],?_⟩
    simp only [eval,sector] at done ⊢
    simp [done,finish]
  | sectorMore s t w n more safe body entry loops ih =>
    obtain ⟨k,budget,run⟩ := ih
    have charge := sector_more_charge s.core more
    refine ⟨k+1,?_,?_⟩
    · simp only [allowance,charge,Nat.add_mul,Nat.one_mul] at *
      omega
    · have notDone : (sector s).pc≠0x27011 := by omega
      simpa only [eval,sector,if_neg notDone,more,ite_true,startLines,
        show (0x26fa6 : Nat)≠0x27011 by decide,ite_false] using run
  | lineDone s opening skip done safe =>
    refine ⟨1,by simp [allowance],?_⟩
    simp only [eval,if_neg (not_not_intro opening),dispatch,skip,ite_true,Option.bind_eq_bind,Option.bind_some,
      advance,done,finish,show (0x27006 : Nat)≠0x26f60 by decide,show (0x27011 : Nat)≠0x26fa8 by decide,ite_false]
  | lineMore s t w n opening skip more safe body progress loops ih =>
    obtain ⟨k,budget,run⟩ := ih
    refine ⟨k+1,?_,?_⟩
    · simp only [allowance] at *; omega
    · simpa only [eval,if_neg (not_not_intro opening),dispatch,skip,ite_true,
        Option.bind_eq_bind,Option.bind_some,advance,more,
        show (0x27006 : Nat)≠0x26f60 by decide,ite_false] using run
  | childDone s u w n opening call safe child ret done active loops ih =>
    obtain ⟨k,budget,run⟩ := ih
    refine ⟨k+1,?_,?_⟩
    · simp only [allowance] at *; omega
    · simp only [dispatch] at run
      simp only [eval,if_neg (not_not_intro opening),dispatch,call,ite_true,run,
        Option.bind_eq_bind,Option.bind_some,ret,advance,done,finish,
        show (0x27011 : Nat)≠0x26fa8 by decide,ite_false]
  | childMore s u t w v n m opening call safe child ret more body progress childLoops bodyLoops childIH bodyIH =>
    obtain ⟨k,kb,cr⟩ := childIH
    obtain ⟨j,jb,br⟩ := bodyIH
    have cr := E1M1NoiseTraceFuel.eval_mono k (max k j) .sector _ _ (Nat.le_max_left ..) cr
    have br := E1M1NoiseTraceFuel.eval_mono j (max k j) .lines _ _ (Nat.le_max_right ..) br
    refine ⟨max k j+1,?_,?_⟩
    · simp only [allowance,Nat.add_mul] at *
      omega
    · simp only [dispatch] at cr
      simpa only [eval,if_neg (not_not_intro opening),dispatch,call,ite_true,cr,
        Option.bind_eq_bind,Option.bind_some,ret,advance,more] using br

theorem at_allowance {limit layout phase s t w n} {h : CheckedTrace layout phase s t w n}
    (loops : LoopGuards limit h) : eval (allowance limit phase n s) phase s=some t := by
  obtain ⟨k,le,run⟩ := bounded_fuel loops
  exact E1M1NoiseTraceFuel.eval_mono _ _ _ _ _ le run

/-- Combine actual recursive admission accounting and per-sector line bounds.
The finite trace and its guards remain premises; unconditional termination and
establishing these guards from the fixed E1M1 setup are separate obligations. -/
theorem sector_budget {limit layout s t w n} (h : CheckedTrace layout .sector s t w n)
    (loops : LoopGuards limit h) (generation : Word) (xs : Ledger)
    (shape : addresses xs=layout) (rep : Represents generation s.core.memory xs) :
    eval (2*layout.length*(limit+1)+1) .sector s=some t := by
  have admissions := h.admission_bound generation xs shape rep
  have mult := Nat.mul_le_mul_right (limit+1) admissions
  exact E1M1NoiseTraceFuel.eval_mono _ _ _ _ _ (by simp only [allowance]; omega) (at_allowance loops)

theorem sector_execution {limit layout s t w n} (h : CheckedTrace layout .sector s t w n)
    (loops : LoopGuards limit h) (generation : Word) (xs : Ledger)
    (shape : addresses xs=layout) (rep : Represents generation s.core.memory xs) (pc : s.pc=0x26f60) :
    Runs (bound (2*layout.length*(limit+1)+1)) s t :=
  E1M1NoiseRecursive.execution _ .sector s t pc (sector_budget h loops generation xs shape rep)
end Doom.Proofs.E1M1NoiseFuelBound
