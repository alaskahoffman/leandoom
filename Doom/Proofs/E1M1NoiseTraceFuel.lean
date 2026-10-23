import Doom.Proofs.E1M1NoisePreservation
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1NoiseTraceFuel
open Verification X86 X86Memory X86Control E1M1NoiseRecursive E1M1NoisePreservation

/-- Extra evaluator fuel cannot change a completed original-machine traversal. -/
theorem eval_succ (k : Nat) (phase : Phase) (s t : X86Control.State)
    (run : eval k phase s=some t) : eval (k+1) phase s=some t := by
  induction k generalizing phase s t with
  | zero => simp [eval] at run
  | succ k ih =>
    cases phase with
    | sector =>
      rw [eval] at run ⊢
      try simp only at run ⊢
      split at run
      · rename_i done
        simp only [done,ite_true]; exact run
      · rename_i notDone
        simp only [if_neg notDone]
        split at run
        · rename_i more
          simp only [more,ite_true]
          exact ih .lines _ _ run
        · contradiction
    | lines =>
      rw [eval] at run ⊢
      try simp only at run ⊢
      split at run
      · contradiction
      · rename_i opening
        simp only [if_neg opening]
        split at run
        · rename_i call
          simp only [call,ite_true]
          cases childRun : eval k .sector (dispatch s) with
          | none => simp only [dispatch] at childRun; simp [childRun] at run
          | some u =>
            have childMore := ih .sector _ _ childRun
            simp only [dispatch] at childRun childMore
            simp only [childRun,Option.bind_eq_bind,Option.bind_some] at run
            simp only [childMore,Option.bind_eq_bind,Option.bind_some]
            split at run
            · rename_i ret
              try simp only [ret,ite_true]
              split at run
              · rename_i more
                try simp only [more,ite_true]
                exact ih .lines _ _ run
              · rename_i notMore
                try simp only [if_neg notMore]
                exact run
            · rename_i noRet
              try simp only [if_neg noRet] at run
              contradiction
        · rename_i notCall
          simp only [if_neg notCall]
          split at run
          · rename_i skip
            simp only [skip,ite_true,Option.bind_eq_bind,Option.bind_some]
            simp only [Option.bind_eq_bind,Option.bind_some] at run
            split at run
            · rename_i more
              simp only [more,ite_true]; exact ih .lines _ _ run
            · rename_i notMore
              simp only [if_neg notMore]; exact run
          · contradiction

theorem eval_mono (k j : Nat) (phase : Phase) (s t : X86Control.State)
    (le : k≤j) (run : eval k phase s=some t) : eval j phase s=some t := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le le
  clear le
  induction d with
  | zero => simpa only [Nat.add_zero] using run
  | succ d ih => exact eval_succ _ phase s t ih

/-- Every finite trace is realized by the evaluator. This is adequacy for an
already supplied trace; it does not construct a trace for every initial state. -/
theorem trace_evaluates {phase s t w} (h : Trace phase s t w) :
    ∃ k, eval k phase s=some t := by
  induction h with
  | sectorDone s done => exact ⟨1,by simp only [eval,sector] at done ⊢; simp [done,finish]⟩
  | sectorMore s t w more body ih =>
    obtain ⟨k,run⟩ := ih
    refine ⟨k+1,?_⟩
    have notDone : (sector s).pc≠0x27011 := by omega
    simpa only [eval,sector,if_neg notDone,more,ite_true,startLines,show (0x26fa6 : Nat)≠0x27011 by decide,ite_false] using run
  | lineDone s opening skip done =>
    refine ⟨1,?_⟩
    have noCall : (dispatch s).pc≠0x26f60 := by omega
    simp only [eval,if_neg (not_not_intro opening),dispatch,skip,if_neg noCall,ite_true,ite_false,
      Option.bind_eq_bind,Option.bind_some,advance,done,finish,show (0x27006 : Nat)≠0x26f60 by decide,show (0x27011 : Nat)≠0x26fa8 by decide,ite_false]
  | lineMore s t w opening skip more body ih =>
    obtain ⟨k,run⟩ := ih
    refine ⟨k+1,?_⟩
    have noCall : (dispatch s).pc≠0x26f60 := by omega
    simpa only [eval,if_neg (not_not_intro opening),dispatch,if_neg noCall,skip,ite_true,
      Option.bind_eq_bind,Option.bind_some,advance,more,show (0x27006 : Nat)≠0x26f60 by decide,ite_false] using run
  | childDone s u w opening call child ret done ih =>
    obtain ⟨k,run⟩ := ih
    refine ⟨k+1,?_⟩
    have stop : (advance u).pc≠0x26fa8 := by omega
    simp only [dispatch] at run
    simp only [eval,if_neg (not_not_intro opening),dispatch,call,ite_true,run,
      Option.bind_eq_bind,Option.bind_some,ret,advance,if_neg stop,done,finish,show (0x27011 : Nat)≠0x26fa8 by decide,ite_false]
  | childMore s u t w v opening call child ret more body childIH bodyIH =>
    obtain ⟨k,cr⟩ := childIH
    obtain ⟨j,br⟩ := bodyIH
    have cr := eval_mono k (k+j) .sector _ _ (by omega) cr
    have br := eval_mono j (k+j) .lines _ _ (by omega) br
    refine ⟨k+j+1,?_⟩
    simp only [dispatch] at cr
    simpa only [eval,if_neg (not_not_intro opening),dispatch,call,ite_true,cr,
      Option.bind_eq_bind,Option.bind_some,ret,advance,more] using br
end Doom.Proofs.E1M1NoiseTraceFuel
