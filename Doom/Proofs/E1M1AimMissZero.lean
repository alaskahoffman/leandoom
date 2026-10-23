import Doom.Proofs.E1M1AimIteration
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 100000
namespace Doom.Proofs.E1M1AimMissZero
open Collision E1M1AimIteration
attribute [local irreducible] checkedPathDiv SolidThing.shootHeight E1M1AimSource.stopped AutoAim.center AutoAim.Window.bottom AutoAim.Window.top

def Good (state : LoopState) : Prop :=
  ∀ answer, state.1=some answer → answer.target=none → answer.slope=⟨0⟩

theorem empty_good (top bottom : Fixed) (history : Array AutoAim.Portal) :
    Good (none,top,bottom,history) := by
  intro answer same
  cases same

theorem miss_good (path : PathResult) (top bottom : Fixed) (history : Array AutoAim.Portal) :
    Good (some {path},top,bottom,history) := by
  intro answer same absent
  cases same
  rfl

theorem hit_good (slope : Fixed) (id : Nat) (path : PathResult) (window : Option AutoAim.Window)
    (top bottom : Fixed) (history : Array AutoAim.Portal) :
    Good (some {slope,target:=some id,path,window},top,bottom,history) := by
  intro answer same absent
  cases same
  cases absent

/-- Every successful live callback either keeps no early answer, returns a
zero-slope miss, or returns a present actor target. No division-success premise
is needed: erroneous callbacks cannot satisfy the successful-result equation. -/
theorem visit_good (scene : Scene) (shooter : Nat) (thing : SolidThing)
    (path : PathResult) (distance : Fixed) (i : Nat) (state : LoopState)
    (step : ForInStep LoopState)
    (run : visit scene shooter thing path distance i state=.ok step) :
    (match step with | .done value => Good value | .yield value => Good value) := by
  simp only [visit,bind,pure,Except.bind,Except.pure] at run
  split at run
  · split at run
    · injection run with same
      subst step
      exact miss_good _ _ _ _
    · split at run
      · split at run
        · injection run with same
          subst step
          exact miss_good _ _ _ _
        · split at run
          · split at run
            · cases run
            · split at run
              · split at run
                · cases run
                · split at run
                  · injection run with same
                    subst step
                    exact miss_good _ _ _ _
                  · injection run with same
                    subst step
                    exact empty_good _ _ _
              · split at run
                · injection run with same
                  subst step
                  exact miss_good _ _ _ _
                · injection run with same
                  subst step
                  exact empty_good _ _ _
          · split at run
            · split at run
              · cases run
              · split at run
                · injection run with same
                  subst step
                  exact miss_good _ _ _ _
                · injection run with same
                  subst step
                  exact empty_good _ _ _
            · split at run
              · injection run with same
                subst step
                exact miss_good _ _ _ _
              · injection run with same
                subst step
                exact empty_good _ _ _
      · cases run
  · split at run
    · injection run with same
      subst step
      exact empty_good _ _ _
    · split at run
      · cases run
      · split at run
        · injection run with same
          subst step
          exact empty_good _ _ _
        · split at run
          · cases run
          · split at run
            · injection run with same
              subst step
              exact empty_good _ _ _
            · injection run with same
              subst step
              exact hit_good _ _ _ _ _ _ _

/-- The successful finite hit fold preserves the zero-on-miss invariant. -/
theorem loop_good (scene : Scene) (shooter : Nat) (thing : SolidThing)
    (path : PathResult) (distance : Fixed) (indices : List Nat)
    (state final : LoopState) (good : Good state)
    (run : forIn indices state (visit scene shooter thing path distance)=Except.ok final) :
    Good final := by
  induction indices generalizing state with
  | nil =>
    simp only [List.forIn_nil,pure,Except.pure,Except.ok.injEq] at run
    exact run ▸ good
  | cons i rest ih =>
    rw [List.forIn_cons] at run
    cases eq : visit scene shooter thing path distance i state with
    | error error => simp [eq,bind,Except.bind] at run
    | ok step =>
      have next := visit_good scene shooter thing path distance i state step eq
      cases step with
      | done value =>
        simp only [eq,bind,Except.bind,pure,Except.pure,Except.ok.injEq] at run
        exact run ▸ next
      | yield value =>
        simp only [eq,bind,Except.bind] at run
        exact ih value next run

/-- Exhaustion and every successful early miss produce the same zero slope. -/
theorem remaining_zero (scene : Scene) (shooter : Nat) (thing : SolidThing)
    (path : PathResult) (distance : Fixed) (indices : List Nat)
    (lower upper : Fixed) (history : Array AutoAim.Portal) (answer : AimResult)
    (run : remaining scene shooter thing path distance indices lower upper history=.ok answer)
    (absent : answer.target=none) : answer.slope=⟨0⟩ := by
  unfold remaining at run
  cases eq : forIn indices (none,upper,lower,history) (visit scene shooter thing path distance) with
  | error error => simp [eq,bind,Except.bind] at run
  | ok final =>
    have good := loop_good scene shooter thing path distance indices _ final (by simp [Good]) eq
    simp only [eq,bind,Except.bind] at run
    cases result : final.1 with
    | none =>
      simp only [result,pure,Except.pure,Except.ok.injEq] at run
      exact congrArg AimResult.slope run.symm
    | some value =>
      simp only [result,pure,Except.pure,Except.ok.injEq] at run
      exact good answer (result.trans (congrArg some run)) absent

/-- For the actual source aim function, absent target implies zero slope for
any successful call. This is not an assumption about reached machine answers. -/
theorem aim (scene : Scene) (shooter : Nat) (angle : Angle) (distance : Fixed)
    (answer : AimResult) (run : scene.aimLineAttack shooter angle distance=.ok answer)
    (absent : answer.target=none) : answer.slope=⟨0⟩ := by
  rw [E1M1AimSource.live] at run
  cases eq : E1M1AimSource.attackPath scene shooter angle distance with
  | error error => simp [eq,bind,Except.bind] at run
  | ok pair =>
    rcases pair with ⟨thing,path⟩
    simp only [eq,bind,Except.bind] at run
    rw [E1M1AimIteration.live] at run
    exact remaining_zero scene shooter thing path distance _ _ _ _ answer run absent
end Doom.Proofs.E1M1AimMissZero
