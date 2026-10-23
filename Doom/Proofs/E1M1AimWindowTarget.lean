import Doom.Proofs.E1M1AimIteration
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 100000
namespace Doom.Proofs.E1M1AimWindowTarget
open Collision E1M1AimIteration
attribute [local irreducible] checkedPathDiv SolidThing.shootHeight E1M1AimSource.stopped AutoAim.center AutoAim.Window.bottom AutoAim.Window.top

def Good (state : LoopState) : Prop :=
  ∀ answer, state.1=some answer → answer.target=answer.window.map AutoAim.Window.target

def StepGood : ForInStep LoopState → Prop
  | .done value => Good value
  | .yield value => Good value

theorem empty_good (top bottom : Fixed) (history : Array AutoAim.Portal) :
    Good (none,top,bottom,history) := by
  intro answer same
  cases same

theorem miss_good (path : PathResult) (top bottom : Fixed) (history : Array AutoAim.Portal) :
    Good (some {path},top,bottom,history) := by
  intro answer same
  cases same
  rfl

theorem hit_good (slope : Fixed) (window : AutoAim.Window) (path : PathResult)
    (top bottom : Fixed) (history : Array AutoAim.Portal) :
    Good (some {slope,target:=some window.target,path,window:=some window},top,bottom,history) := by
  intro answer same
  cases same
  rfl

/-- Every successful live callback either keeps no early answer, returns a
windowless miss, or returns a present actor target. No division-success premise
is needed: erroneous callbacks cannot satisfy the successful-result equation. -/
theorem visit_good (scene : Scene) (shooter : Nat) (thing : SolidThing)
    (path : PathResult) (distance : Fixed) (i : Nat) (state : LoopState)
    (step : ForInStep LoopState)
    (run : visit scene shooter thing path distance i state=.ok step) :
    StepGood step := by
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
              intro answer same
              cases same
              rfl

/-- The successful finite hit fold preserves the target/window identity. -/
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

/-- Exhaustion and early stops preserve the exact target/window relation. -/
theorem remaining_target (scene : Scene) (shooter : Nat) (thing : SolidThing)
    (path : PathResult) (distance : Fixed) (indices : List Nat)
    (lower upper : Fixed) (history : Array AutoAim.Portal) (answer : AimResult)
    (run : remaining scene shooter thing path distance indices lower upper history=.ok answer)
    : answer.target=answer.window.map AutoAim.Window.target := by
  unfold remaining at run
  cases eq : forIn indices (none,upper,lower,history) (visit scene shooter thing path distance) with
  | error error => simp [eq,bind,Except.bind] at run
  | ok final =>
    have good := loop_good scene shooter thing path distance indices _ final (by simp [Good]) eq
    simp only [eq,bind,Except.bind] at run
    cases result : final.1 with
    | none =>
      simp only [result,pure,Except.pure,Except.ok.injEq] at run
      cases run
      rfl
    | some value =>
      simp only [result,pure,Except.pure,Except.ok.injEq] at run
      exact good answer (result.trans (congrArg some run))

/-- Every successful production query identifies its target in its captured
window, and has no target exactly when there is no window. -/
theorem aim (scene : Scene) (shooter : Nat) (angle : Angle) (distance : Fixed)
    (answer : AimResult) (run : scene.aimLineAttack shooter angle distance=.ok answer)
    : answer.target=answer.window.map AutoAim.Window.target := by
  rw [E1M1AimSource.live] at run
  cases eq : E1M1AimSource.attackPath scene shooter angle distance with
  | error error => simp [eq,bind,Except.bind] at run
  | ok pair =>
    rcases pair with ⟨thing,path⟩
    simp only [eq,bind,Except.bind] at run
    rw [E1M1AimIteration.live] at run
    exact remaining_target scene shooter thing path distance _ _ _ _ answer run
end Doom.Proofs.E1M1AimWindowTarget
