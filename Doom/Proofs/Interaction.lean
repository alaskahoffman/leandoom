import Doom.Interaction

namespace Doom.Proofs
open Interaction

/-- The HITree interpreter is deterministic for fixed input. This rules out an
additional, different observable execution hidden by an existential proof. -/
theorem interaction_run_unique {ctx : Engine.Context} {tree : Tree}
    {commands : List Ticcmd} {a b : Recording}
    (ha : Run ctx tree commands a) (hb : Run ctx tree commands b) : a = b := by
  induction ha generalizing b with
  | returned => cases hb; rfl
  | waiting => cases hb; rfl
  | input k cmd commands r h ih =>
    cases hb with
    | input _ _ _ _ h' => exact ih h'
  | present k frame commands r h ih =>
    cases hb with
    | present _ _ _ _ h' => exact congrArg (Recording.prepend frame) (ih h')
  | again k state events commands r h ih =>
    cases hb with
    | again _ _ _ _ _ h' => exact ih h'

/-- Universal in initial engine state AND command list. This connects the
HITree semantics to direct replay of the actual shared update/render functions.
It does not assert correspondence with DOS, or progress of unsupported paths. -/
theorem interaction_replay_sound (ctx : Engine.Context) (state : Engine.State)
    (commands : List Ticcmd) :
    Run ctx (program ctx state) commands (replay ctx state commands) := by
  induction commands generalizing state with
  | nil =>
    cases h : state.game.exitRequested <;>
      simp only [program, replay, h, Bool.false_eq_true, ↓reduceIte]
    · exact .waiting _
    · exact .returned _ _
  | cons cmd rest ih =>
    cases h : state.game.exitRequested
    · simp only [program, replay, h, Bool.false_eq_true, ↓reduceIte]
      apply Run.input
      cases ha : Engine.advance ctx state cmd with
      | error e =>
        simp only [onCommand, ha]
        exact .returned _ _
      | ok drawn =>
        simp only [onCommand, ha]
        apply Run.present
        cases hr : Engine.afterPresent ctx drawn.pending with
        | error e =>
          simp only [afterFrame, hr]
          exact .returned _ _
        | ok pair =>
          rcases pair with ⟨next, events⟩
          simp only [afterFrame, hr, tailCall]
          exact .again _ _ _ _ _ (ih next)
    · simp only [program, replay, h, ↓reduceIte]
      exact .returned _ _

/-- Exactly the direct replay, not just one permitted execution. -/
theorem interaction_replay_iff (ctx : Engine.Context) (state : Engine.State)
    (commands : List Ticcmd) (recording : Recording) :
    Run ctx (program ctx state) commands recording ↔
      recording = replay ctx state commands := by
  constructor
  · intro h
    exact interaction_run_unique h (interaction_replay_sound ctx state commands)
  · intro h
    subst recording
    exact interaction_replay_sound ctx state commands

end Doom.Proofs
