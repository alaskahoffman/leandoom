import Doom.ActorClock
import Init.Data.SInt.Lemmas

namespace Doom.Proofs
open ActorClock

/-- Independent operational transcription of the original countdown branch.
This models wrapping 32-bit subtraction; it excludes preceding XY/Z movement,
nightmare respawning, and the implementation of the state-entry continuation. -/
def originalActorClock (tics : Int32) : Decision :=
  if tics == -1 then .hold tics else
    let decremented := tics-1
    if decremented == 0 then .enterNext else .hold decremented

/-- All 32-bit countdown values, including the -1 sentinel and wrapping cases. -/
theorem actor_clock_matches_original (tics : Int32) :
    step tics = originalActorClock tics := by
  simp [step, originalActorClock, Int32.sub_eq_iff_eq_add]

/-- A local simulation rule: if corresponding hosts agree on their countdown,
and both retaining a countdown and entering the next state preserve their
relation, a complete clock update preserves it. No action semantics are assumed
implicitly; they are the explicit hypotheses of this theorem. -/
theorem actor_clock_preserves (R : α → β → Prop)
    (setA : Int32 → α → α) (setB : Int32 → β → β)
    (enterA : α → α) (enterB : β → β)
    (hset : ∀ n a b, R a b → R (setA n a) (setB n b))
    (henter : ∀ a b, R a b → R (enterA a) (enterB b))
    (tics : Int32) (a : α) (b : β) (h : R a b) :
    R (advance setA enterA tics a)
      (match originalActorClock tics with
        | .hold n => setB n b
        | .enterNext => enterB (setB 0 b)) := by
  rw [← actor_clock_matches_original]
  unfold advance
  cases step tics with
  | hold n => exact hset n a b h
  | enterNext => exact henter _ _ (hset 0 a b h)

end Doom.Proofs
