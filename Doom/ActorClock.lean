/- State-countdown branch of P_MobjThinker. Original DOOM uses -1 to hold;
otherwise it decrements the signed 32-bit counter and enters the next state at 0.
GPL-2.0-or-later. See COPYING.md. -/
namespace Doom.ActorClock

inductive Decision where
  | hold (tics : Int32)
  | enterNext
  deriving BEq, Repr

/-- Declarative implementation shared by live actor state machines. -/
def step (tics : Int32) : Decision :=
  if tics == -1 then .hold tics
  else if tics == 1 then .enterNext else .hold (tics-1)

/-- Execute the clock decision with an explicit state-entry continuation. Entry
may change state again and produce effects; the clock never repeats that action. -/
def advance (setTics : Int32 → α → α) (enterNext : α → α) (tics : Int32) (state : α) : α :=
  match step tics with
  | .hold n => setTics n state
  | .enterNext => enterNext (setTics 0 state)

end Doom.ActorClock
