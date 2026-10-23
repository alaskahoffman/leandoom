/- Original live player mobj states from DOOM info.c. This is the player's
world body, separate from weapon psprites. GPL-2.0-or-later. -/
import Doom.ActorClock
import Doom.Ticcmd

namespace Doom.PlayerAnim

structure State where
  frame : Nat := 149
  tics : Int32 := -1
  deriving Inhabited, BEq

/-- S_PLAY, RUN1..4, ATK1..2, PAIN1..2; all entry actions are null except
PAIN2's A_Pain. The Boolean is that sound request, handled by the host. -/
def enter (frame : Nat) : State × Bool :=
  (⟨frame, if frame == 149 then -1 else if frame == 154 then 12
    else if frame == 155 then 6 else 4⟩, frame == 157)

/-- The command-driven standing-to-walking transition used by prepareTick. -/
def State.startWalking (s : State) (cmd : Ticcmd) : State :=
  if s.frame == 149 && (cmd.forwardMove != 0 || cmd.sideMove != 0)
    then (enter 150).1 else s

def tick (s : State) : State × Bool :=
  match ActorClock.step s.tics with
  | .hold n => ({ s with tics := n },false)
  | .enterNext => enter (match s.frame with
    | 150 => 151 | 151 => 152 | 152 => 153 | 153 => 150
    | 155 => 154 | 156 => 157 | _ => 149)

end Doom.PlayerAnim
