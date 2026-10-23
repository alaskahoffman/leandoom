import Doom.Motion
import Doom.PlayerAnim

namespace Doom.PlayerReaction

/-- P_PlayerThink tests nonzero, not positive: the original word subtraction
wraps even for negative/extreme timer encodings. Movement resumes next tic
when a timer of one is decremented to zero. -/
def remaining (timer : Int32) : Int32 := if timer = 0 then 0 else timer - 1

def move (body : Motion) (timer : Int32) (cmd : Ticcmd) : Motion :=
  if timer = 0 then body.movePlayer cmd else body

def animate (anim : PlayerAnim.State) (timer : Int32) (cmd : Ticcmd) : PlayerAnim.State :=
  if timer = 0 then anim.startWalking cmd else anim

end Doom.PlayerReaction
