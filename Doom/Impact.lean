/- P_SpawnPuff/P_SpawnBlood and their nonblocking mobj movement/state branches,
pinned Chocolate Doom 3.1.1 p_mobj.c. Copyright id Software / Simon Howard.
GPL-2.0-or-later. See COPYING.md. -/
import Doom.ImpactData
import Doom.Motion

namespace Doom.Impact
open ImpactData

structure Body where
  motion : Motion
  frame : Nat
  tics : Int32
  lastlook : Nat
  thinkerSerial : Nat := 0
  removed : Bool := false
  deriving Inhabited

/-- Height jitter precedes P_SpawnMobj's lastlook draw, then the duration draw.
Blood size and melee-puff state changes happen last and replace the countdown,
but still consume the original duration draw. -/
def spawn (blood : Bool) (damage : Int32) (melee : Bool)
    (x y z floor ceiling : Fixed) (rng : DoomRandom) : Body × DoomRandom := Id.run do
  let (jitter,rng) := rng.subPlay
  let (look,rng) := rng.nextPlay
  let (duration,rng) := rng.nextPlay
  let mut frame := if blood then BLOOD1 else PUFF1
  let mut tics : Int32 := max 1 ((if blood then 8 else 4)-Int32.ofNat (duration &&& 3))
  if blood && damage ≤ 12 then
    frame := if damage ≥ 9 then BLOOD2 else BLOOD3
    tics := 8
  else if !blood && melee then
    frame := PUFF3
    tics := 4
  let jittered := z + (⟨Int32.ofInt jitter <<< 10⟩ : Fixed)
  -- P_SpawnMobj interprets these sentinels after the wrapping height jitter.
  let height := Fixed.ofInt 16
  let z := if jittered.raw == -2147483648 then floor
    else if jittered.raw == 2147483647 then ceiling-height else jittered
  let motion : Motion := {
    x, y, z,
    momz := Fixed.ofInt (if blood then 2 else 1),
    floorz := floor, ceilingz := ceiling, height,
    noGravity := !blood }
  return ({ motion, frame, tics, lastlook := look%4 },rng)

/-- P_MobjThinker: vertical movement precedes the state countdown. These objects
have no XY momentum, player, float, skull-fly, missile, or count-kill flags. -/
def tick (b : Body) : Except String Body := do
  if b.removed then return b
  let mut m := b.motion
  if m.z != m.floorz || m.momz.raw != 0 then
    m := { m with z := m.z+m.momz }
    if m.z.raw ≤ m.floorz.raw then
      m := { m with z := m.floorz, momz := ⟨max 0 m.momz.raw⟩ }
    else if !m.noGravity then
      m := { m with momz := if m.momz.raw == 0 then ⟨-131072⟩ else m.momz-Fixed.ofInt 1 }
    if (m.z+m.height).raw > m.ceilingz.raw then
      m := { m with z := m.ceilingz-m.height, momz := ⟨min 0 m.momz.raw⟩ }
  let mut b := { b with motion := m, tics := b.tics-1 }
  if b.tics == 0 then
    let some frame := frames.find? (·.id == b.frame) | throw "impact: unknown state"
    if frame.next == 0 then return { b with removed := true }
    let some next := frames.find? (·.id == frame.next) | throw "impact: unknown next state"
    b := { b with frame := next.id, tics := next.tics }
  return b

end Doom.Impact
