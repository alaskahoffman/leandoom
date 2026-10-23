/- Shared P_DamageMobj thrust branch, pinned Chocolate Doom 3.1.1 p_inter.c.
Derived from id Software / Simon Howard. GPL-2.0-or-later. -/
import Doom.Angles
import Doom.Random

namespace Doom.DamageThrust

structure Position where
  x : Fixed := ⟨0⟩
  y : Fixed := ⟨0⟩
  z : Fixed := ⟨0⟩
  deriving Inhabited

/-- Call after the shootable/alive/skill gates. Mass is positive original actor
metadata; damage is nonnegative. Preserve intermediate signed 32-bit products,
the strict fall-forward gates, and the conditional RNG draw before damage. -/
def apply (target : Position) (health damage mass : Int32) (momx momy : Fixed)
    (inflictor : Option Position) (noClip chainsaw : Bool) (rng : DoomRandom)
    : Fixed × Fixed × DoomRandom := Id.run do
  let some inflictor := inflictor | return (momx,momy,rng)
  if noClip || chainsaw then return (momx,momy,rng)
  let mut rng := rng
  let mut angle := Angle.between inflictor.x inflictor.y target.x target.y
  let mut thrust : Fixed := ⟨(damage * 8192 * 100) / mass⟩
  if damage < 40 && damage > health && (target.z-inflictor.z).raw > 64*65536 then
    let (roll,next) := rng.nextPlay
    rng := next
    if roll &&& 1 != 0 then
      angle := ⟨angle.raw + 0x80000000⟩
      thrust := ⟨thrust.raw * 4⟩
  return (momx + thrust*angle.fineCosine,momy + thrust*angle.fineSine,rng)

end Doom.DamageThrust
