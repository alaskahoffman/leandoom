/- Player branch of DOOM 1.9 P_DamageMobj, derived from pinned Chocolate Doom
3.1.1 p_inter.c. GPL-2.0-or-later. See COPYING.md.
Death/state entry are explicit results, applied by the runtime in original order. -/
import Doom.Angles
import Doom.Random
import Doom.DamageThrust

namespace Doom.PlayerDamage

abbrev Inflictor := DamageThrust.Position

structure State where
  x : Fixed := ⟨0⟩
  y : Fixed := ⟨0⟩
  z : Fixed := ⟨0⟩
  momx : Fixed := ⟨0⟩
  momy : Fixed := ⟨0⟩
  momz : Fixed := ⟨0⟩
  health : Int32 := 100
  playerHealth : Int32 := 100
  armor : Int32 := 0
  armorType : Int32 := 0
  damageCount : Int32 := 0
  shootable : Bool := true
  skullFly : Bool := false
  noClip : Bool := false
  god : Bool := false
  invulnerable : Bool := false
  sectorSpecial : Int32 := 0
  deriving Inhabited

structure Result where
  state : State
  rng : DoomRandom
  /-- The original reached player health/attacker bookkeeping (even at zero damage). -/
  applied : Bool := false
  killed : Bool := false
  pain : Bool := false
  deriving Inhabited

/-- Surviving accepted damage clears the actor's movement reaction delay.
Rejected and lethal damage never reaches this tail of P_DamageMobj. -/
def Result.reactionTime (result : Result) (before : Int32) : Int32 :=
  if result.applied && !result.killed then 0 else before

/-- The shared armor stage. Returns the updated player and damage remaining
for health bookkeeping; depletion clears the armor type on equality too. -/
def absorbArmor (s : State) (damage : Int32) : State × Int32 :=
  if s.armorType != 0 then
    let saved := min (damage / (if s.armorType == 1 then 3 else 2)) s.armor
    ({s with armor := s.armor-saved,
             armorType := if s.armor ≤ saved then 0 else s.armorType}, damage-saved)
  else (s,damage)

/-- Player bookkeeping after armor. Both arithmetic operations wrap before
the signed clamps, just as in the original executable. -/
def bookkeep (s : State) (damage : Int32) : State :=
  { s with playerHealth := max 0 (s.playerHealth-damage),
           damageCount := min 100 (s.damageCount+damage) }

/-- Damage after entry/protection checks; shared with the entry correspondence
proof so health, pain and death continue through the actual live routine. -/
def finish (state : State) (damage : Int32) (rng : DoomRandom) : Result := Id.run do
  let mut s := state
  let mut damage := damage
  let (armored,remaining) := absorbArmor s damage
  s := armored
  damage := remaining
  s := bookkeep s damage
  s := { s with health := s.health-damage }
  if s.health ≤ 0 then return ⟨s,rng,true,true,false⟩
  let (roll,next) := rng.nextPlay
  return ⟨s,next,true,false,roll < 255 && !s.skullFly⟩


/-- Normal DOOM player metadata: mass 100, painchance 255. Skill and chainsaw
gates are explicit inputs; arbitrary source/target identities stay in the host.
Nonnegative damage is the supported gameplay domain. Integer operations wrap. -/
def apply (state : State) (damage : Int32) (inflictor : Option Inflictor)
    (chainsaw : Bool) (baby : Bool) (rng : DoomRandom) : Result := Id.run do
  let mut s := state
  let mut rng := rng
  if !s.shootable || s.health ≤ 0 then return ⟨s,rng,false,false,false⟩
  if s.skullFly then s := { s with momx := ⟨0⟩, momy := ⟨0⟩, momz := ⟨0⟩ }
  let mut damage := if baby then damage >>> 1 else damage
  let (mx,my,nextRng) := DamageThrust.apply ⟨s.x,s.y,s.z⟩ s.health damage 100
    s.momx s.momy inflictor s.noClip chainsaw rng
  rng := nextRng
  s := { s with momx := mx, momy := my }
  if s.sectorSpecial == 11 && damage ≥ s.health then damage := s.health-1
  if damage < 1000 && (s.god || s.invulnerable) then return ⟨s,rng,false,false,false⟩
  return finish s damage rng

end Doom.PlayerDamage
