import Doom.Fire
import Init.Data.SInt.Lemmas
import Init.Omega
namespace Doom.Proofs

/-- A positive signed ammo count can be decremented without wrapping or going
negative. This is about the same discharge function called by Weapon.enter. -/
theorem discharge_spends_one (gun : Fire.Gun) (ammo : Int32)
    (loaded : 0 < ammo.toInt) :
    (Fire.discharge gun ammo).ammoAfter.toInt = ammo.toInt - 1 ∧
    0 ≤ (Fire.discharge gun ammo).ammoAfter.toInt := by
  have upper := ammo.toInt_lt
  have eq : (ammo - 1).toInt = ammo.toInt - 1 := by
    rw [Int32.toInt_sub]
    change (ammo.toInt - 1).bmod 4294967296 = ammo.toInt - 1
    apply Int.bmod_eq_of_le <;> omega
  change (ammo - 1).toInt = ammo.toInt - 1 ∧ 0 ≤ (ammo - 1).toInt
  rw [eq]
  omega

theorem pistol_one_pellet (ammo : Int32) :
    (Fire.discharge .pistol ammo).pellets = 1 := rfl

theorem shotgun_seven_pellets (ammo : Int32) :
    (Fire.discharge .shotgun ammo).pellets = 7 := rfl

/-- Table-path sums, not a proof of the entire partial recursive state machine.
The displayed live intervals are observations, not new proof obligations. -/
theorem pistol_cycle_fourteen : Fire.Gun.pistol.cycleTics = 14 := by decide +kernel
theorem shotgun_cycle_thirty_seven : Fire.Gun.shotgun.cycleTics = 37 := by decide +kernel

end Doom.Proofs
