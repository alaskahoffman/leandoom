import Doom.Motion
import Init.Data.SInt.Lemmas
import Init.Omega

namespace Doom.Proofs

/-- Exact squared raw 16.16 momentum: no floating-point rounding. -/
def speedSquared (body : Motion) : Nat :=
  body.momx.raw.toInt.natAbs * body.momx.raw.toInt.natAbs +
  body.momy.raw.toInt.natAbs * body.momy.raw.toInt.natAbs

/-- The original fixed-point friction multiplier cannot increase the magnitude
of a component, including signed rounding at negative sub-unit velocities. -/
theorem friction_component_contracts (v : Fixed) :
    (v * (⟨0xe800⟩ : Fixed)).raw.toInt.natAbs ≤ v.raw.toInt.natAbs := by
  have lower := v.raw.le_toInt
  have upper := v.raw.toInt_lt
  change (Int32.ofInt ((v.raw.toInt * 59392) / 65536)).toInt.natAbs ≤ v.raw.toInt.natAbs
  rw [Int32.toInt_ofInt]
  have bounded : ((v.raw.toInt * 59392) / 65536).bmod 4294967296 =
      (v.raw.toInt * 59392) / 65536 := by
    apply Int.bmod_eq_of_le <;> omega
  change (((v.raw.toInt * 59392) / 65536).bmod 4294967296).natAbs ≤ v.raw.toInt.natAbs
  rw [bounded]
  omega

/-- Every branch of the real friction function: normal ground friction,
airborne preservation, stop-speed snapping, and no-momentum mode. This is not
a theorem about thrust, collision, knockback or a complete player tic. -/
theorem friction_does_not_accelerate (body : Motion) (cmd : Ticcmd) :
    (body.friction cmd).momx.raw.toInt.natAbs ≤ body.momx.raw.toInt.natAbs ∧
    (body.friction cmd).momy.raw.toInt.natAbs ≤ body.momy.raw.toInt.natAbs := by
  unfold Motion.friction
  split
  · simp
  · split
    · exact ⟨Nat.le_refl _, Nat.le_refl _⟩
    · split
      · simp
      · exact ⟨friction_component_contracts body.momx, friction_component_contracts body.momy⟩

/-- Consequently the squared horizontal speed cannot increase at this stage. -/
theorem friction_speed_squared (body : Motion) (cmd : Ticcmd) :
    speedSquared (body.friction cmd) ≤ speedSquared body := by
  obtain ⟨hx, hy⟩ := friction_does_not_accelerate body cmd
  exact Nat.add_le_add (Nat.mul_le_mul hx hx) (Nat.mul_le_mul hy hy)

end Doom.Proofs
