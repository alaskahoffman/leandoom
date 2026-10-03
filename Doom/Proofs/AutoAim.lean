import Doom.AutoAim
import Init.Data.SInt.Lemmas
import Init.Omega

namespace Doom.Proofs

/-- In a nonempty clipped interval inside DOOM's initial ±100/160 slope
window, its exact Int32 midpoint stays inside. Includes negative odd sums,
which truncate toward zero rather than rounding down. -/
theorem autoaim_center_inside (bottom top : Int32)
    (lo : -40960 ≤ bottom.toInt) (ordered : bottom.toInt ≤ top.toInt)
    (hi : top.toInt ≤ 40960) :
    bottom.toInt ≤ (AutoAim.center bottom top).raw.toInt ∧
    (AutoAim.center bottom top).raw.toInt ≤ top.toInt := by
  have sum : (top + bottom).toInt = top.toInt + bottom.toInt := by
    rw [Int32.toInt_add]
    apply Int.bmod_eq_of_le <;> omega
  have mid : bottom.toInt ≤ (top.toInt + bottom.toInt).tdiv 2 ∧
      (top.toInt + bottom.toInt).tdiv 2 ≤ top.toInt := by
    rw [Int.tdiv_eq_ediv]
    simp only [show Int.sign 2 = 1 from rfl]
    split <;> omega
  unfold AutoAim.center
  rw [sum, Int32.toInt_ofInt]
  have unwrapped : ((top.toInt + bottom.toInt).tdiv 2).bmod 4294967296 =
      (top.toInt + bottom.toInt).tdiv 2 := by
    apply Int.bmod_eq_of_le <;> omega
  change bottom.toInt ≤ ((top.toInt + bottom.toInt).tdiv 2).bmod 4294967296 ∧
    ((top.toInt + bottom.toInt).tdiv 2).bmod 4294967296 ≤ top.toInt
  rw [unwrapped]
  exact mid

/-- FixedMul has no wrapping on the autoaim slope/range domain. -/
private theorem aim_mul_exact (slope distance : Int32)
    (lo : -40960 ≤ slope.toInt) (hi : slope.toInt ≤ 40960)
    (near : 0 ≤ distance.toInt) (far : distance.toInt ≤ 67108864) :
    ((⟨slope⟩ : Fixed) * ⟨distance⟩).raw.toInt =
      slope.toInt * distance.toInt / 65536 := by
  have low := Int.mul_le_mul_of_nonneg_right lo near
  have high := Int.mul_le_mul_of_nonneg_right hi near
  change (Int32.ofInt (slope.toInt * distance.toInt / 65536)).toInt = _
  rw [Int32.toInt_ofInt]
  change (slope.toInt * distance.toInt / 65536).bmod 4294967296 = _
  apply Int.bmod_eq_of_le <;> omega

/-- At every distance from 0 to 1024 map units, the chosen ray's vertical
rise lies between the two clipped boundary rays, with exact FixedMul rounding.
This is relative rise, before adding shootZ; not a hit/visibility/traversal proof. -/
theorem autoaim_trajectory_inside (bottom top distance : Int32)
    (lo : -40960 ≤ bottom.toInt) (ordered : bottom.toInt ≤ top.toInt)
    (hi : top.toInt ≤ 40960)
    (near : 0 ≤ distance.toInt) (far : distance.toInt ≤ 67108864) :
    ((⟨bottom⟩ : Fixed) * ⟨distance⟩).raw.toInt ≤
      (AutoAim.center bottom top * ⟨distance⟩).raw.toInt ∧
    (AutoAim.center bottom top * ⟨distance⟩).raw.toInt ≤
      ((⟨top⟩ : Fixed) * ⟨distance⟩).raw.toInt := by
  obtain ⟨lower, upper⟩ := autoaim_center_inside bottom top lo ordered hi
  rw [aim_mul_exact bottom distance lo (by omega) near far,
      aim_mul_exact top distance (by omega) hi near far]
  have center := aim_mul_exact (AutoAim.center bottom top).raw distance
    (by omega) (by omega) near far
  change _ ≤ ((⟨(AutoAim.center bottom top).raw⟩ : Fixed) * ⟨distance⟩).raw.toInt ∧
    ((⟨(AutoAim.center bottom top).raw⟩ : Fixed) * ⟨distance⟩).raw.toInt ≤ _
  rw [center]
  exact ⟨Int.ediv_le_ediv (by decide) (Int.mul_le_mul_of_nonneg_right lower near),
    Int.ediv_le_ediv (by decide) (Int.mul_le_mul_of_nonneg_right upper near)⟩

end Doom.Proofs
