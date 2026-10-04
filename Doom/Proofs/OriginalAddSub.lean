import Doom.Fixed
import Doom.Verification.X86
import Doom.Verification.Doom19
import Doom.Proofs.OriginalMul
import Init.Data.SInt.Lemmas

namespace Doom.Proofs
open Verification X86

/-- All bit patterns, including signed overflow. Result flags are outside scope. -/
theorem fixed_add_matches_doom19 (a b : Fixed) :
    (run 1 Doom19.addBytes (originalMulInputs a b)).map (fun r => r eax) =
      some (a + b).raw.toBitVec := by rfl

theorem fixed_sub_matches_doom19 (a b : Fixed) :
    (run 1 Doom19.subBytes (originalMulInputs a b)).map (fun r => r eax) =
      some (a - b).raw.toBitVec := by rfl

end Doom.Proofs
