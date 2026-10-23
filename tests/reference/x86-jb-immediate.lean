import Doom.Verification.X86Routine
open Doom.Verification X86 X86Memory X86Control
set_option maxRecDepth 32768
example : ∀ d : Fin 256,
    X86Routine.decode [0x72,UInt8.ofNat d.val,0x90] =
      some (.jumpUnsigned 0 (UInt8.ofNat d.val).toBitVec.toInt,[0x90]) := by decide
example : X86Routine.decode [0x72]=none := by decide
/-- The two possible carry values control the unsigned-below branch. -/
example (s : X86Memory.State) (z sign ov : Bool) (carry : Bool) :
    X86Routine.execute (.jumpUnsigned 0 (-16)) ⟨s,some ⟨z,sign,ov,some carry⟩,32⟩=
      some ⟨s,some ⟨z,sign,ov,some carry⟩,if carry then 16 else 32⟩ := by
  cases carry <;> rfl
example (s : X86Memory.State) :
    X86Routine.execute (.jumpUnsigned 0 16) ⟨s,none,32⟩=none := rfl
