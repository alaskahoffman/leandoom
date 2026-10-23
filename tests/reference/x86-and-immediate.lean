import Doom.Verification.X86Routine
open Doom.Verification X86 X86Routine
-- Every imm8/register encoding, including negative sign-extended immediates.
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
example : ∀ (r : Fin 8) (v : Fin 256),
    X86Routine.decode [0x83,UInt8.ofNat (0xe0+r.val),UInt8.ofNat v.val] =
      some (.andRegister r ((UInt8.ofNat v.val).toBitVec.signExtend 32),[]) := by decide
example : X86Routine.decode [0x83,0x20,3]=none := by decide
example : X86Routine.decode [0x83,0xe0]=none := by decide
example (s : Doom.Verification.X86Control.State) (r : Fin 8) (v : BitVec 8) :
    X86Routine.execute (.andRegister r (v.signExtend 32)) s = some
      ⟨Doom.Verification.X86Memory.put s.core r (s.core.regs r &&& v.signExtend 32),
        some (Doom.Verification.X86Control.logical32 (s.core.regs r &&& v.signExtend 32)),s.pc⟩ := by rfl
