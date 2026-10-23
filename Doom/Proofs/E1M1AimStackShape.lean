import Doom.Proofs.E1M1AimScanCaller
set_option backward.isDefEq.respectTransparency false
namespace Doom.Proofs.E1M1AimStackShape
open Verification X86 X86Memory X86Control
/-- The fixed parent stack base is shared by both loop exits. A live callback
has exactly one additional return word on the stack. -/
def Shape (base : Word) (out : X86Control.State) : Prop :=
  ((out.pc=0x2c887 ∨ out.pc=0x2c88c) ∧ out.core.regs 4=base) ∨
  (out.pc=0x2b760 ∧ out.core.regs 4=base-4)
theorem scan (base : Word) (out : X86Control.State)
    (position : E1M1AimScanStack.Position 0x2b760 base out) : Shape base out := by
  rcases position with ⟨pc,stack⟩|⟨pc,stack⟩
  · exact Or.inl ⟨Or.inl pc,stack⟩
  · exact Or.inr ⟨pc,stack⟩
theorem stopped (base : Word) (out : X86Control.State)
    (pc : out.pc=0x2c88c) (stack : out.core.regs 4=base) : Shape base out :=
  Or.inl ⟨Or.inr pc,stack⟩
theorem terminal (base : Word) (out : X86Control.State) (shape : Shape base out)
    (pc : out.pc=0x2c887 ∨ out.pc=0x2c88c) : out.core.regs 4=base := by
  rcases shape with ⟨_,stack⟩|⟨live,_⟩
  · exact stack
  · rcases pc with pc|pc <;> omega
theorem live (base : Word) (out : X86Control.State) (shape : Shape base out)
    (pc : out.pc=0x2b760) : out.core.regs 4+4=base := by
  rcases shape with ⟨(done|done),_⟩|⟨_,stack⟩
  · omega
  · omega
  · rw [stack,BitVec.sub_add_cancel]
end Doom.Proofs.E1M1AimStackShape
