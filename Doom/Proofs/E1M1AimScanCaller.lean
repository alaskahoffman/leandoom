import Doom.Proofs.E1M1AimLineScanStack
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimScanCaller
open Verification X86 X86Memory X86Control BlockSummary Collision
attribute [local irreducible] load32 store32 E1M1AimCompletedReturn.result E1M1AimTraversalReturn.result

/-- A scan with the proved aiming destination can reach a traversal exit only
with the parent's stack. The callback case cannot masquerade as either exit. -/
theorem exit_stack (base : Word) (out : X86Control.State)
    (position : E1M1AimScanStack.Position 0x2b760 base out)
    (exit : out.pc=0x2c887 ∨ out.pc=0x2c88c) : out.core.regs 4=base := by
  rcases position with ⟨_,stack⟩|⟨pc,_⟩
  · exact stack
  · change out.pc=0x2b760 at pc
    rcases exit with exit|exit <;> omega

/-- Append the complete real aiming return to a terminal scan prefix. ESP is
derived from the scan's proved shape, not supplied as a separate endpoint
hypothesis. This does not yet strengthen the enclosing exhaustive-loop theorem. -/
theorem execution (initial : Array Intercept) (resolve : Intercept → Word)
    (start finish : X86Control.State) (base : Word) (steps : Nat) (answer : AimResult)
    (run : X86CodeMemory.Prefix FloorCaller.cm E1M1AimActorSelect.program [] steps start finish)
    (exit : E1M1AimHitMemory.Exit initial resolve finish answer)
    (nonnull : ∀ j<initial.size, resolve initial[j]!≠0)
    (image : E1M1AimSavedCaller.Image start finish base)
    (position : E1M1AimScanStack.Position 0x2b760 base finish)
    (protect : ∀ addr∈E1M1AimSavedCaller.words base, E1M1AimSavedWords.Protect start.core addr)
    (first : load32 start.core.memory (base+20)=0x2cb0b)
    (second : load32 start.core.memory (base+84)=0x2bbff) :
    ∃ n≤steps+21,
      X86ReturnCleanup.Prefix FloorCaller.cm E1M1AimCompletedReturn.program [] n start (E1M1AimCompletedReturn.result finish) ∧
      (E1M1AimCompletedReturn.result finish).core.regs 0=answer.slope.raw.toBitVec ∧
      E1M1AimSavedCaller.Restores start base (E1M1AimCompletedReturn.result finish) := by
  exact E1M1AimSavedCaller.execution initial resolve start finish base steps answer run exit nonnull image
    (exit_stack base finish position exit.1.1) protect first second
end Doom.Proofs.E1M1AimScanCaller
