import Doom.Verification.X86ReturnCleanup
import Doom.Proofs.E1M1AimTraversalReturn
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
namespace Doom.Proofs.OriginalPathReturn
open Verification X86 X86Memory X86Control BlockSummary
attribute [local irreducible] load32 store32

def code : List UInt8 := [0xc2,8,0]
def bytesProgram (bytes : List UInt8) : X86ReturnCleanup.Program := fun pc =>
  if 0x2cb11≤pc ∧ pc<0x2cb14 then X86ReturnCleanup.decodeAt bytes (pc-0x2cb11) else none
def program := bytesProgram code
def result (s : X86Memory.State) (f : Option Flags) : X86Control.State :=
  X86ReturnCleanup.returned 8 ⟨s,f,0x2cb11⟩

theorem decoded : program 0x2cb11=some (.retCleanup 8,3) := by decide

theorem execution (cm : Memory) (s : X86Memory.State) (f : Option Flags) :
    X86ReturnCleanup.Prefix cm program [] 1 ⟨s,f,0x2cb11⟩ (result s f) := by
  exact .step (op := .retCleanup 8) (length := 3) (by simp) decoded (by rfl) (.nil _)

theorem layout (s : X86Memory.State) (f : Option Flags) :
    (result s f).pc=(load32 s.memory (s.regs 4)).toNat ∧
    (result s f).core.regs 4=s.regs 4+12 ∧
    (result s f).core.memory=s.memory ∧ (result s f).flags=f ∧
    (∀ r, r≠4 → (result s f).core.regs r=s.regs r) := by
  simp [result,X86ReturnCleanup.returned,put,write,BitVec.add_assoc]; intro r h; simp [h]
end Doom.Proofs.OriginalPathReturn
