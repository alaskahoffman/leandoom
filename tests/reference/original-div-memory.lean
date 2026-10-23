import Doom.Proofs.E1M1LineIteration
namespace Doom.Verification.DivMemoryFixture
open X86 X86Memory X86Control Doom.Proofs OriginalDivMemory

def initial (a b sp ret : Word) : X86Memory.State :=
  ⟨fun r => if r=0 then a else if r=1 then 0x11223344 else if r=2 then b else if r=3 then 0x55667788
    else if r=4 then sp else if r=6 then 0x99aabbcc else 0,
    store32 (fun _ => 0x5a) sp ret⟩
example : Safe (initial 1 65536 0x7000 0x2e312) := by unfold Safe DivSafe; decide +kernel
example : Safe (initial 0x80000000 65536 2 0x1d180) := by unfold Safe DivSafe; decide +kernel
example : ¬Safe (initial 0x80000000 0 2 0x2e312) := by unfold Safe DivSafe; decide +kernel
example : ¬Safe (initial 0x80000000 0xffff0000 2 0x2e312) := by unfold Safe DivSafe; decide +kernel
example : (result (initial 1 65536 0x7000 0x2e312)).core.regs 0=1 ∧
    (result (initial 1 65536 0x7000 0x2e312)).core.regs 2=0 ∧
    (result (initial 1 65536 0x7000 0x2e312)).core.regs 1=0x11223344 ∧
    (result (initial 1 65536 0x7000 0x2e312)).core.regs 3=0x55667788 ∧
    (result (initial 1 65536 0x7000 0x2e312)).core.regs 6=0x99aabbcc ∧
    (result (initial 1 65536 0x7000 0x2e312)).core.regs 4=0x7004 ∧
    (result (initial 1 65536 0x7000 0x2e312)).pc=0x2e312 := by decide +kernel
example : (result (initial 0x80000000 65536 2 0x1d180)).core.regs 0=0x80000000 ∧
    (result (initial 0x80000000 65536 2 0x1d180)).core.regs 4=6 ∧
    (result (initial 0x80000000 65536 2 0x1d180)).pc=0x1d180 := by decide +kernel
example : Safe (initial 0xffff0000 1 0x7000 0x2e312) :=
  safe_of_fixed_success _ (by decide +kernel)
-- Both saturation signs, and a genuine truncated zero quotient.
example : (result (initial 65536 1 0x7000 0x2e312)).core.regs 0=0x7fffffff := by decide +kernel
example : (result (initial 0xffff0000 1 0x7000 0x2e312)).core.regs 0=0x80000000 := by decide +kernel
example : (result (initial 1 131072 0x7000 0x2e312)).core.regs 0=0 := by decide +kernel
example : ∃ n≤25, X86Routine.Prefix program [] n ⟨initial 0x80000000 65536 2 0x1d180,none,0x1d180⟩
    (result (initial 0x80000000 65536 2 0x1d180)) :=
  execution_path _ _ (by unfold Safe DivSafe; decide +kernel)
end Doom.Verification.DivMemoryFixture
