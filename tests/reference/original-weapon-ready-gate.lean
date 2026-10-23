import Doom.Proofs.E1M1WeaponReadyGate
namespace Doom.Verification.ReadyGateFixture
open Doom Doom.Proofs X86 X86Memory X86Control

def initial (pending health weapon latch : Word) (attack : BitVec 8) : X86Memory.State :=
  ⟨fun r => if r=1 then 0x600041 else if r=4 then 1 else 0,
   fun a => if a=0x600050 then attack else
     (store32 (store32 (store32 (store32 (fun _ => 0) 0x6000b5 pending)
       0x600061 health) 0x6000b1 weapon) 0x6000fd latch) a⟩

-- Unaligned player fields, wrapping call stack, and nonzero attack latch.
example : WeaponReadyGate.Inputs (initial 10 100 1 7 0) 1 9 100 false := by
  constructor <;> decide
example : WeaponReadyGate.Inputs (initial 2 0 2 7 1) 2 2 0 true := by
  constructor <;> decide
example : (WeaponReadyGate.result (initial 10 100 1 7 0)).pc=0x2d392 := by decide
example : (WeaponReadyGate.result (initial 10 100 2 7 1)).pc=0x2d410 := by decide
example : (WeaponReadyGate.result (initial 10 0 1 7 1)).pc=0x2d040 := by decide
example : (WeaponReadyGate.result (initial 2 100 1 7 1)).pc=0x2d040 := by decide
example : (WeaponReadyGate.result (initial 10 100 4 7 1)).pc=0x2d39c := by decide
example : (WeaponReadyGate.result (initial 10 100 6 7 1)).pc=0x2d39c := by decide
example : (WeaponReadyGate.result (initial 10 100 4 0 1)).pc=0x2d410 := by decide
example : (WeaponReadyGate.result (initial 10 100 2 7 1)).core.regs 4=0xfffffffd := by decide
example : load32 (WeaponReadyGate.result (initial 10 100 2 7 1)).core.memory 0xfffffffd=0x2d38d := by decide
example : load32 (WeaponReadyGate.result (initial 10 100 2 7 1)).core.memory 0x6000fd=1 := by decide
example : ∃ n, n≤39 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1WeaponReadyGate.program [] n
    ⟨initial 10 100 1 7 0,none,0x2d333⟩ (WeaponReady.result (initial 10 100 1 7 0)) :=
  E1M1WeaponReadyGate.idle_execution _ _ (by decide) (by decide)
end Doom.Verification.ReadyGateFixture
