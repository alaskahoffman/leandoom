import Doom.Proofs.E1M1LineSetup
import Doom.Proofs.OriginalRandom
namespace Doom.Verification.LineSetupFixture
open X86 X86Memory X86Control Doom.Proofs OriginalLineSetup
-- The value-only and byte-memory interpreters coexist in this compilation.
example (a b : Doom.Fixed) :
    X86ValueRoutine.resultWord (X86ValueRoutine.run Doom19.fixedDivBytes 40 (divisionInputs a b)) =
      some (divisionAnswer (Doom.Fixed.divChecked a b)) := fixed_div_matches_doom19 a b

def source : Memory :=
  X86Routine.store16 (X86Routine.store16 (X86Routine.store16 (fun _ => 0) 0x1004 0x1234) 0x1006 0xabcd) 0x1008 0x9876
def raw (line : Word) : X86Memory.State :=
  ⟨fun r => if r=0 then 0xfeedffff else if r=1 then 0x1000 else if r=3 then line else 0,source⟩
example : load16 (metadata (raw 0x2000)).memory 0x2010=0x1234 ∧
    load16 (metadata (raw 0x2000)).memory 0x2012=0xabcd ∧
    load16 (metadata (raw 0x2000)).memory 0x2014=0x9876 ∧
    (metadata (raw 0x2000)).regs 0=0xfeed9876 := by decide +kernel
-- First destination aliases the later tag source: preserving read order matters.
example : load16 (metadata (raw 0xff8)).memory 0x100c=0x1234 := by decide +kernel

def lineState (x y stack : Word) : X86Memory.State :=
  ⟨fun r => if r=3 then 0x2000 else if r=4 then stack else 0,
    store32 (store32 (fun _ => 0) 0x2008 x) 0x200c y⟩
example : (selected (lineState 0 0 0x3000)).pc=0x2e326 ∧
    load32 (selected (lineState 0 0 0x3000)).core.memory 0x202a=1 := by decide +kernel
example : (selected (lineState 1 0 0x3000)).pc=0x2e326 ∧
    load32 (selected (lineState 1 0 0x3000)).core.memory 0x202a=0 := by decide +kernel
example : (selected (lineState 0xffffffff 1 2)).pc=0x1d180 ∧
    (selected (lineState 0xffffffff 1 2)).core.regs 4=0xfffffffe ∧
    load32 (selected (lineState 0xffffffff 1 2)).core.memory 0xfffffffe=0x2e312 := by decide +kernel
example : load32 (classified (put (lineState 1 1 0x3000) 0 0)).core.memory 0x202a=3 := by decide +kernel
example : load32 (classified (put (lineState 1 1 0x3000) 0 1)).core.memory 0x202a=2 := by decide +kernel
example : load32 (classified (put (lineState 1 1 0x3000) 0 0x80000000)).core.memory 0x202a=3 := by decide +kernel
end Doom.Verification.LineSetupFixture
