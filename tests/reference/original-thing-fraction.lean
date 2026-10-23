import Doom.Proofs.E1M1ThingFraction
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
namespace ThingFractionFixture
-- Synthetic diagnostics, not a claim of reachable E1M1 states. SP=1 wraps saves.
def machine (dx dy x y radius : Word) : X86Memory.State :=
  ⟨fun r => if r=1 then 0x700401 else if r=4 then 1 else 0,
    ([(0x2ba10,0),(0x2ba14,0),(0x2ba18,dx),(0x2ba1c,dy),(0x2c028,0x2ba20),
      (0x70040d,x),(0x700411,y),(0x700441,radius)] : List (Word × Word)).foldl
      (fun m (a,v) => store32 m a v) (fun _ => 0)⟩
def run (s : X86Memory.State) := E1M1ThingFraction.continueFraction (OriginalThingSecondSide.crossing s)
theorem positive_fraction : let out := run (machine 65536 131072 65536 131072 65536)
    out.pc=0x2c7e4 ∧ out.core.regs 0=65536 ∧ out.core.regs 4=1 ∧
    out.core.regs 1=0x700401 ∧ load32 out.core.memory 0x2c028=0x2ba20 := by decide +kernel
example : let out := run (machine 65536 131072 4294901760 4294836224 65536)
    out.pc=0x2c7da ∧ out.core.regs 0=1 ∧ out.core.regs 4=1 := by decide +kernel
-- A fraction of zero is accepted; the rejection comparison is strictly negative.
example : let out := run (machine 65536 131072 0 0 65536)
    out.pc=0x2c7e4 ∧ out.core.regs 0=0 := by decide +kernel
example : let out := run (machine 65536 131072 196608 131072 65536)
    out.pc=0x2c805 ∧ out.core.regs 0=1 := by decide +kernel
example : let out := run (machine 0 65536 0 131072 65536)
    out.pc=0x2c7e4 ∧ out.core.regs 0=131072 := by decide +kernel
example : let out := run (machine 65536 0 196608 0 65536)
    out.pc=0x2c7e4 ∧ out.core.regs 0=196608 := by decide +kernel
-- Direct helper-entry diagnostic: parallel diagonal takes the zero-denominator path.
def parallel : X86Memory.State :=
  ⟨fun r => if r=4 then 1 else if r=5 then 65536 else 0,
    ([(0x2ba10,0),(0x2ba14,0),(0x2ba18,65536),(0x2ba1c,65536),(21,65536)] : List (Word × Word)).foldl
      (fun m (a,v) => store32 m a v) (fun _ => 0)⟩
example : let out := OriginalThingFraction.result parallel
    out.pc=0x2c7e4 ∧ out.core.regs 0=0 ∧ out.core.regs 4=1 := by decide +kernel
#print axioms positive_fraction
end ThingFractionFixture
