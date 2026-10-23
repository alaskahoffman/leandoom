import Doom.Proofs.E1M1ThingFirstSide
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
namespace ThingFirstSideFixture
-- Diagnostic states, not assertions that these states are reachable in E1M1.
def machine (dx dy x y radius : Word) : X86Memory.State :=
  ⟨fun r => if r=1 then 0x700401 else if r=4 then 1 else 0,
    ([(0x2ba10,0),(0x2ba14,0),(0x2ba18,dx),(0x2ba1c,dy),
      (0x70040d,x),(0x700411,y),(0x700441,radius)] : List (Word × Word)).foldl
      (fun m (a,v) => store32 m a v) (fun _ => 0)⟩
example : let s := machine 65536 131072 196608 131072 65536
    let out := OriginalThingDiagonal.diagonal s
    out.regs 7=131072 ∧ out.regs 6=196608 ∧ out.regs 5=65536 ∧
    load32 out.memory 21=262144 := by decide +kernel
-- Equal deltas give XOR zero: DOS selects the nonpositive branch.
theorem zero_xor_uses_lower_y :
    (OriginalThingDiagonal.diagonal (machine 65536 65536 196608 131072 65536)).regs 6=65536 := by decide +kernel
example : let out := OriginalThingDiagonal.diagonal (machine 65536 4294836224 196608 131072 65536)
    out.regs 7=131072 ∧ out.regs 6=65536 ∧ out.regs 5=196608 := by decide +kernel
example : let out := OriginalThingDiagonal.diagonal (machine 0 1 2147483647 2147483648 1)
    out.regs 7=2147483646 ∧ out.regs 6=2147483649 ∧ out.regs 5=2147483647 ∧
    load32 out.memory 21=2147483648 := by decide +kernel
example : let out := OriginalThingFirstSide.result (machine 65536 131072 196608 131072 65536)
    out.pc=0x2c78d ∧ out.core.regs 0=0 ∧ out.core.regs 4=1 ∧ out.core.regs 1=0x700401 ∧
    load32 out.core.memory 21=262144 ∧ out.core.regs 5=65536 := by decide +kernel
example : let out := OriginalThingFirstSide.result (machine 65536 4294836224 196608 131072 65536)
    out.pc=0x2c78d ∧ out.core.regs 0=1 ∧ out.core.regs 4=1 := by decide +kernel
example : let out := OriginalThingFirstSide.result (machine 0 65536 196608 131072 65536)
    out.pc=0x2c78d ∧ out.core.regs 0=0 ∧ out.core.regs 4=1 := by decide +kernel
example : let out := OriginalThingFirstSide.result (machine 65536 0 196608 131072 65536)
    out.pc=0x2c78d ∧ out.core.regs 0=1 ∧ out.core.regs 4=1 := by decide +kernel
#print axioms zero_xor_uses_lower_y
end ThingFirstSideFixture
