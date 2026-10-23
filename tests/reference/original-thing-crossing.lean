import Doom.Proofs.E1M1ThingCrossing
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
namespace ThingCrossingFixture
-- Synthetic diagnostic states; these are not claims about reachable game states.
-- SP=1 deliberately makes nested stack writes wrap through zero.
def machine (dx dy x y radius : Word) : X86Memory.State :=
  ⟨fun r => if r=1 then 0x700401 else if r=4 then 1 else 0,
    ([(0x2ba10,0),(0x2ba14,0),(0x2ba18,dx),(0x2ba1c,dy),
      (0x70040d,x),(0x700411,y),(0x700441,radius)] : List (Word × Word)).foldl
      (fun m (a,v) => store32 m a v) (fun _ => 0)⟩
theorem same_side_skips : let out := OriginalThingSecondSide.crossing (machine 65536 131072 196608 131072 65536)
    out.pc=0x2c805 ∧ out.core.regs 0=1 ∧ out.core.regs 4=1 ∧
    out.core.regs 1=0x700401 ∧ load32 out.core.memory 17=0 := by decide +kernel
example : let out := OriginalThingSecondSide.crossing (machine 65536 131072 65536 131072 65536)
    out.pc=0x2c7ae ∧ out.core.regs 4=1 := by decide +kernel
example : let out := OriginalThingSecondSide.crossing (machine 65536 4294836224 65536 4294836224 65536)
    out.pc=0x2c7ae ∧ out.core.regs 4=1 := by decide +kernel
-- Equal dx/dy exercises the historical XOR-zero diagonal selection.
example : (OriginalThingSecondSide.crossing (machine 65536 65536 196608 131072 65536)).pc=0x2c805 := by decide +kernel
example : (OriginalThingSecondSide.crossing (machine 0 65536 0 131072 65536)).pc=0x2c7ae := by decide +kernel
example : (OriginalThingSecondSide.crossing (machine 65536 0 196608 0 65536)).pc=0x2c7ae := by decide +kernel
#print axioms same_side_skips
end ThingCrossingFixture
