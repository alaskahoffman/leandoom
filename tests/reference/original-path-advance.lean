import Doom.Proofs.E1M1FiringAdvance
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open E1M1PathAdvance
namespace PathAdvanceFixture
-- A stack that crosses the 32-bit address boundary; no alignment assumption.
def machine (g : Cell) (sp : Word) : X86Memory.State :=
  ⟨fun r => if r=1 then g.mapY else if r=4 then sp else if r=5 then g.xi
    else if r=6 then g.mapX else if r=7 then g.count else 0x12345678,
    ([(20,g.endX),(24,g.endY),(28,g.yDirection),(32,g.xDirection),
      (36,g.xStride),(40,g.yStride),(44,g.yi)] : List (Word × Word)).foldl
      (fun m (off,v) => store32 m (sp+off) v) (fun _ => 0)⟩
def base : Cell := ⟨3,4,9,8,0x30000,0x40000,1,0xffffffff,0xffff0000,0x18000,0⟩
-- Both tests match: X wins, leaving Y and xi unchanged.
example : let out := OriginalPathAdvance.result (machine base 0xffffffe1)
    numeric (observe out.core)=(4,4,0x30000,0x58000) ∧
    out.core.regs 7=1 ∧ out.pc=0x2ca7f := by decide +kernel
-- X fails, Y matches; signed direction and stride are used.
example : let out := OriginalPathAdvance.result (machine {base with yi:=0x60000} 1)
    numeric (observe out.core)=(3,3,0x20000,0x60000) ∧
    out.core.regs 7=1 ∧ out.pc=0x2ca7f := by decide +kernel
-- A stall changes no coordinate/intercept, but consumes the final iteration.
example : let out := OriginalPathAdvance.result (machine {base with xi:=0x70000,yi:=0x60000,count:=63} 0xfffffff1)
    numeric (observe out.core)=(3,4,0x70000,0x60000) ∧
    out.core.regs 7=64 ∧ out.pc=0x2cafd := by decide +kernel
-- Final iteration still executes its axis update before the budget exit.
example : let out := OriginalPathAdvance.result (machine {base with count:=63} 3)
    numeric (observe out.core)=(4,4,0x30000,0x58000) ∧
    out.core.regs 7=64 ∧ out.pc=0x2cafd := by decide +kernel
-- Endpoint exit precedes matching axis tests and the increment.
example : let out := OriginalPathAdvance.result (machine {base with endX:=3,endY:=4,count:=63} 1)
    numeric (observe out.core)=(3,4,0x30000,0x40000) ∧
    out.core.regs 7=63 ∧ out.pc=0x2cafd := by decide +kernel
-- Arithmetic shift floors negative intercepts; additions wrap at 32 bits.
example : let g := {base with mapX:=0xffffffff,mapY:=0xffffffff,xi:=0,yi:=0xffff0001,yStride:=0x20000,xDirection:=1}
    let out := OriginalPathAdvance.result (machine g 0xffffffe1)
    numeric (observe out.core)=(0,0xffffffff,0,0x10001) ∧ out.pc=0x2ca7f := by decide +kernel
-- The numeric Int32/Fixed fragment uses the same X-first rule.
example : productionAxis 3 4 ⟨0x30000⟩ ⟨0x40000⟩ 1 (-1) ⟨-65536⟩ ⟨0x18000⟩ =
    (4,4,⟨0x30000⟩,⟨0x58000⟩) := by decide +kernel
end PathAdvanceFixture
