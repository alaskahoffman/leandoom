import Doom.Proofs.OriginalGroupLines
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Verification.GroupLinesFixture
open Doom Doom.Proofs X86 X86Memory X86Control BlockSummary OriginalGroupLines E1M1NoiseImage E1M1NoiseTopology

def state (sector array count f b : Word) : X86Memory.State :=
  ⟨fun r => if r=5 then sector else if r=6 then array else 0x12345678,
    store32 (store32 (store32 (store32 (fun _ => 0xaa) 0x2c120 0x600201)
      0x2c134 count) 0x60022f f) 0x600233 b⟩

-- Self-reference follows the front branch, storing one pointer only.
example : (result (state 0x600501 0x600901 475 0x600501 0x600501)).pc=0x2e682 := by decide +kernel
example : load32 (result (state 0x600501 0x600901 475 0x600501 0x600501)).core.memory 0x600901=0x600201 ∧
    load32 (result (state 0x600501 0x600901 475 0x600501 0x600501)).core.memory 0x600905=0xaaaaaaaa := by decide +kernel
example : (result (state 0x600501 0xffffffff 475 0x600700 0x600501)).pc=0x2e682 ∧
    load32 (result (state 0x600501 0xffffffff 475 0x600700 0x600501)).core.memory 0xffffffff=0x600201 := by decide +kernel
example : (result (state 0x600501 0x600901 475 0x600700 0)).pc=0x2e6a2 := by decide +kernel
example : (result (state 0x600501 0x600901 0xffffffff 0x600501 0)).pc=0x2e6af := by decide +kernel

-- The count was loaded before the pointer publication clobbered its global.
example : (result (state (0x2c134-82) 0x600901 0 (0x2c134-82) 0)).pc=0x2e6af ∧
    load32 (result (state (0x2c134-82) 0x600901 0 (0x2c134-82) 0)).core.memory 0x2c134=0x600901 := by decide +kernel
-- Publishing the array can overwrite the current line's front pointer. The
-- subsequent selection reads that updated word, not the original front value.
example : (result (state (0x60022f-82) 0x600901 475 (0x60022f-82) 0)).pc=0x2e6a2 := by decide +kernel
example : (result (state 0x600501 0x600901 475 0x600501 0)).core.regs 6=0x600901 := by decide +kernel
-- Advancing ESI belongs to the later bounding-box continuation, not this store.

example (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x2e682,0x2e6a2,0x2e6af] 11 ⟨s,f,0x2e661⟩=some (result s) := joined_execution s f

def topo : Topology := ⟨[[0,1,2],[0]], [0,1],
  [⟨0,4,0,1,0,1⟩,⟨1,0,0,65535,0,0⟩,⟨2,4,0,0,0,0⟩]⟩
def addr : Addresses := ⟨fun i => if i=0 then 0x600101 else 0x600201,
    fun i => 0x601001+BitVec.ofNat 32 (i*62),fun _ => 0x602001⟩
theorem layout : SectorAddresses addr 2 := by
  constructor
  · intro i hi; by_cases h : i=0 <;> simp [addr,h]
  · intro i hi j hj eq
    by_cases h : i=0 <;> by_cases k : j=0 <;> simp_all [addr] <;> omega
example : (topo.lines.filter fun e => accepts (addr.sector 0) (addr.sector e.front) (backAddress e addr)).map Line.index=[0,1,2] :=
  ordered_selection topo addr layout (by decide +kernel) (by decide +kernel) ⟨0,by decide⟩
example : (topo.lines.filter fun e => accepts (addr.sector 1) (addr.sector e.front) (backAddress e addr)).map Line.index=[0] :=
  ordered_selection topo addr layout (by decide +kernel) (by decide +kernel) ⟨1,by decide⟩

-- A null live sector would falsely match an absent back pointer.
example : accepts 0 1 0=true := by decide +kernel
example : ¬SectorAddresses ⟨fun _ => 0,fun _ => 0,fun _ => 0⟩ 1 := by
  intro h; exact h.nonzero 0 (by decide) rfl
example : ¬SectorAddresses ⟨fun _ => 7,fun _ => 0,fun _ => 0⟩ 2 := by
  intro h; have bad := h.distinct 0 (by decide) 1 (by decide) rfl; contradiction
end Doom.Verification.GroupLinesFixture
