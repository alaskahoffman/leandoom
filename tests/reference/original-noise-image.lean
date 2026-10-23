import Doom.Proofs.E1M1NoiseImage
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
namespace Doom.Verification.NoiseImageFixture
open Doom Doom.Proofs X86 X86Memory X86Control E1M1NoiseAllocation E1M1NoiseMap
open E1M1NoiseLedger E1M1NoisePreservation E1M1NoiseGraph E1M1NoiseGraphAllocation
open E1M1NoiseTopology E1M1NoiseImage

def topo : Topology := ⟨[[0,1],[0,1]],[0,1],[⟨0,4,0,1,0,1⟩,⟨1,4,1,0,1,0⟩]⟩
def addr : Addresses := ⟨fun i => 0x600101+BitVec.ofNat 32 (256*i),
  fun i => 0x601001+BitVec.ofNat 32 (64*i),fun i => 0x600b01+BitVec.ofNat 32 (16*i)⟩
def table := topo.table addr
def sides : Word := 0x600801
def edges := topo.edges addr
def arena : Region := ⟨0x70007d,0x700105⟩
def regions : List Region := [⟨0x2c118,0x2c11c⟩,⟨0x601001,0x601080⟩,⟨0x600801,0x600825⟩]
def plan := freshImage table sides edges 7 0
-- Unspecified memory is conspicuously nonzero, not an implicit zero image.
def before : X86Control.State :=
  ⟨⟨fun r => if r=0 then addr.sector 0 else if r=2 then 0 else if r=4 then 0x700101 else 0,
      store32 (fun _ => 0xaa) 0x700101 0x28000⟩,none,0x26f60⟩
def after := initialized table sides edges 7 0 before

theorem certified : Certified topo 2 := by constructor <;> decide +kernel
-- Both edges share both side-pointer cells. Equal repeated writes are legal.
theorem consistent : Consistent plan := by decide +kernel

theorem image_relations : MapRep table after.core.memory ∧ GraphRep sides edges after.core.memory ∧
    Represents 7 after.core.memory (freshLedger table) :=
  initializes_fresh table sides edges 7 0 (by decide) consistent before.core.memory

example : load32 after.core.memory (addr.sector 0+78)=2 ∧
    load32 after.core.memory (addr.sector 0+82)=addr.array 0 ∧
    load32 after.core.memory (addr.array 0+4)=addr.line 1 := by decide +kernel
example : load16 after.core.memory (addr.line 1+22)=1 ∧
    load16 after.core.memory (addr.line 1+24)=0 ∧
    load32 after.core.memory (sideAddress sides 0)=addr.sector 0 := by decide +kernel
-- The flags high byte and old sound cost are outside this sparse initializer.
example : after.core.memory (addr.line 0+17)=0xaa ∧
    load32 after.core.memory (addr.sector 0+18)=0xaaaaaaaa := by decide +kernel
example : after.core.memory 0x123456=before.core.memory 0x123456 :=
  frame plan before.core.memory 0x123456 (by decide +kernel)
example : load32 after.core.memory 0x700101=0x28000 := by decide +kernel

theorem allocated : Allocation table arena := by
  constructor <;> simp [table,Topology.table,topo,addr,arena,sectorRegion,arrayRegion,
    globals,counter,Region.Disjoint,List.finRange_succ]
theorem stored : Storage table arena sides edges regions := by
  constructor <;> simp [graphReads,edgeReads,edges,Topology.edges,Line.relocate,topo,regions,
    Region.Contains,Region.Disjoint,sideAddress,sides,addr,table,Topology.table,
    arena,sectorRegion,globals,List.finRange_succ]

-- MapRep, GraphRep and the fresh ledger are outputs of the initializer, not
-- premises of this completion theorem. Physical storage remains certified.
example : ∃ out, E1M1NoiseRecursive.eval 13 .sector after=some out ∧
    Restored after.core out ∧ MapRep table out.core.memory ∧ GraphRep sides edges out.core.memory :=
  E1M1NoiseImage.completes certified addr allocated stored (by decide) consistent
    0 (by decide) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
end Doom.Verification.NoiseImageFixture
