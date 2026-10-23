import Doom.Proofs.E1M1NoiseTermination
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1NoiseTopology
open Verification X86 X86Memory X86Control E1M1NoiseMap E1M1NoiseGraph E1M1NoiseMapGuards
open E1M1NoiseAllocation E1M1NoiseGraphAllocation E1M1NoiseTermination E1M1NoiseLedger
open E1M1NoisePreservation E1M1NoiseRecursive

/-- Map indices, before the DOS loader chooses addresses. Front/back indices
retain their original 16-bit encoding, including the missing-back sentinel. -/
structure Line where
  index : Nat
  flags : BitVec 8
  frontIndex : BitVec 16
  backIndex : BitVec 16
  front : Nat
  back : Nat
  deriving DecidableEq, Repr

def Line.two (e : Line) : Prop := e.flags &&& (4#8)≠0
instance (e : Line) : Decidable e.two := by unfold Line.two; infer_instance

structure Topology where
  sectors : List (List Nat)
  sides : List Nat
  lines : List Line
  deriving DecidableEq, Repr

/-- Address functions remain parameters: topology certification is independent
of a particular allocator run. Allocation and memory representation are separate. -/
structure Addresses where
  sector : Nat → Word
  line : Nat → Word
  array : Nat → Word

def Line.relocate (e : Line) (a : Addresses) : Edge :=
  ⟨a.line e.index,e.flags,e.frontIndex,e.backIndex,a.sector e.front,a.sector e.back⟩
def Topology.table (t : Topology) (a : Addresses) : List SectorLines :=
  (List.finRange t.sectors.length).map fun i =>
    ⟨a.sector i.val,a.array i.val,(t.sectors[i.val]).map a.line⟩
def Topology.edges (t : Topology) (a : Addresses) : List Edge := t.lines.map (·.relocate a)

def Topology.Coverage (t : Topology) : Prop :=
  ∀ row∈t.sectors, ∀ index∈row, ∃ e∈t.lines, e.index=index
def Topology.Closure (t : Topology) : Prop :=
  ∀ e∈t.lines, e.two → e.front<t.sectors.length ∧ e.back<t.sectors.length
def Topology.Bounded (t : Topology) (limit : Nat) : Prop :=
  ∀ row∈t.sectors, row.length≤limit ∧ row.length≤2147483647

/-- Check side references as signed-compatible indices. Only a missing back
side can use 65535; a two-sided edge must have a represented back sector. -/
def Topology.SideRefs (t : Topology) : Prop :=
  ∀ e∈t.lines, e.frontIndex.toNat<32768 ∧ t.sides[e.frontIndex.toNat]?=some e.front ∧
    (e.backIndex≠65535 → e.backIndex.toNat<32768 ∧ t.sides[e.backIndex.toNat]?=some e.back) ∧
    (e.two → e.backIndex≠65535)

/-- P_GroupLines' per-sector order: scan linedefs in file order, include front
and distinct present back sectors, and include a self-referencing line once. -/
def Topology.Grouped (t : Topology) : Prop :=
  ∀ i : Fin t.sectors.length, t.sectors[i.val]=
    (t.lines.filter fun e => e.front==i.val || (e.backIndex != 65535 && e.back==i.val)).map Line.index

instance (t : Topology) : Decidable t.Coverage := by unfold Topology.Coverage; infer_instance
instance (t : Topology) : Decidable t.Closure := by unfold Topology.Closure; infer_instance
instance (t : Topology) (limit : Nat) : Decidable (t.Bounded limit) := by unfold Topology.Bounded; infer_instance
instance (t : Topology) : Decidable t.SideRefs := by unfold Topology.SideRefs; infer_instance
instance (t : Topology) : Decidable t.Grouped := by unfold Topology.Grouped; infer_instance

structure Certified (t : Topology) (limit : Nat) : Prop where
  coverage : t.Coverage
  closure : t.Closure
  bounded : t.Bounded limit
  sides : t.SideRefs
  grouped : t.Grouped

@[simp] theorem table_length (t : Topology) (a : Addresses) : (t.table a).length=t.sectors.length := by
  simp [Topology.table]

theorem covered {t limit} (h : Certified t limit) (a : Addresses) : Covered (t.table a) (t.edges a) := by
  intro sector member line inLines
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp member
  obtain ⟨index,hi,rfl⟩ := List.mem_map.mp inLines
  obtain ⟨e,he,eq⟩ := h.coverage _ (List.getElem_mem i.isLt) index hi
  exact ⟨e.relocate a,List.mem_map.mpr ⟨e,he,rfl⟩,congrArg a.line eq⟩

theorem sector_member (t : Topology) (a : Addresses) (i : Nat) (inside : i<t.sectors.length) :
    a.sector i∈layout (t.table a) := by
  apply List.mem_map.mpr
  refine ⟨⟨a.sector i,a.array i,(t.sectors[i]).map a.line⟩,?_,rfl⟩
  exact List.mem_map.mpr ⟨⟨i,inside⟩,by simp,rfl⟩

theorem closed {t limit} (h : Certified t limit) (a : Addresses) : Closed (t.table a) (t.edges a) := by
  intro edge member two
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp member
  have pair := h.closure e he two
  exact ⟨sector_member t a e.front pair.1,sector_member t a e.back pair.2⟩

theorem bounded {t limit} (h : Certified t limit) (a : Addresses) : E1M1NoiseMap.Bounded (t.table a) limit := by
  intro sector member
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp member
  simpa only [List.length_map] using h.bounded _ (List.getElem_mem i.isLt)

/-- Discharge the map-specific parts of World from the finite certificate.
This does not assume the DOS loader wrote the corresponding words. -/
theorem world {t limit stack base regions} (h : Certified t limit) (a : Addresses)
    (allocation : Allocation (t.table a) stack) (storage : Storage (t.table a) stack base (t.edges a) regions) :
    World (t.table a) stack base (t.edges a) regions limit :=
  ⟨allocation,storage,bounded h a,covered h a,closed h a⟩

/-- Specialize completion to an indexed map, leaving physical memory/ledger
relations explicit. No trace, graph closure or line bound is a caller premise. -/
theorem completes {t limit stack base regions generation s xs} (h : Certified t limit) (a : Addresses)
    (allocation : Allocation (t.table a) stack) (storage : Storage (t.table a) stack base (t.edges a) regions)
    (shape : addresses xs=layout (t.table a)) (ledger : Represents generation s.core.memory xs)
    (map : MapRep (t.table a) s.core.memory) (graph : GraphRep base (t.edges a) s.core.memory)
    (index : Nat) (inside : index<t.sectors.length) (sector : s.core.regs 0=a.sector index)
    (count : s.core.regs 2=0 ∨ s.core.regs 2=1)
    (low : stack.lo+56*t.sectors.length+20≤(s.core.regs 4).toNat)
    (high : (s.core.regs 4).toNat+4≤stack.hi) (bound : stack.hi≤2^32) :
    ∃ out, eval (2*t.sectors.length*(limit+1)+1) .sector s=some out ∧
      Restored s.core out ∧ MapRep (t.table a) out.core.memory ∧ GraphRep base (t.edges a) out.core.memory := by
  have ready : Ready (t.table a) base (t.edges a) generation .sector s xs :=
    ⟨shape,ledger,map,graph,by change s.core.regs 0∈layout (t.table a); rw [sector]; exact sector_member t a index inside,count⟩
  simpa only [table_length] using sector_total (world h a allocation storage) ready
    (by simpa only [table_length] using low) high bound
end Doom.Proofs.E1M1NoiseTopology
