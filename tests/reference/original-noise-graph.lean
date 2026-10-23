import Doom.Proofs.E1M1NoiseGraph
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
namespace Doom.Verification.NoiseGraphFixture
open Doom Doom.Proofs X86 X86Memory X86Control E1M1NoiseAllocation E1M1NoiseMap
open E1M1NoiseLedger E1M1NoiseAccounting E1M1NoisePreservation
def origin : Word := 0x600101
def other : Word := 0x600201
def wall : Word := 0x601001
def sides : Word := 0x600801
-- Two self-lines exercise child pruning and resumption; every object and the
-- stack are deliberately unaligned. The second sector has no lines.
def initial : X86Control.State :=
  ⟨⟨fun r => if r=0 then origin else if r=2 then 0 else if r=4 then 0x700101 else BitVec.ofNat 32 (10+r.val),
    ([(0x13580,7),(0x2b958,0x600d01),(0x2c118,sides),(0x700101,0x28000),
      (origin,0),(origin+4,128),(origin+66,6),(origin+18,0),(origin+22,0),
      (other+66,6),(other+18,0),(other+4,128),
      (origin+78,2),(origin+82,0x600b01),(0x600b01,wall),(0x600b05,wall),
      (wall+16,4),(wall+22,65536),(wall+46,origin),(wall+50,other),
      (sides+14,origin),(sides+32,other)] : List (Word × Word)).foldl
      (fun m p => store32 m p.1 p.2) (fun _ => 0)⟩,none,0x26f60⟩

def mainSector : SectorLines := ⟨origin,0x600b01,[wall,wall]⟩
def idleSector : SectorLines := ⟨other,0,[]⟩
def table := [mainSector,idleSector]
def arena : Region := ⟨0x700000,0x701000⟩
def parent := startLines initial
def called := dispatch parent
def childEnd := finish (sector called)

theorem allocated : Allocation table arena := by
  constructor <;> simp [table,mainSector,idleSector,origin,other,wall,arena,sectorRegion,arrayRegion,
    globals,counter,Region.Disjoint]

theorem initial_room : StackRoom arena initial.core :=
  stack_room (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem parent_room : StackRoom arena parent.core :=
  stack_room (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem child_room : StackRoom arena called.core :=
  stack_room (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem initial_safe : E1M1NoiseLedger.SectorSafe (E1M1NoiseMapGuards.layout table) initial.core :=
  allocated.ledger_sector initial_room (by decide +kernel) (by decide +kernel)
theorem child_safe : E1M1NoiseLedger.SectorSafe (E1M1NoiseMapGuards.layout table) called.core :=
  allocated.ledger_sector child_room (by decide +kernel) (by decide +kernel)
example : LineSafe (E1M1NoiseMapGuards.layout table) parent.core := allocated.ledger_line parent_room

theorem represented : MapRep table initial.core.memory := by
  intro e he
  simp only [table,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl <;> constructor <;> decide +kernel

theorem started : MapRep table parent.core.memory ∧ Cursor mainSector parent.core ∧
    E1M1NoiseLineProgress.remaining parent≤2 :=
  start_step (table:=table) (limit:=2) (by simp [table]) represented rfl
    (by simp [Bounded,table,mainSector,idleSector])
    (allocated.map_sector initial_room (by decide +kernel)) (by decide +kernel)

open E1M1NoiseGraph

def edge : Edge := ⟨wall,4,0,1,origin,other⟩
def edges := [edge]
local instance (a b : Word) : Decidable (BlockSummary.Apart a b) := by unfold BlockSummary.Apart; infer_instance
local instance (a : Word) (writes : List Word) : Decidable (∀ b, b∈writes → BlockSummary.Apart a b) :=
  List.decidableBAll (BlockSummary.Apart a) writes
local instance (reads writes : List Word) : Decidable (Protect reads writes) :=
  List.decidableBAll (fun a => ∀ b, b∈writes → BlockSummary.Apart a b) reads

theorem graph_initial : GraphRep sides edges initial.core.memory := by
  constructor
  · decide +kernel
  · intro e he
    have eq : e=edge := List.mem_singleton.mp he
    subst e
    constructor
    all_goals first | decide +kernel | { intro _; decide +kernel }

theorem graph_parent : GraphRep sides edges parent.core.memory :=
  graph_initial.sector_step (by decide +kernel)
theorem coverage : Covered table edges := by
  simp [Covered,table,mainSector,idleSector,edges,edge]
theorem closure : Closed table edges := by
  simp [Closed,edges,edge,E1M1NoiseMapGuards.layout,table,mainSector,idleSector]
theorem graph_safe : Protect (graphReads sides edges) (E1M1NoiseFootprint.lineWrites parent.core) := by decide +kernel

example : E1M1NoiseRecursive.OpeningReturns parent.core :=
  E1M1NoiseOpeningFrame.opening_returns allocated parent_room
example : (dispatch parent).core.regs 0∈E1M1NoiseMapGuards.layout table ∧
    ((dispatch parent).core.regs 2=0 ∨ (dispatch parent).core.regs 2=1) :=
  dispatch_child coverage closure (by simp [table]) (started.1 mainSector (by simp [table]))
    started.2.1 graph_parent graph_safe (E1M1NoiseOpeningFrame.allocation_safe allocated parent_room)
    (by decide +kernel) (by decide +kernel)
example : E1M1NoiseLedger.SectorSafe (E1M1NoiseMapGuards.layout table) called.core ∧
    GraphRep sides edges called.core.memory ∧ MapRep table called.core.memory :=
  child_entry (n:=0) allocated (by simp only [E1M1NoiseStack.Reserve,E1M1NoiseStack.need]; decide +kernel)
    coverage closure (by simp [table]) started.1 started.2.1 graph_parent graph_safe
    (by decide +kernel) (by decide +kernel)
example : called.core.regs 0=other ∧ called.core.regs 2=0 := by decide +kernel

-- Exercise both sides of the original current-sector/front-sector comparison.
def neighborState (current : Word) : X86Memory.State :=
  { parent.core with regs := write (write parent.core.regs 2 wall) 3 current }
theorem choose (current : Word) :
    (E1M1NoiseOpening.neighbor (neighborState current)).core.regs 0=
      if current=origin then other else origin := by
  have h := neighbor_choice (s:=neighborState current) (e:=edge) (base:=sides)
    (graph_parent.edges edge (by simp [edges])) graph_parent.pointer rfl (by unfold Edge.two; decide +kernel)
    (by change Protect (edgeReads sides edge) [parent.core.regs 4]; decide +kernel)
  simpa [neighborState,edge,write] using h
example : (E1M1NoiseOpening.neighbor (neighborState origin)).core.regs 0=other := by simpa [origin,other] using choose origin
example : (E1M1NoiseOpening.neighbor (neighborState other)).core.regs 0=origin := by simpa [origin,other] using choose other

-- Blocking lines allow the first crossing, then reject a second crossing.
def blockState (flags count : Word) : X86Memory.State :=
  { parent.core with regs := write parent.core.regs 1 count, memory := store32 parent.core.memory (wall+16) flags }
example : (E1M1NoiseIteration.dispatched (blockState 68 0)).pc=0x26f60 ∧
    (E1M1NoiseIteration.dispatched (blockState 68 0)).core.regs 2=1 := by decide +kernel
example : (E1M1NoiseIteration.dispatched (blockState 68 1)).pc=0x27006 := by decide +kernel
example : (E1M1NoiseIteration.dispatched (blockState 4 1)).pc=0x26f60 ∧
    (E1M1NoiseIteration.dispatched (blockState 4 1)).core.regs 2=1 := by decide +kernel
-- One-sided sentinel and a shut opening cannot dispatch a child.
example : (E1M1NoiseIteration.dispatched { (blockState 0 0) with
    memory := store32 (blockState 0 0).memory (wall+22) 0xffff0000 }).pc=0x27006 := by decide +kernel
example : (E1M1NoiseIteration.dispatched { parent.core with
    memory := store32 parent.core.memory (other+4) 0 }).pc=0x27006 := by decide +kernel

-- Diagnostic signed indices: model the exact MOVSX/18-byte stride, not an
-- unsigned host-language array index. This is not a reachable-WAD claim.
def signedEdge : Edge := ⟨wall,4,0xffff,0xfffe,origin,other⟩
def signedState : X86Memory.State := { (neighborState origin) with memory := store32 (store32 (store32 parent.core.memory (wall+22) 0xfffeffff) (sides-4) origin) (sides-22) other }
theorem signed_rep : EdgeRep sides signedEdge signedState.memory := by
  constructor
  all_goals first | decide +kernel | { intro _; decide +kernel }
example : (E1M1NoiseOpening.neighbor signedState).core.regs 0=other := by
  have h := neighbor_choice (e:=signedEdge) signed_rep (by decide +kernel) rfl
    (by unfold Edge.two; decide +kernel) (by decide +kernel)
  simpa [signedState,neighborState,signedEdge,write] using h
end Doom.Verification.NoiseGraphFixture
