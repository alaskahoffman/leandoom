import Doom.Proofs.E1M1NoiseTermination
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
namespace Doom.Verification.NoiseTerminationFixture
open Doom Doom.Proofs X86 X86Memory X86Control E1M1NoiseAllocation E1M1NoiseMap
open E1M1NoiseLedger E1M1NoiseAccounting E1M1NoisePreservation E1M1NoiseStack
open E1M1NoiseGraph E1M1NoiseGraphAllocation E1M1NoiseTermination

def origin : Word := 0x600101
def other : Word := 0x600201
def wall : Word := 0x601001
def sides : Word := 0x600801
-- A has two links to B; B links back to A. Both start unvisited.
-- All objects and the stack are deliberately unaligned.
def initial : X86Control.State :=
  ⟨⟨fun r => if r=0 then origin else if r=2 then 0 else if r=4 then 0x700101 else BitVec.ofNat 32 (10+r.val),
    ([(0x13580,7),(0x2b958,0x600d01),(0x2c118,sides),(0x700101,0x28000),
      (origin,0),(origin+4,128),(origin+66,6),(origin+18,0),(origin+22,0),
      (other,0),(other+4,128),(other+66,6),(other+18,0),(other+22,0),
      (origin+78,2),(origin+82,0x600b01),(0x600b01,wall),(0x600b05,wall),
      (other+78,1),(other+82,0x600b11),(0x600b11,wall),
      (wall+16,4),(wall+22,65536),(wall+46,origin),(wall+50,other),
      (sides+14,origin),(sides+32,other)] : List (Word × Word)).foldl
      (fun m p => store32 m p.1 p.2) (fun _ => 0)⟩,none,0x26f60⟩
def mainSector : SectorLines := ⟨origin,0x600b01,[wall,wall]⟩
def otherSector : SectorLines := ⟨other,0x600b11,[wall]⟩
def table := [mainSector,otherSector]
def arena : Region := ⟨0x70007d,0x700105⟩
def edge : Edge := ⟨wall,4,0,1,origin,other⟩
def edges := [edge]
def regions : List Region := [⟨0x2c118,0x2c11c⟩,⟨0x601001,0x601037⟩,⟨0x600801,0x600825⟩]
def ledger : Ledger := [(origin,.unseen),(other,.unseen)]

theorem allocated : Allocation table arena := by
  constructor <;> simp [table,mainSector,otherSector,origin,other,wall,arena,sectorRegion,arrayRegion,
    globals,counter,Region.Disjoint]
theorem stored : Storage table arena sides edges regions := by
  constructor <;> simp [graphReads,edgeReads,edge,edges,regions,Region.Contains,Region.Disjoint,
    sideAddress,sides,wall,origin,other,table,mainSector,otherSector,arena,sectorRegion,globals]
theorem represented : MapRep table initial.core.memory := by
  intro e he
  simp only [table,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl <;> constructor <;> decide +kernel
theorem graph_initial : GraphRep sides edges initial.core.memory := by
  constructor
  · decide +kernel
  · intro e he
    have eq : e=edge := List.mem_singleton.mp he
    subst e
    constructor
    all_goals first | decide +kernel | { intro _; decide +kernel }
theorem ledger_initial : Represents (7#32) initial.core.memory ledger := by
  constructor
  · decide +kernel
  · intro p hp
    simp only [ledger,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl <;> unfold E1M1NoiseVisits.Rep <;> decide +kernel

theorem world : World table arena sides edges regions 2 := by
  refine ⟨allocated,stored,?_,?_,?_⟩
  · simp [Bounded,table,mainSector,otherSector]
  · simp [Covered,table,mainSector,otherSector,edges,edge]
  · simp [Closed,edges,edge,E1M1NoiseMapGuards.layout,table,mainSector,otherSector]
theorem ready : Ready table sides edges 7 .sector initial ledger :=
  ⟨rfl,ledger_initial,represented,graph_initial,by unfold Position; decide +kernel,
    by unfold E1M1NoiseCount.Entry E1M1NoiseCount.Legal; decide +kernel⟩

-- Neither a hand-written CheckedTrace nor an eval-success proof is supplied.
theorem generated : ∃ t w n, CheckedTrace (E1M1NoiseMapGuards.layout table) .sector initial t w n :=
  construct world ready (entry_reserve ready (by decide +kernel) (by decide +kernel) (by decide +kernel))
theorem completes : ∃ t, E1M1NoiseRecursive.eval 13 .sector initial=some t ∧
    Restored initial.core t ∧ MapRep table t.core.memory ∧ GraphRep sides edges t.core.memory :=
  sector_total world ready (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem executes : ∃ t, E1M1NoiseRecursive.Runs (E1M1NoiseRecursive.bound 13) initial t ∧
    Restored initial.core t ∧ MapRep table t.core.memory ∧ GraphRep sides edges t.core.memory :=
  sector_execution world ready (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
example : ∃ t, E1M1NoiseRecursive.eval 13 .sector initial=some t ∧ t.pc=0x28000 := by
  obtain ⟨t,run,restored,_,_⟩ := completes
  exact ⟨t,run,restored.pc.trans (by decide +kernel)⟩
-- The first child is admitted, not immediately pruned. The next recursive
-- call points back to its already-visited parent. These checks ensure the
-- fixture really exercises recursive construction, rather than a trivial RET.
def parent := startLines initial
def called := dispatch parent
example : called.pc=0x26f60 ∧ called.core.regs 0=other ∧ (sector called).pc=0x26fa6 := by decide +kernel
example : (dispatch (startLines called)).core.regs 0=origin ∧
    (sector (dispatch (startLines called))).pc=0x27011 := by decide +kernel
end Doom.Verification.NoiseTerminationFixture
