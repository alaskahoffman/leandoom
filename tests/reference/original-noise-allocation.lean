import Doom.Proofs.E1M1NoiseAllocation
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
namespace Doom.Verification.NoiseAllocationFixture
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
      (other+66,6),(other+18,0),
      (origin+78,2),(origin+82,0x600b01),(0x600b01,wall),(0x600b05,wall),
      (wall+16,4),(wall+22,65536),(wall+46,origin),(wall+50,origin),
      (sides+14,origin),(sides+32,origin)] : List (Word × Word)).foldl
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

theorem child : CheckedTrace (E1M1NoiseMapGuards.layout table) .sector called childEnd
    (E1M1NoiseFootprint.sectorWrites called.core) 0 := by
  have count : charge called.core=0 := by decide +kernel
  simpa only [count,childEnd] using CheckedTrace.sectorDone called (by decide +kernel) child_safe

theorem below : BelowFrame table called.core (E1M1NoiseFootprint.sectorWrites called.core) := by
  intro b hb
  simp only [E1M1NoiseFootprint.sectorWrites,List.drop,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl <;>
    apply Or.inr <;> apply Or.inl <;> refine ⟨mainSector,by simp [table],?_⟩ <;>
    simp only [Region.Contains,sectorRegion] <;> decide +kernel

example : Restored called.core childEnd := allocated.restores child child_room (by decide +kernel) below

theorem resumed : MapRep table (advance childEnd).core.memory ∧ Cursor mainSector (advance childEnd).core ∧
    E1M1NoiseLineProgress.remaining (advance childEnd)+1=E1M1NoiseLineProgress.remaining parent :=
  allocated.child_step parent_room (by simp [table]) started.1 started.2.1 (by decide +kernel)
    child child_room (by decide +kernel) below
    (allocated.map_sector child_room (by decide +kernel)) (by decide +kernel)
example : (NoiseTraversal.selected (advance childEnd).core).regs 2=wall :=
  resumed.2.1.selected (resumed.1 mainSector (by simp [table]))

-- Exact adjacency is safe; a one-byte overlap is not. No alignment assumption.
example : (Region.mk 101 105).Disjoint (Region.mk 105 109) := by decide +kernel
example : ¬(Region.mk 101 105).Disjoint (Region.mk 104 108) := by decide +kernel
example : ¬(Region.mk 4294967293 4294967297).Contains (4294967293#32) := by decide +kernel
end Doom.Verification.NoiseAllocationFixture
