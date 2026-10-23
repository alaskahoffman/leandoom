import Doom.Proofs.E1M1NoiseCount
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
namespace Doom.Verification.NoiseCountFixture
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
      (wall+16,68),(wall+22,65536),(wall+46,origin),(wall+50,origin),
      (sides+14,origin),(sides+32,origin)] : List (Word × Word)).foldl
      (fun m p => store32 m p.1 p.2) (fun _ => 0)⟩,none,0x26f60⟩

def mainSector : SectorLines := ⟨origin,0x600b01,[wall,wall]⟩
def idleSector : SectorLines := ⟨other,0,[]⟩
def table := [mainSector,idleSector]
def arena : Region := ⟨0x70007d,0x700105⟩
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

open E1M1NoiseStack

def after := advance childEnd
def calledAgain := dispatch after
def lastReturn := finish (sector calledAgain)
def result := finish (advance lastReturn)
def childWrites := E1M1NoiseFootprint.sectorWrites called.core
def lastWrites := E1M1NoiseFootprint.sectorWrites calledAgain.core
def tailWrites := E1M1NoiseFootprint.lineWrites after.core++lastWrites
def bodyWrites := E1M1NoiseFootprint.lineWrites parent.core++childWrites++tailWrites
def allWrites := E1M1NoiseFootprint.sectorWrites initial.core++bodyWrites

theorem after_room : StackRoom arena after.core :=
  stack_room (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem again_room : StackRoom arena calledAgain.core :=
  stack_room (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem lastChild : CheckedTrace (E1M1NoiseMapGuards.layout table) .sector calledAgain lastReturn lastWrites 0 := by
  have safe := allocated.ledger_sector again_room (by decide +kernel) (by decide +kernel)
  have count : charge calledAgain.core=0 := by decide +kernel
  simpa only [count,lastReturn,lastWrites] using CheckedTrace.sectorDone calledAgain (by decide +kernel) safe

theorem checked : CheckedTrace (E1M1NoiseMapGuards.layout table) .sector initial result allWrites 1 := by
  have tail := CheckedTrace.childDone after lastReturn _ 0 (by decide +kernel) (by decide +kernel)
    (allocated.ledger_line after_room) lastChild (by decide +kernel) (by decide +kernel)
  have body := CheckedTrace.childMore parent childEnd result _ _ 0 0 (by decide +kernel) (by decide +kernel)
    (allocated.ledger_line parent_room) child (by decide +kernel) (by decide +kernel) tail
  have count : charge initial.core=1 := by decide +kernel
  simpa only [count,Nat.zero_add,allWrites,bodyWrites,tailWrites,childWrites] using
    CheckedTrace.sectorMore initial result _ 0 (by decide +kernel) initial_safe body

def ledger : Ledger := [(origin,.unseen),(other,.unseen)]
theorem ledger_rep : Represents (7#32) initial.core.memory ledger := by
  constructor
  · decide +kernel
  · intro p hp
    simp only [ledger,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl <;> unfold E1M1NoiseVisits.Rep <;> decide +kernel

theorem entry_reserve : Reserve arena .sector 1 initial :=
  sector_reserve (table:=table) checked 7 ledger rfl ledger_rep
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
example : E1M1NoiseMapGuards.MemoryGuards table checked := (checked_guards allocated checked entry_reserve).1
example : BelowFrame table initial.core allWrites := (checked_guards allocated checked entry_reserve).2.2
example : Restored initial.core result ∧ MapRep table result.core.memory ∧
    E1M1NoiseRecursive.eval 13 .sector initial=some result :=
  E1M1NoiseStack.sector_budget (table:=table) allocated checked 7 ledger rfl ledger_rep
    (by decide +kernel) (by decide +kernel) (by decide +kernel) 2
    (by simp [Bounded,table,mainSector,idleSector]) represented

-- No two-sided flag: the same two array entries now exercise both skip cases.
def skippedInitial : X86Control.State := { initial with core := { initial.core with
  memory := store32 initial.core.memory (wall+16) 0 } }
def skippedParent := startLines skippedInitial
def skippedNext := advance (dispatch skippedParent)
def skippedResult := finish (advance (dispatch skippedNext))
def skippedWrites := E1M1NoiseFootprint.sectorWrites skippedInitial.core++
  (E1M1NoiseFootprint.lineWrites skippedParent.core++E1M1NoiseFootprint.lineWrites skippedNext.core)
theorem skipped_checked : CheckedTrace (E1M1NoiseMapGuards.layout table) .sector skippedInitial skippedResult skippedWrites 1 := by
  have ir : StackRoom arena skippedInitial.core := stack_room (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have pr : StackRoom arena skippedParent.core := stack_room (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have nr : StackRoom arena skippedNext.core := stack_room (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have tail := CheckedTrace.lineDone skippedNext (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (allocated.ledger_line nr)
  have body := CheckedTrace.lineMore skippedParent skippedResult _ 0 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (allocated.ledger_line pr) tail
  have count : charge skippedInitial.core=1 := by decide +kernel
  simpa only [count,Nat.zero_add,skippedWrites] using
    CheckedTrace.sectorMore skippedInitial skippedResult _ 0 (by decide +kernel)
      (allocated.ledger_sector ir (by decide +kernel) (by decide +kernel)) body
example : E1M1NoiseMapGuards.MemoryGuards table skipped_checked :=
  (checked_guards allocated skipped_checked (show Reserve arena .sector 1 skippedInitial from
    by simp only [Reserve,need]; decide +kernel)).1


open E1M1NoiseGraph E1M1NoiseGraphAllocation

def edge : Edge := ⟨wall,68,0,1,origin,origin⟩
def edges := [edge]
-- One global-pointer word, an allocated line block, and two 18-byte sides.
def regions : List Region := [⟨0x2c118,0x2c11c⟩,⟨0x601001,0x601037⟩,⟨0x600801,0x600825⟩]
theorem stored : Storage table arena sides edges regions := by
  constructor <;> simp [graphReads,edgeReads,edge,edges,regions,Region.Contains,Region.Disjoint,
    table,mainSector,idleSector,arena,sectorRegion,sideAddress,globals,wall,sides,origin,other]

theorem graph_initial : GraphRep sides edges initial.core.memory := by
  constructor
  · decide +kernel
  · intro e he
    have eq : e=edge := List.mem_singleton.mp he
    subst e
    constructor
    all_goals first | decide +kernel | { intro _; decide +kernel }

theorem graph_parent : GraphRep sides edges parent.core.memory :=
  graph_initial.sector_step (stored.protect_sector allocated initial_room (by decide +kernel))
theorem coverage : Covered table edges := by simp [Covered,table,mainSector,idleSector,edges,edge]
theorem closure : Closed table edges := by
  simp [Closed,edges,edge,E1M1NoiseMapGuards.layout,table,mainSector,idleSector]

example : E1M1NoiseLedger.SectorSafe (E1M1NoiseMapGuards.layout table) called.core ∧
    GraphRep sides edges called.core.memory ∧ MapRep table called.core.memory :=
  stored.child_entry (n:=0) allocated (by simp only [Reserve,need]; decide +kernel)
    coverage closure (by simp [table]) started.1 started.2.1 graph_parent
    (by decide +kernel) (by decide +kernel)
example : Protect (graphReads sides edges) allWrites := stored.protect_trace allocated checked entry_reserve
example : GraphRep sides edges result.core.memory := stored.preserves_graph allocated checked entry_reserve graph_initial
example : Restored initial.core result ∧ MapRep table result.core.memory ∧
    GraphRep sides edges result.core.memory ∧ E1M1NoiseRecursive.eval 13 .sector initial=some result :=
  stored.sector_budget allocated checked 7 ledger rfl ledger_rep
    (by decide +kernel) (by decide +kernel) (by decide +kernel) 2
    (by simp [Bounded,table,mainSector,idleSector]) represented graph_initial
example : Protect (graphReads sides edges) skippedWrites :=
  stored.protect_trace allocated skipped_checked (show Reserve arena .sector 1 skippedInitial from
    by simp only [Reserve,need]; decide +kernel)

-- Shared/overlapping read-only regions are fine. They need separation from
-- writes, not from one another.
example : Storage table arena sides edges (regions++regions) := by
  constructor
  · intro address ha
    obtain ⟨r,hr,inside⟩ := stored.placed address ha
    exact ⟨r,List.mem_append_left _ hr,inside⟩
  · intro r hr
    rcases List.mem_append.mp hr with h|h <;> exact stored.stack r h
  · intro r hr e he
    rcases List.mem_append.mp hr with h|h <;> exact stored.sectors r h e he
  · intro r hr
    rcases List.mem_append.mp hr with h|h <;> exact stored.globals r h
open E1M1NoiseCount
-- Each child crosses a blocker (EDX=1); both returns resume parent ECX=0.
example : called.core.regs 2=1 ∧ parent.core.regs 1=0 ∧ after.core.regs 1=0 ∧ calledAgain.core.regs 2=1 := by decide +kernel
example : (advance childEnd).core.regs 1=parent.core.regs 1 :=
  resume_count allocated child (by simp only [Reserve,need]; decide +kernel) (by decide +kernel)
example : Every Entry checked.trace := all_entries allocated checked entry_reserve (by unfold Entry Legal; decide +kernel)
example : Every Entry skipped_checked.trace := all_entries allocated skipped_checked
  (by simp only [Reserve,need]; decide +kernel) (by unfold Entry Legal; decide +kernel)
example : Every Entry checked.trace ∧ Restored initial.core result ∧ MapRep table result.core.memory ∧
    GraphRep sides edges result.core.memory ∧ E1M1NoiseRecursive.eval 13 .sector initial=some result :=
  E1M1NoiseCount.sector_budget stored allocated checked 7 ledger rfl ledger_rep
    (by decide +kernel) (by decide +kernel) (by decide +kernel) 2
    (by simp [Bounded,table,mainSector,idleSector]) represented graph_initial (by unfold Entry Legal; decide +kernel)
-- A second blocker skips the call and preserves the parent's count of one.
def secondBlock : X86Memory.State := { parent.core with regs := write parent.core.regs 1 1 }
example : (E1M1NoiseIteration.dispatched secondBlock).pc=0x27006 ∧
    (E1M1NoiseIteration.dispatched secondBlock).core.regs 1=1 := by decide +kernel
-- Ordinary lines pass one unchanged, and do not reset it to zero.
def ordinary : X86Memory.State := { secondBlock with memory := store32 secondBlock.memory (wall+16) 4 }
example : (E1M1NoiseIteration.dispatched ordinary).pc=0x26f60 ∧
    (E1M1NoiseIteration.dispatched ordinary).core.regs 2=1 := by decide +kernel
end Doom.Verification.NoiseCountFixture
