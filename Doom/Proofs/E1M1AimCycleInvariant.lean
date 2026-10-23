import Doom.Proofs.E1M1AimHistoryCycle
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1AimCycleInvariant
open Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1MinimumScan (address)
open E1M1SelectionHistory (History)
open E1M1HistoryDispatch (Selection)
open E1M1InterceptMark (consume)
open E1M1AimHistoryCycle (Frame)
attribute [local irreducible] load32 store32

/-- Fixed stack-layout obligations, independent of which line is selected.
Map-image and pointer-dependent clipping obligations remain separate. -/
structure Layout (s : X86Memory.State) (hits : Array Intercept) : Prop where
  returnSafe : E1M1AimReturnFrame.Safe s
  recordsSafe : E1M1AimRecordFrame.RecordsSafe s hits
  cursorSafe : E1M1AimRecordFrame.ReadSafe s 0x2c028
  floorReads : E1M1AimFloorEntry.ReadSafe s
  ceilingReads : E1M1AimCeilingEntry.ReadSafe s
  helperSafe : E1M1AimOpening.CallerSafe s
  targetSafe : Apart (s.regs 4+4) 0x2c028
  cursorStore : Apart 0x2c028 (s.regs 4)
  recordStore : ∀ i<hits.size, ∀ off∈[(0#32),4,8],
    Apart (OriginalLineCollection.slot 0x2ba20 i off) (s.regs 4)
  boundsStore : Apart (0x2c1e4#32) (s.regs 4) ∧ Apart (0x2c1e8#32) (s.regs 4)
  slotSafe : E1M1AimRecordFrame.ReadSafe s (s.regs 4+4)

/-- A callback pops its return word and the next CALL pushes one: the reached
callback has exactly the same entry stack pointer, including wraparound. -/
theorem stack (s : X86Memory.State) (initial work : Array Intercept) (seen : List Nat)
    (resolve : Intercept → Word) (target : Word) (out : X86Control.State)
    (distance : Int32) (j : Nat)
    (selection : Selection initial work seen resolve target (s.regs 4+4) out distance j) :
    out.core.regs 4=s.regs 4 := by
  simpa [BitVec.add_sub_cancel] using selection.ready.stack

/-- The fixed separation conditions transfer to the next callback without
assuming them anew. Marking a record does not change the buffer's size. -/
theorem layout (s t : X86Memory.State) (hits : Array Intercept) (j : Nat)
    (sameStack : t.regs 4=s.regs 4) (safe : Layout s hits) :
    Layout t (consume hits j) := by
  rcases safe with ⟨ret,records,cursor,floor,ceiling,helper,target,store,record,bounds,slot⟩
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [E1M1AimReturnFrame.Safe,sameStack] using ret
  · simpa only [E1M1AimRecordFrame.RecordsSafe,E1M1AimRecordFrame.ReadSafe,sameStack,E1M1InterceptMark.size] using records
  · simpa only [E1M1AimRecordFrame.ReadSafe,sameStack] using cursor
  · simpa only [E1M1AimFloorEntry.ReadSafe,sameStack] using floor
  · simpa only [E1M1AimCeilingEntry.ReadSafe,sameStack] using ceiling
  · simpa only [E1M1AimOpening.CallerSafe,sameStack] using helper
  · simpa only [sameStack] using target
  · simpa only [sameStack] using store
  · simpa only [sameStack,E1M1InterceptMark.size] using record
  · simpa only [sameStack] using bounds
  · simpa only [E1M1AimRecordFrame.ReadSafe,sameStack] using slot

/-- Read the exact original next hit from the actual reached callback memory,
using its explicit selected index rather than an unrelated existential witness. -/
theorem record (initial work : Array Intercept) (seen : List Nat) (visits : Array Intercept)
    (resolve : Intercept → Word) (target sp : Word) (out : X86Control.State)
    (distance : Int32) (j : Nat) (history : History initial work seen visits)
    (selection : Selection initial work seen resolve target sp out distance j) :
    OriginalLineFinish.RecordAt out.core.memory (out.core.regs 0) initial[j]! (resolve initial[j]!) := by
  have size := (E1M1SelectionHistory.image history).size
  have inside : j<work.size := by have := selection.inside; omega
  have encoded := selection.ready.records j inside
  rw [← getElem!_pos work j inside,selection.original] at encoded
  rw [selection.argument]
  simpa [E1M1MinimumScan.address,BitVec.ofNat_add] using encoded

/-- Query range and eye height are read-only for this cycle; clipping bounds
are intentionally excluded because the callback updates them. -/
def QuerySafe (s : X86Memory.State) : Prop :=
  ∀ a∈[(0x2b9b8#32),(0x2b9a8#32)],
    E1M1AimRecordFrame.ReadSafe s a ∧ Apart a (s.regs 3) ∧ Apart a (s.regs 4)

theorem query_words (s : X86Memory.State) (out : X86Control.State)
    (frame : Frame s out) (safe : QuerySafe s) :
    load32 out.core.memory (0x2b9b8#32)=load32 s.memory (0x2b9b8#32) ∧
    load32 out.core.memory (0x2b9a8#32)=load32 s.memory (0x2b9a8#32) := by
  have range := safe (0x2b9b8#32) (by simp)
  have eye := safe (0x2b9a8#32) (by simp)
  exact ⟨frame _ range.1 range.2.1 (by unfold Apart; decide) range.2.2,
    frame _ eye.1 eye.2.1 (by unfold Apart; decide) eye.2.2⟩

/-- Whichever bounded record is selected next, its fraction store is disjoint
from the fixed query globals. Thus the query protection itself is reusable. -/
theorem query_safe (s : X86Memory.State) (initial work : Array Intercept) (seen : List Nat)
    (resolve : Intercept → Word) (target : Word) (out : X86Control.State)
    (distance : Int32) (j : Nat)
    (selection : Selection initial work seen resolve target (s.regs 4+4) out distance j)
    (bounded : initial.size≤128) (safe : QuerySafe s) : QuerySafe out.core := by
  have sp := stack s initial work seen resolve target out distance j selection
  have pointer := selection.ready.pointer.trans selection.argument
  have all : ∀ i : Fin 128,
      Apart (0x2b9b8#32) (address i.val) ∧ Apart (0x2b9a8#32) (address i.val) := by
    unfold Apart E1M1MinimumScan.address; decide
  have inside : j<128 := by have := selection.inside; omega
  intro a member
  have prior := safe a member
  refine ⟨?_,?_,?_⟩
  · simpa only [E1M1AimRecordFrame.ReadSafe,sp] using prior.1
  · rw [pointer]
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl
    · exact (all ⟨j,inside⟩).1
    · exact (all ⟨j,inside⟩).2
  · simpa only [sp] using prior.2.2
/-- At a reached next callback, assemble the preserved layout and query data
with its original source record. No next-state layout or query words are premises. -/
theorem entry (s : X86Memory.State) (initial hits : Array Intercept) (marked : Nat)
    (seen : List Nat) (visits : Array Intercept) (resolve : Intercept → Word)
    (target : Word) (out : X86Control.State) (distance : Int32) (j : Nat)
    (history : History initial (consume hits marked) seen visits)
    (selection : Selection initial (consume hits marked) seen resolve target (s.regs 4+4) out distance j)
    (bounded : initial.size≤128) (safe : Layout s hits) (querySafe : QuerySafe s)
    (frame : Frame s out) :
    out.core.regs 4=s.regs 4 ∧ Layout out.core (consume hits marked) ∧ QuerySafe out.core ∧
    OriginalLineFinish.RecordAt out.core.memory (out.core.regs 0) initial[j]! (resolve initial[j]!) ∧
    load32 out.core.memory (0x2b9b8#32)=load32 s.memory (0x2b9b8#32) ∧
    load32 out.core.memory (0x2b9a8#32)=load32 s.memory (0x2b9a8#32) := by
  have sp := stack s initial (consume hits marked) seen resolve target out distance j selection
  exact ⟨sp,layout s out.core hits marked sp safe,
    query_safe s initial (consume hits marked) seen resolve target out distance j selection bounded querySafe,
    record initial (consume hits marked) seen visits resolve target (s.regs 4+4) out distance j history selection,
    query_words s out frame querySafe⟩

end Doom.Proofs.E1M1AimCycleInvariant
