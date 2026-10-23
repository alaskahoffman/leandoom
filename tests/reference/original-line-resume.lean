import Doom.Proofs.E1M1LineResume
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open OriginalLineResume

def listMemory : Memory :=
  [(0xfffffffd,0x00010000),(1,0xffff0000),(0x13580,99),(0x2c120,0x600400),
    (0x600436,99),(0x600474,99),(0xfffffe05,777),(0xfffffe09,0x4f000)].foldl
    (fun m (a,v) => store32 m a v) (fun _ => 0)
def listState : X86Control.State :=
  ⟨⟨fun r => if r=2 then 0xfffffffd else if r=4 then 0xfffffe01 else 0,listMemory⟩,none,0x2c57f⟩

theorem window : ∀ i<3, SeenAt listState.core.memory (listState.core.regs 2+BitVec.ofNat 32 (2*i)) := by
  intro i hi
  have cases : i=0 ∨ i=1 ∨ i=2 := by omega
  rcases cases with rfl|rfl|rfl <;> unfold SeenAt <;> decide
example : Duplicates 3 listState := duplicates_from_memory 3 listState window
example : (skipMany 3 listState).core.regs 2=(3#32) := by decide
example : OriginalLineCell.item (skipMany 3 listState).core=(0xffff#16) := by decide
example : ∃ steps≤37, X86Routine.Prefix program [] steps listState
    (OriginalLineBounds.returned (OriginalLineCell.header (skipMany 3 listState).core).core) :=
  through_sentinel 3 listState rfl window (by decide)
example : (OriginalLineBounds.returned (OriginalLineCell.header (skipMany 3 listState).core).core).core.regs 0=(1#32) := by decide
example : (OriginalLineBounds.returned (OriginalLineCell.header (skipMany 3 listState).core).core).core.regs 4=(0xfffffe0d#32) := by decide
example : (OriginalLineBounds.returned (OriginalLineCell.header (skipMany 3 listState).core).core).core.regs 7=(777#32) := by decide
example : (OriginalLineBounds.returned (OriginalLineCell.header (skipMany 3 listState).core).core).pc=0x4f000 := by decide
example : (result (put listState.core 0 0)).core.regs 0=(0#32) := by decide
example : (result (put listState.core 0 0)).pc=0x4f000 := by decide
example : (result (put listState.core 0 0x80000000)).pc=0x2c57f := by decide
example : (result (put listState.core 0 0x80000000)).core.regs 2=(0xffffffff#32) := by decide

-- A real callback return must preserve its saved cursor and return word.
def callback : X86Memory.State :=
  ⟨fun r => if r=0 then 65536 else if r=1 then 0x600401 else if r=4 then 0xfffffe01 else 0,
   [(0x2c028,0x600801),(0xfffffe19,0xfffffffd),(0xfffffe25,0x2c578)].foldl
    (fun m (a,v) => store32 m a v) (fun _ => 0)⟩
example : (OriginalLineFinish.result callback).pc=0x2c578 := by decide
example : (result (OriginalLineFinish.result callback).core).core.regs 2=(0xffffffff#32) := by decide
example : (result (OriginalLineFinish.result callback).core).core.regs 4=(0xfffffe29#32) := by decide
example : (result (OriginalLineFinish.result callback).core).pc=0x2c57f := by decide
