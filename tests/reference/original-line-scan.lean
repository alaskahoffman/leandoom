import Doom.Proofs.E1M1LineScan
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
namespace Doom.Verification.LineScanFixture
open X86 X86Memory X86Control Doom.Proofs E1M1LineScan BlockSummary

-- Two raw records share vertices; the first is vertical, the second diagonal.
-- Distinct raw/runtime strides and a wrapping, unaligned stack are deliberate.
def words : List (Word × Word) :=
  [(0x2c134,2),(0x2c138,0x8000),(0x2c118,0x9000),
   (0x8000,0),(0x8004,0),(0x8008,0),(0x800c,65536),
   (0x8010,65536),(0x8014,131072)]
def halves : List (Word × BitVec 16) :=
  [(0x6000,0),(0x6002,1),(0x6004,7),(0x6006,8),(0x6008,9),
   (0x600a,65535),(0x600c,65535),
   (0x600e,1),(0x6010,2),(0x6012,10),(0x6014,11),(0x6016,12),
   (0x6018,65535),(0x601a,65535)]
def memory : Memory := halves.foldl (fun m (a,v) => X86Routine.store16 m a v)
  (words.foldl (fun m (a,v) => store32 m a v) (fun _ => 0x5a))
def initial : X86Memory.State :=
  ⟨fun r => if r=1 then 0x6000 else if r=3 then 0x7000 else if r=4 then 2 else 0,memory⟩

theorem layout : Layout 2 0x7000 2 := by
  refine ⟨by decide,?_⟩
  intro i bound
  have cases : i=0 ∨ i=1 := by omega
  rcases cases with rfl|rfl
  all_goals constructor
  all_goals simp only [List.forall_mem_cons,List.not_mem_nil,false_implies,implies_true,and_true]
  all_goals simp only [Apart,HalfMemory.Separate]
  all_goals decide +kernel

theorem ready : Ready 2 0x6000 0x7000 2 0 initial := by
  constructor <;> decide +kernel

theorem arithmetic : Arithmetic 2 initial none := by
  intro i bound
  have cases : i=0 ∨ i=1 := by omega
  rcases cases with rfl|rfl
  all_goals unfold E1M1LineIteration.Safe OriginalDivMemory.Safe OriginalDivMemory.DivSafe
  all_goals decide +kernel

theorem complete : X86Routine.run E1M1LineIteration.program [0x2e3c1] 208
    ⟨initial,none,0x2e29a⟩=some (states initial none 2) :=
  (scan_execution (total:=2) (raw:=0x6000) (line:=0x7000) (sp:=2)
    (s:=initial) (f:=none) layout ready arithmetic (by decide)).1

-- The loop really took both branches, retained the first record, and stopped.
example : E1M1LineIteration.Axis initial ∧ ¬E1M1LineIteration.Axis (states initial none 1).core := by
  decide +kernel
example : (states initial none 2).pc=0x2e3c1 ∧
    (states initial none 2).core.regs 1=0x601c ∧
    (states initial none 2).core.regs 3=0x707c ∧
    (states initial none 2).core.regs 4=2 ∧
    load32 (states initial none 2).core.memory 0x702a=1 ∧
    load32 (states initial none 2).core.memory 0x7068=2 ∧
    load16 (states initial none 2).core.memory 0x7010=7 := by decide +kernel

-- Overlapping count/output storage cannot satisfy the frame premise.
example : ¬E1M1LineFrame.Protected 0x2c134 0x2c134 2 := by
  intro h
  have bad := h.words 0 (by simp)
  exact bad 0 0 (by simp)
#print axioms complete
end Doom.Verification.LineScanFixture
