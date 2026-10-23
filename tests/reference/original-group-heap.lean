import Doom.Proofs.OriginalGroupHeap
set_option maxRecDepth 32768
set_option maxHeartbeats 30000
namespace Doom.Tests.GroupHeap
open Verification X86 X86Memory X86Control Doom.Proofs BlockSummary
open OriginalGroupOutput (Line Inputs Linked)
def lines : List Line := [⟨0x6000,0xa000,0⟩]
def initial : X86Memory.State :=
  ⟨fun r => if r=4 then 0x680000 else 0,
    [(0x2c120,0x6000),(0x2c134,1),(0x602e,0xa000),(0x6032,0),
     (0x74fe0,0x610000),(0x61001c,0x620000),(0x620000,4096),
     (0x620014,0x621000),(0x621004,2),(0x620010,0x622100),
     (0x2c148,0xa000),(0x2c14c,1)].foldl (fun m (a,v) => store32 m a v) (fun _ => 0)⟩
def before := (OriginalGroupCountScan.final lines initial).core

theorem layout : OriginalGroupCountScan.Layout lines := by
  constructor
  · simp only [OriginalGroupCountScan.SafeWord,lines,List.forall_mem_cons,List.not_mem_nil,false_implies,implies_true,and_true]
    constructor
    · unfold Apart; decide +kernel
    · simp
  · intro e he
    simp only [lines,List.mem_singleton] at he
    subst e
    simp only [OriginalGroupCountScan.SafeWord,lines,List.forall_mem_cons,List.not_mem_nil,false_implies,implies_true,and_true]
    repeat' apply And.intro
    all_goals try { simp }
    all_goals unfold Apart
    all_goals decide +kernel

theorem inputs : Inputs lines initial.memory := by
  intro e he
  simp only [lines,List.mem_singleton] at he
  subst e
  constructor <;> decide +kernel

theorem linked : Linked lines (load32 initial.memory 0x2c120) := by
  simp only [lines,Linked]
  decide +kernel

def view : OriginalGroupHeap.View :=
  ⟨0x610000,0x620000,0x621000,2,0x621000,4096,0x622100⟩

theorem heap : view.Holds initial.memory := by
  simp only [OriginalGroupHeap.View.Holds,OriginalGroupHeap.View.words,
    List.forall_mem_cons,List.not_mem_nil,false_implies,implies_true,and_true]
  repeat' apply And.intro
  all_goals decide +kernel

theorem untouched : ∀ w∈view.words, OriginalGroupCountScan.SafeWord w.1 lines := by
  simp only [OriginalGroupHeap.View.words,OriginalGroupCountScan.SafeWord,lines,
    List.forall_mem_cons,List.not_mem_nil,false_implies,implies_true,and_true]
  repeat' apply And.intro
  all_goals try { simp }
  all_goals unfold Apart
  all_goals decide +kernel

theorem conditions : OriginalGroupHeap.Conditions view (OriginalGroupHeap.request lines) (initial.regs 4) := by
  constructor
  · decide +kernel
  · decide +kernel
  all_goals try simp only [OriginalGroupHeap.View.words,OriginalGroupHeap.StackSafe,
    OriginalGroupHeap.Separated,OriginalGroupHeap.splitWrites,OriginalGroupHeap.headerWrites,
    List.forall_mem_append,List.forall_mem_cons,List.not_mem_nil,false_implies,implies_true,and_true]
  all_goals repeat' apply And.intro
  all_goals unfold Apart
  all_goals decide +kernel

theorem ready : OriginalGroupMalloc.Ready before :=
  OriginalGroupHeap.count_ready view lines initial layout inputs linked heap untouched conditions

theorem whole : X86Routine.run OriginalGroupStartup.program [0x2e661,0x2e791] 104
    ⟨initial,none,0x2e5ef⟩=some (OriginalGroupStartup.result lines initial) :=
  OriginalGroupHeap.execution view lines initial none (by decide) layout inputs linked
    (by decide +kernel) heap untouched conditions

theorem safe_count : OriginalGroupMalloc.SafeWord 0xa04e before := by
  simp only [OriginalGroupMalloc.SafeWord,OriginalGroupMallocEntry.SafeWord,
    OriginalGroupSelected.SafeWord,OriginalGroupSplit.SafeWord,OriginalGroupHandoff.SafeWord,
    OriginalGroupAllocation.SafeWord,OriginalGroupEntry.SafeWord,
    List.forall_mem_cons,List.not_mem_nil,false_implies,implies_true,and_true]
  repeat' apply And.intro
  all_goals unfold Apart
  all_goals decide +kernel

theorem counter_safe : OriginalGroupCountScan.CounterSafe 0xa000 lines := by
  simp only [OriginalGroupCountScan.CounterSafe,
    lines,List.forall_mem_cons,List.not_mem_nil,false_implies,implies_true,and_true]
  repeat' apply And.intro
  all_goals try { simp }
  all_goals unfold Apart
  all_goals decide +kernel

theorem final_count : load32 (OriginalGroupStartup.result lines initial).core.memory 0xa04e=1 :=
  OriginalGroupStartup.sector_count lines initial 0xa000 layout inputs linked (by decide) counter_safe safe_count

-- No return-address premise: the actual CALL supplies this word.
theorem return_from_call : load32 (OriginalGroupMalloc.candidate before).core.memory
    ((OriginalGroupMalloc.candidate before).core.regs 4+16)=0x2e63e :=
  OriginalGroupMalloc.return_address before

theorem rounded_request : (OriginalGroupMalloc.candidate before).core.regs 1=28 :=
  (OriginalGroupMalloc.candidate_arguments before).1

theorem e1m1_request : OriginalGroupMallocEntry.rounded 2568=2592 := OriginalGroupMallocEntry.request_e1m1

theorem wrap_rounding : OriginalGroupMallocEntry.rounded 0xfffffffc=20 ∧
    OriginalGroupMallocEntry.rounded 0xfffffffd=24 := by decide +kernel

#print axioms whole
#print axioms final_count
#print axioms return_from_call
#print axioms rounded_request
end Doom.Tests.GroupHeap
