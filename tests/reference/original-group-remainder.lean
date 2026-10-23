import Doom.Proofs.OriginalGroupRemainder
set_option maxRecDepth 32768
set_option maxHeartbeats 40000
set_option linter.unusedSimpArgs false
namespace Doom.Tests.GroupRemainder
open Verification X86 X86Memory X86Control Doom.Proofs BlockSummary

-- Values suggested by the pinned startup diagnostic. Earlier history is not a premise proved here.
def plan : OriginalGroupRemainder.Plan :=
  ⟨2678820,4621964,2678824,6445464,928,11071584,50⟩
def initial : X86Memory.State :=
  ⟨fun r => if r=4 then 0x680000 else 0,
    [(0x74fe0,2678820),(4621980,2678824),(0x2c148,0x630000),(0x2c14c,85)].foldl
      (fun m (a,v) => store32 m a v) (fun _ => 0)⟩

theorem conditions : OriginalGroupRemainder.Conditions plan initial.memory := by
  constructor
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  all_goals simp only [OriginalGroupRemainder.Plan.writes,OriginalGroupRemainder.Plan.published,
    OriginalGroupRemainder.Plan.splitWrites,OriginalGroupRemainder.Plan.header,
    HeapWrites.Disjoint,List.pairwise_cons,List.forall_mem_append,
    List.forall_mem_cons,List.not_mem_nil,false_implies,implies_true,and_true]
  all_goals repeat' apply And.intro
  all_goals try exact List.Pairwise.nil
  all_goals unfold Apart
  all_goals decide +kernel

theorem predecessor_run : X86Routine.run OriginalGroupRemainder.program [0x39771] 26
    ⟨plan.input initial,none,0x39704⟩=some (plan.result initial) :=
  OriginalGroupRemainder.execution plan initial none (by decide +kernel)

theorem produced_view : plan.view.Holds (plan.result initial).core.memory :=
  OriginalGroupRemainder.establishes_view plan initial conditions

theorem owner_cell : load32 (plan.result initial).core.memory 11071584=4621988 :=
  OriginalGroupRemainder.owner_published plan initial conditions

theorem remainder_size : load32 (plan.result initial).core.memory 4622892=6444536 :=
  (OriginalGroupHeap.View.fields plan.view _ produced_view).2.2.2.2.2.2.1

-- An explicit caller seam: this is a subsequent call state, not a proof of the
-- intervening RET/caller instructions. Its heap is produced by the first run.
def next : X86Memory.State :=
  ⟨fun r => if r=0 then 2568 else if r=2 then 50 else if r=4 then 0x680000 else 0,
    (plan.result initial).core.memory⟩

theorem next_conditions : OriginalGroupHeap.Conditions plan.view 2568 0x680000 := by
  constructor
  · decide +kernel
  · decide +kernel
  all_goals try simp only [OriginalGroupHeap.View.words,OriginalGroupHeap.StackSafe,
    OriginalGroupHeap.Separated,OriginalGroupHeap.splitWrites,OriginalGroupHeap.headerWrites,
    List.forall_mem_append,List.forall_mem_cons,List.not_mem_nil,false_implies,implies_true,and_true]
  all_goals repeat' apply And.intro
  all_goals try exact List.Pairwise.nil
  all_goals unfold Apart
  all_goals decide +kernel

theorem next_ready : OriginalGroupMalloc.Ready next :=
  OriginalGroupHeap.ready plan.view next produced_view next_conditions

theorem next_run : X86Routine.run OriginalGroupMalloc.program [0x2e661,0x2e791] 78
    ⟨next,none,0x2e639⟩=some (OriginalGroupMalloc.result next) :=
  OriginalGroupMalloc.execution next none next_ready (by decide +kernel) (by decide +kernel)

#print axioms predecessor_run
#print axioms produced_view
#print axioms owner_cell
#print axioms remainder_size
#print axioms next_ready
#print axioms next_run
end Doom.Tests.GroupRemainder
