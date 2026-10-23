import Doom.Proofs.OriginalGroupReturn
set_option maxRecDepth 32768
set_option maxHeartbeats 40000
set_option linter.unusedSimpArgs false
namespace Doom.Tests.GroupReturn
open Verification X86 X86Memory X86Control Doom.Proofs BlockSummary

-- Values suggested by the pinned startup diagnostic. Earlier history is not a premise proved here.
def plan : OriginalGroupRemainder.Plan :=
  ⟨2678820,4621964,2678824,6445464,928,11071584,50⟩
def initial : X86Memory.State :=
  ⟨fun r => if r=4 then 0x680000 else 0,
    [(0x680000,0x11111111),(0x680004,0),(0x680008,60),(0x68000c,15),(0x680010,0x38d41),
     (0x74f94,11071524),(0x74fe0,2678820),(4621980,2678824),(0x2c148,0x630000),(0x2c14c,85)].foldl
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

theorem frame : OriginalGroupReturn.FrameSafe plan initial := by
  simp only [OriginalGroupReturn.FrameSafe,OriginalGroupRemainder.Plan.writes,
    OriginalGroupRemainder.Plan.published,OriginalGroupRemainder.Plan.splitWrites,
    OriginalGroupRemainder.Plan.header,List.forall_mem_append,List.forall_mem_cons,
    List.not_mem_nil,false_implies,implies_true,and_true]
  unfold Apart
  decide +kernel

theorem return_run : X86Routine.run OriginalGroupRemainder.program [0x38d41] 31
    ⟨plan.input initial,none,0x39704⟩=some (OriginalGroupReturn.returned plan initial) :=
  OriginalGroupReturn.return_execution plan initial none conditions frame (by decide +kernel)

theorem whole : X86Routine.run OriginalGroupReturn.program [0x38bf0] 35
    ⟨plan.input initial,none,0x39704⟩=some (OriginalGroupReturn.result plan initial) :=
  OriginalGroupReturn.execution plan initial none conditions frame (by decide +kernel)

theorem cache_safe : ∀ w∈plan.writes, Apart 0x74f94 w.1 := by
  simp only [OriginalGroupRemainder.Plan.writes,OriginalGroupRemainder.Plan.published,
    OriginalGroupRemainder.Plan.splitWrites,OriginalGroupRemainder.Plan.header,
    List.forall_mem_append,List.forall_mem_cons,List.not_mem_nil,false_implies,implies_true,and_true]
  repeat' apply And.intro
  all_goals unfold Apart
  all_goals decide +kernel

theorem arguments : (OriginalGroupReturn.result plan initial).core.regs 0=15 ∧
    (OriginalGroupReturn.result plan initial).core.regs 2=4621988 ∧
    (OriginalGroupReturn.result plan initial).core.regs 4=0x680010 :=
  OriginalGroupReturn.read_arguments plan initial conditions frame 15 11071524
    (by decide +kernel) (by decide +kernel) (by decide +kernel) cache_safe (by decide +kernel)

theorem stack_safe : ∀ w∈plan.view.words, Apart w.1 (initial.regs 4+16) := by
  simp only [OriginalGroupHeap.View.words,List.forall_mem_cons,List.not_mem_nil,
    false_implies,implies_true,and_true]
  repeat' apply And.intro
  all_goals unfold Apart
  all_goals decide +kernel

theorem heap_view : plan.view.Holds (OriginalGroupReturn.result plan initial).core.memory :=
  OriginalGroupReturn.read_view plan initial conditions frame stack_safe

theorem actual_read_return : load32 (OriginalGroupReturn.result plan initial).core.memory
    ((OriginalGroupReturn.result plan initial).core.regs 4)=0x38d50 :=
  OriginalGroupReturn.read_return plan initial

-- The second CALL reuses the slot that held the allocator's return address.
theorem overwritten_return : load32 (OriginalGroupReturn.result plan initial).core.memory 0x680010=0x38d50 := by
  have h := actual_read_return
  rw [arguments.2.2] at h
  exact h

#print axioms whole
#print axioms return_run
#print axioms arguments
#print axioms heap_view
#print axioms overwritten_return
end Doom.Tests.GroupReturn
