import Doom.Proofs.OriginalGroupSelected
set_option maxRecDepth 32768
set_option maxHeartbeats 30000
namespace Doom.Tests.GroupSelected
open Verification X86 X86Memory X86Control Doom.Proofs BlockSummary

def memory (size : Word) : Memory :=
  [(0x620000,size),(0x620010,0x620f00),(0x74fe0,0x610000),
    (0x680010,0x2e63e),(0x2c148,0x630000),(0x2c14c,85),
    (0x63004e,3)].foldl (fun m (a,v) => store32 m a v) (fun _ => 0)
def initial (size : Word) : X86Memory.State :=
  ⟨fun r => if r=1 then 2592 else if r=3 then 0x620000 else if r=4 then 0x680000
    else if r=5 then 50 else 0,memory size⟩
def start := initial 3000

theorem safe_return : OriginalGroupSelected.ReturnSafe start := by
  simp only [OriginalGroupSelected.ReturnSafe,OriginalGroupSplit.SafeWord,
    OriginalGroupAllocation.SafeWord,List.forall_mem_cons,List.not_mem_nil,false_implies,implies_true,and_true]
  repeat' apply And.intro
  all_goals unfold Apart
  all_goals decide +kernel

theorem safe_count : OriginalGroupSelected.SafeWord 0x63004e start := by
  simp only [OriginalGroupSelected.SafeWord,OriginalGroupSplit.SafeWord,
    OriginalGroupHandoff.SafeWord,OriginalGroupAllocation.SafeWord,
    OriginalGroupEntry.SafeWord,List.forall_mem_cons,List.not_mem_nil,false_implies,implies_true,and_true]
  repeat' apply And.intro
  all_goals unfold Apart
  all_goals decide +kernel

theorem joined : X86Routine.run OriginalGroupSelected.program [0x2e661,0x2e791] 53
    ⟨start,none,0x396f8⟩=some (OriginalGroupSelected.result start) :=
  OriginalGroupSelected.execution start none (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) safe_return (by decide +kernel)

theorem count_preserved : load32 (OriginalGroupSelected.result start).core.memory 0x63004e=3 :=
  OriginalGroupSelected.count_field start 0x630000 3 (by decide +kernel) safe_count

-- The original threshold is strictly greater than 64, not greater-or-equal.
theorem threshold64 :
    (OriginalGroupSelected.allocated (initial 2656)).core.memory=(initial 2656).memory :=
  OriginalGroupSplit.no_split_memory _ (by decide +kernel)
theorem threshold65 :
    load32 (OriginalGroupSelected.allocated (initial 2657)).core.memory 0x620000=2592 ∧
    load32 (OriginalGroupSelected.allocated (initial 2657)).core.memory 0x620a20=65 := by
  constructor <;> decide +kernel

theorem split_links :
    load32 (OriginalGroupSelected.allocated start).core.memory 0x620a30=0x620f00 ∧
    load32 (OriginalGroupSelected.allocated start).core.memory 0x620f14=0x620a20 ∧
    load32 (OriginalGroupSelected.allocated start).core.memory 0x620010=0x620a20 ∧
    load32 (OriginalGroupSelected.allocated start).core.memory 0x620a34=0x620000 := by
  repeat' apply And.intro
  all_goals decide +kernel

theorem undersized_rejected :
    (OriginalGroupSplit.candidate (initial 2591)).pc=0x396bd := by decide +kernel

theorem occupied_rejected :
    (OriginalGroupSplit.candidate {start with memory:=store32 start.memory 0x620004 2}).pc=0x396bd := by
  decide +kernel

-- The old saved-return slot is intentionally reused by the next CALL.
theorem return_slot_reused : ¬OriginalGroupEntry.SafeWord 0x680010 0x680014 := by
  intro safe
  have overlap := safe 0x680010 (by decide +kernel)
  exact overlap 0 0 rfl

#print axioms joined
#print axioms count_preserved
#print axioms threshold64
#print axioms threshold65
#print axioms split_links
end Doom.Tests.GroupSelected
