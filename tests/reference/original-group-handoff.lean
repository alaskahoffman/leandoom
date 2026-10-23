import Doom.Proofs.OriginalGroupHandoff
set_option maxRecDepth 32768
set_option maxHeartbeats 100000
namespace Doom.Tests.GroupHandoff
open Verification X86 X86Memory X86Control Doom.Proofs BlockSummary

def memory : Memory :=
  let m : Memory := fun _ => 0
  let m := store32 m 0x74fe0 0x610000
  let m := store32 m 0x620010 0x620100
  let m := store32 m 0x680010 0x2e63e
  let m := store32 m 0x2c148 0x630000
  let m := store32 m 0x2c14c 85
  let m := store32 m 0x63004e 3
  let m := store32 m 0x63202e 0x630000
  store32 m 0x632032 0

def initial : X86Memory.State :=
  ⟨fun r => if r=3 then 0x620000 else if r=4 then 0x680000 else if r=5 then 50 else 0,memory⟩

theorem safe_return : OriginalGroupAllocation.SafeWord (initial.regs 4+16) initial := by
  unfold OriginalGroupAllocation.SafeWord Apart
  decide +kernel

theorem saved_return : load32 initial.memory (initial.regs 4+16)=0x2e63e := by decide +kernel

theorem run_checked :
    X86Routine.run OriginalGroupHandoff.program [0x2e661,0x2e791] 34 ⟨initial,none,0x39731⟩=
      some (OriginalGroupHandoff.result initial) :=
  OriginalGroupHandoff.execution initial none (by decide +kernel) (by decide +kernel) safe_return saved_return

theorem safe_word (a : Word) (h : a=0x63004e ∨ a=0x63202e ∨ a=0x632032) :
    OriginalGroupHandoff.SafeWord a initial := by
  rcases h with rfl|rfl|rfl
  all_goals simp only [OriginalGroupHandoff.SafeWord,OriginalGroupAllocation.SafeWord,
    OriginalGroupEntry.SafeWord,List.forall_mem_cons,List.not_mem_nil,false_implies,implies_true,and_true]
  all_goals repeat' apply And.intro
  all_goals unfold Apart
  all_goals decide +kernel

theorem count_preserved : load32 (OriginalGroupHandoff.result initial).core.memory 0x63004e=3 := by
  exact OriginalGroupHandoff.count_field initial 0x630000 3 (by decide +kernel)
    (safe_word _ (Or.inl rfl))

theorem fields_preserved :
    OriginalGroupOutput.Inputs [⟨0x632000,0x630000,0⟩] (OriginalGroupHandoff.result initial).core.memory := by
  apply OriginalGroupHandoff.inputs _ initial
  · intro e he
    simp only [List.mem_singleton] at he
    subst e
    constructor <;> decide +kernel
  · intro e he
    simp only [List.mem_singleton] at he
    subst e
    exact ⟨safe_word _ (Or.inr (Or.inl rfl)),safe_word _ (Or.inr (Or.inr rfl))⟩

theorem entry_registers : (OriginalGroupHandoff.result initial).core.regs 5=0x630000 ∧
    (OriginalGroupHandoff.result initial).core.regs 6=0x620018 ∧
    (OriginalGroupHandoff.result initial).core.regs 4=0x680014 := by
  exact OriginalGroupHandoff.registers initial
    (by unfold OriginalGroupAllocation.SafeWord Apart; decide +kernel)

theorem entry_pc : (OriginalGroupHandoff.result initial).pc=0x2e661 :=
  OriginalGroupHandoff.positive_pc initial
    (by unfold OriginalGroupAllocation.SafeWord Apart; decide +kernel) (by decide +kernel)

-- An overlapping saved-return word cannot satisfy the separation contract.
theorem rejects_overlap : ¬OriginalGroupAllocation.SafeWord (initial.regs 3+4) initial := by
  unfold OriginalGroupAllocation.SafeWord Apart
  decide +kernel

#print axioms run_checked
#print axioms count_preserved
#print axioms fields_preserved
#print axioms entry_registers
#print axioms entry_pc
end Doom.Tests.GroupHandoff
