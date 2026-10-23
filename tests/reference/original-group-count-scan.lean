import Doom.Proofs.OriginalGroupCountScan
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
namespace Doom.Verification.GroupCountScanFixture
open X86 X86Memory X86Control Doom.Proofs OriginalGroupCountScan BlockSummary
open OriginalGroupOutput (Line Inputs Linked chosen)

-- Absent back, distinct back, then a self-referencing line. All three must
-- survive prior counter writes, and both sectors start with zero references.
def lines : List Line := [⟨0x6000,0xa000,0⟩,⟨0x603e,0xb000,0xa000⟩,⟨0x607c,0xa000,0xa000⟩]
def initial : X86Memory.State :=
  ⟨fun _ => 0xdeadbeef,
    [(0x2c120,0x6000),(0x2c134,3),(0x602e,0xa000),(0x6032,0),
     (0x606c,0xb000),(0x6070,0xa000),(0x60aa,0xa000),(0x60ae,0xa000),
     (0xa04e,0),(0xb04e,0)].foldl (fun m (a,v) => store32 m a v) (fun _ => 0x5a)⟩

theorem layout : Layout lines := by
  constructor
  · simp only [SafeWord,lines,List.forall_mem_cons,List.not_mem_nil,false_implies,implies_true,and_true]
    repeat' apply And.intro
    all_goals simp only [Apart]
    all_goals decide +kernel
  · intro e he
    simp only [lines,List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl|rfl|rfl
    all_goals constructor
    all_goals simp only [SafeWord,lines,List.forall_mem_cons,List.not_mem_nil,false_implies,implies_true,and_true]
    all_goals repeat' apply And.intro
    all_goals simp only [Apart]
    all_goals decide +kernel

theorem inputs : Inputs lines initial.memory := by
  intro e he
  simp only [lines,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl <;> constructor <;> decide +kernel

theorem linked : Linked lines (load32 initial.memory 0x2c120) := by
  simp only [lines,Linked]
  decide +kernel
theorem count : (load32 initial.memory 0x2c134).toNat=lines.length := by decide +kernel

theorem whole : X86Routine.run OriginalGroupCount.program [0x2e639] 60 ⟨initial,none,0x2e5ef⟩=
    some (final lines initial) := complete lines initial none (by decide) layout inputs linked count

theorem counters (q : Word) (h : q=0xa000 ∨ q=0xb000) : CounterSafe q lines := by
  rcases h with rfl|rfl
  all_goals simp only [CounterSafe,lines,List.forall_mem_cons,List.not_mem_nil,false_implies,implies_true,and_true]
  all_goals repeat' apply And.intro
  all_goals simp only [Apart]
  all_goals decide +kernel

theorem counts :
    load32 (final lines initial).core.memory 0xa04e=3 ∧
    load32 (final lines initial).core.memory 0xb04e=1 := by
  constructor
  · have v := final_sector lines initial 0xa000 layout inputs linked (by decide) (counters _ (Or.inl rfl))
    exact v
  · have v := final_sector lines initial 0xb000 layout inputs linked (by decide) (counters _ (Or.inr rfl))
    exact v

theorem allocation : (final lines initial).core.regs 0=16 ∧ (final lines initial).pc=0x2e639 :=
  ⟨(final_arguments lines initial layout inputs linked).1,(final_arguments lines initial layout inputs linked).2.2.2⟩

theorem pointers : Inputs lines (final lines initial).core.memory := final_inputs lines initial layout inputs linked

def empty : X86Memory.State := ⟨fun _ => 0xffffffff,fun _ => 0⟩
theorem empty_run : X86Routine.run OriginalGroupCount.program [0x2e639] 9 ⟨empty,none,0x2e5ef⟩=
    some (final [] empty) := complete [] empty none (by decide)
      ⟨by simp [SafeWord],by simp⟩ (by simp [Inputs]) trivial (by decide +kernel)
example : (final [] empty).core.regs 0=0 := by decide +kernel

#print axioms whole
#print axioms counts
#print axioms allocation
#print axioms pointers
#print axioms empty_run
end Doom.Verification.GroupCountScanFixture
