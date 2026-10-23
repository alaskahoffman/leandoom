import Doom.Proofs.E1M1QueryCollection
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalInterceptMinimum
open Verification X86 X86Memory X86Control BlockSummary
def code : List UInt8 := [0xb8,0x20,0xba,0x2,0x0,0xba,0xff,0xff,0xff,0x7f,0x39,0xc1,0x76,0xf,0x3b,0x10,0x7e,0x4,0x89,0xc3,0x8b,0x10,0x83,0xc0,0xc,0x39,0xc8,0x72,0xf1]
def bytesProgram (bytes : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2c841≤pc ∧ pc<0x2c85e then X86Routine.decodeAt bytes (pc-0x2c841) else none
def program := bytesProgram code
def listed : X86Routine.Program
  | 0x2c841 => some (.immediate 0 0x2ba20,5)
  | 0x2c846 => some (.immediate 2 0x7fffffff,5)
  | 0x2c84b => some (.compareRegisters 1 0,2)
  | 0x2c84d => some (.jumpUnsigned 1 15,2)
  | 0x2c84f => some (.control (.cmpMemory 2 ⟨some 0,none,0,0⟩),2)
  | 0x2c851 => some (.jumpSigned 1 4,2)
  | 0x2c853 => some (.control (.block (.legacy (.mov 3 0))),2)
  | 0x2c855 => some (.control (.block (.legacy (.load 2 0 0))),2)
  | 0x2c857 => some (.addImmediate 0 12,3)
  | 0x2c85a => some (.compareRegisters 0 1,2)
  | 0x2c85c => some (.jumpUnsigned 0 (-15),2)
  | _ => none

theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def fraction (s : X86Memory.State) := load32 s.memory (s.regs 0)
def better (s : X86Memory.State) : Prop := (fraction s).toInt < (s.regs 2).toInt
instance (s : X86Memory.State) : Decidable (better s) := inferInstanceAs (Decidable (_<_))
def picked (s : X86Memory.State) := if better s then put (put s 3 (s.regs 0)) 2 (fraction s) else s
def advanced (s : X86Memory.State) := put (picked s) 0 (s.regs 0+12)
def result (s : X86Memory.State) : X86Control.State :=
  ⟨advanced s,some (compare32 (s.regs 0+12) (s.regs 1)),
    if (s.regs 0+12).toNat<(s.regs 1).toNat then 0x2c84f else 0x2c85e⟩
def steps (s : X86Memory.State) := if better s then 7 else 5

private theorem compare_carry (a b : Word) : (compare32 a b).carry=some (a.ult b) := rfl

/-- One original scan iteration, including strict signed comparison and the
unsigned pointer loop test. Equal fractions retain the earlier best pointer. -/
theorem iteration (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] (steps s) ⟨s,f,0x2c84f⟩ (result s) := by
  have run : X86Routine.Prefix listed [] (steps s) ⟨s,f,0x2c84f⟩ (result s) := by
    by_cases h : better s
    · simp only [steps,if_pos h]
      apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (s.regs 2) (fraction s)),0x2c851⟩) (by simp) (by rfl) (by
        try simp only [advanced,result,picked,h]
        simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        X86Block.Address.eval,put,write,blockPreservesFlags,cmp32_signed_le,
        compare_carry,BitVec.sub_eq_iff_eq_add,BitVec.ult,better,fraction,picked,advanced,result,steps]
        all_goals split <;> rfl)
      apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (s.regs 2) (fraction s)),0x2c853⟩) (by simp) (by rfl) (by
        try simp only [advanced,result,picked,h]
        simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        X86Block.Address.eval,put,write,blockPreservesFlags,cmp32_signed_le,
        compare_carry,BitVec.sub_eq_iff_eq_add,BitVec.ult,better,fraction,picked,advanced,result,steps]
        all_goals split <;> rfl)
      apply X86Routine.Prefix.step (middle := ⟨put s 3 (s.regs 0),some (compare32 (s.regs 2) (fraction s)),0x2c855⟩) (by simp) (by rfl) (by
        try simp only [advanced,result,picked,h]
        simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        X86Block.Address.eval,put,write,blockPreservesFlags,cmp32_signed_le,
        compare_carry,BitVec.sub_eq_iff_eq_add,BitVec.ult,better,fraction,picked,advanced,result,steps]
        all_goals split <;> rfl)
      apply X86Routine.Prefix.step (middle := ⟨picked s,some (compare32 (s.regs 2) (fraction s)),0x2c857⟩) (by simp) (by rfl) (by
        try simp only [advanced,result,picked,h]
        simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        X86Block.Address.eval,put,write,blockPreservesFlags,cmp32_signed_le,
        compare_carry,BitVec.sub_eq_iff_eq_add,BitVec.ult,better,fraction,picked,advanced,result,steps]
        all_goals split <;> rfl)
      apply X86Routine.Prefix.step (middle := ⟨advanced s,none,0x2c85a⟩) (by simp) (by rfl) (by
        try simp only [advanced,result,picked,h]
        simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        X86Block.Address.eval,put,write,blockPreservesFlags,cmp32_signed_le,
        compare_carry,BitVec.sub_eq_iff_eq_add,BitVec.ult,better,fraction,picked,advanced,result,steps]
        all_goals split <;> rfl)
      apply X86Routine.Prefix.step (middle := ⟨advanced s,some (compare32 (s.regs 0+12) (s.regs 1)),0x2c85c⟩) (by simp) (by rfl) (by
        try simp only [advanced,result,picked,h]
        simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        X86Block.Address.eval,put,write,blockPreservesFlags,cmp32_signed_le,
        compare_carry,BitVec.sub_eq_iff_eq_add,BitVec.ult,better,fraction,picked,advanced,result,steps]
        all_goals split <;> rfl)
      apply X86Routine.Prefix.step (middle := result s) (by simp) (by rfl) (by
        try simp only [advanced,result,picked,h]
        simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        X86Block.Address.eval,put,write,blockPreservesFlags,cmp32_signed_le,
        compare_carry,BitVec.sub_eq_iff_eq_add,BitVec.ult,better,fraction,picked,advanced,result,steps]
        all_goals split <;> rfl)
      exact .nil _
    · simp only [steps,if_neg h]
      apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (s.regs 2) (fraction s)),0x2c851⟩) (by simp) (by rfl) (by
        try simp only [advanced,result,picked,h]
        simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        X86Block.Address.eval,put,write,blockPreservesFlags,cmp32_signed_le,
        compare_carry,BitVec.sub_eq_iff_eq_add,BitVec.ult,better,fraction,picked,advanced,result,steps]
        all_goals split <;> rfl)
      apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (s.regs 2) (fraction s)),0x2c857⟩) (by simp) (by rfl) (by
        try simp only [advanced,result,picked,h]
        simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        X86Block.Address.eval,put,write,blockPreservesFlags,cmp32_signed_le,
        compare_carry,BitVec.sub_eq_iff_eq_add,BitVec.ult,better,fraction,picked,advanced,result,steps]
        all_goals split <;> rfl)
      apply X86Routine.Prefix.step (middle := ⟨advanced s,none,0x2c85a⟩) (by simp) (by rfl) (by
        try simp only [advanced,result,picked,h]
        simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        X86Block.Address.eval,put,write,blockPreservesFlags,cmp32_signed_le,
        compare_carry,BitVec.sub_eq_iff_eq_add,BitVec.ult,better,fraction,picked,advanced,result,steps]
        all_goals split <;> rfl)
      apply X86Routine.Prefix.step (middle := ⟨advanced s,some (compare32 (s.regs 0+12) (s.regs 1)),0x2c85c⟩) (by simp) (by rfl) (by
        try simp only [advanced,result,picked,h]
        simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        X86Block.Address.eval,put,write,blockPreservesFlags,cmp32_signed_le,
        compare_carry,BitVec.sub_eq_iff_eq_add,BitVec.ult,better,fraction,picked,advanced,result,steps]
        all_goals split <;> rfl)
      apply X86Routine.Prefix.step (middle := result s) (by simp) (by rfl) (by
        try simp only [advanced,result,picked,h]
        simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        X86Block.Address.eval,put,write,blockPreservesFlags,cmp32_signed_le,
        compare_carry,BitVec.sub_eq_iff_eq_add,BitVec.ult,better,fraction,picked,advanced,result,steps]
        all_goals split <;> rfl)
      exact .nil _
  exact run.transfer program [] decoded (by simp)

def initialized (s : X86Memory.State) := put (put s 0 0x2ba20) 2 0x7fffffff
def entry (s : X86Memory.State) : X86Control.State :=
  ⟨initialized s,some (compare32 (s.regs 1) 0x2ba20),
    if (s.regs 1).toNat≤178720 then 0x2c85e else 0x2c84f⟩

private theorem compare_zero (a b : Word) : (compare32 a b).zero=decide (a.toNat=b.toNat) := by
  apply Bool.eq_iff_iff.mpr
  simp [compare32,beq_iff_eq,BitVec.sub_eq_iff_eq_add,BitVec.toNat_inj]

/-- The original scan resets distance but deliberately keeps the old best
pointer. Empty arrays bypass the record loads. -/
theorem entry_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 4 ⟨s,f,0x2c841⟩ (entry s) := by
  have run : X86Routine.Prefix listed [] 4 ⟨s,f,0x2c841⟩ (entry s) := by
    apply X86Routine.Prefix.step (middle := ⟨put s 0 0x2ba20,f,0x2c846⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        put,write,initialized,entry,compare_carry,compare_zero,BitVec.ult]
      all_goals split <;> simp_all <;> omega)
    apply X86Routine.Prefix.step (middle := ⟨initialized s,f,0x2c84b⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        put,write,initialized,entry,compare_carry,compare_zero,BitVec.ult]
      all_goals split <;> simp_all <;> omega)
    apply X86Routine.Prefix.step (middle := ⟨initialized s,some (compare32 (s.regs 1) 0x2ba20),0x2c84d⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        put,write,initialized,entry,compare_carry,compare_zero,BitVec.ult]
      all_goals split <;> simp_all <;> omega)
    apply X86Routine.Prefix.step (middle := entry s) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        put,write,initialized,entry,compare_carry,compare_zero,BitVec.ult]
      all_goals split <;> simp_all <;> omega)
    exact .nil _
  exact run.transfer program [] decoded (by simp)

/-- Frame and register observations used to iterate the real scan body. -/
theorem fields (s : X86Memory.State) :
    (advanced s).memory=s.memory ∧ (advanced s).regs 0=s.regs 0+12 ∧
    (advanced s).regs 1=s.regs 1 ∧
    (advanced s).regs 2=(if better s then fraction s else s.regs 2) ∧
    (advanced s).regs 3=(if better s then s.regs 0 else s.regs 3) := by
  by_cases h : better s <;> simp [advanced,picked,h,put,write]
end Doom.Proofs.OriginalInterceptMinimum
