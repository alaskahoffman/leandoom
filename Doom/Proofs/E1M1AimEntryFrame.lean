import Doom.Proofs.E1M1ScanInterface
set_option backward.isDefEq.respectTransparency false
namespace Doom.Proofs.E1M1AimEntryFrame
open Verification X86 X86Memory X86Control BlockSummary
open E1M1InterceptSetup (Safe result)
attribute [local irreducible] load32 store32

/-- Static protection against the six setup stores, cursor update and callback
CALL. These are addresses relative to collection exit, before execution. -/
def SafeWord (sp a : Word) : Prop :=
  Safe sp a ∧ Apart a 0x2c028 ∧ Apart a (sp-28)

/-- The real handoff creates this return word; it is not an endpoint premise.
Word disjointness holds even for a wrapping 32-bit stack pointer. -/
theorem return_word (s : X86Memory.State) (n : Nat) :
    load32 (result s n).core.memory (s.regs 4-4)=0x2cb0b := by
  change load32 (OriginalInterceptSetup.prepared (OriginalInterceptSetup.called s)).memory _=_
  rw [E1M1InterceptSetup.memory]
  have sep : ∀ off∈[(8#32),12,16,20,24], Apart (s.regs 4-4) (s.regs 4-off) := by
    intro off member
    have base : ∀ off∈[(8#32),12,16,20,24], Apart (-(4#32)) (-off) := by
      intro off member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl|rfl|rfl|rfl|rfl <;> unfold Apart <;> decide
    simpa [BitVec.sub_eq_add_neg] using
      OriginalPathXStep.apart_translate (s.regs 4) (-(4#32)) (-off) (base off member)
  rw [load_store_apart _ _ _ _ (sep 24 (by simp)),
      load_store_apart _ _ _ _ (sep 20 (by simp)),
      load_store_apart _ _ _ _ (sep 16 (by simp)),
      load_store_apart _ _ _ _ (sep 12 (by simp)),
      load_store_apart _ _ _ _ (sep 8 (by simp)),load_store]

theorem return_safe (sp : Word) : Apart (sp-4) (sp-28) := by
  have small : Apart (-(4#32)) (-(28#32)) := by unfold Apart; decide
  simpa [BitVec.sub_eq_add_neg] using OriginalPathXStep.apart_translate sp (-(4#32)) (-(28#32)) small

/-- A separated word survives setup and the first scan/CALL together. -/
theorem preserved (s : X86Memory.State) (n : Nat) (out : X86Control.State)
    (frame : E1M1AimRepeatProgram.ReadFrame (result s n).core out)
    (a : Word) (safe : SafeWord (s.regs 4) a)
    (stack : (result s n).core.regs 4=s.regs 4-24) :
    load32 out.core.memory a=load32 s.memory a := by
  have push : (result s n).core.regs 4-4=s.regs 4-28 := by
    rw [stack]; simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  exact (frame a safe.2.1 (by rw [push]; exact safe.2.2)).trans
    (E1M1InterceptSetup.frame s a safe.1)
end Doom.Proofs.E1M1AimEntryFrame
