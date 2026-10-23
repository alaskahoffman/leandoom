import Doom.Proofs.E1M1AimSource
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1AimWall
open Verification X86 X86Memory X86Control BlockSummary
open OriginalAimGuard
attribute [local irreducible] load32 store32

def Safe (sp a : Word) : Prop := ∀ off∈[(4#32),8,12,16,20,24], Apart a (sp-off)

theorem saved_memory (s : X86Memory.State) : (saved s).memory=
    store32 (store32 (store32 (store32 (store32 (store32 s.memory
      (s.regs 4-4) (s.regs 3)) (s.regs 4-8) (s.regs 1))
      (s.regs 4-12) (s.regs 2)) (s.regs 4-16) (s.regs 6))
      (s.regs 4-20) (s.regs 7)) (s.regs 4-24) (s.regs 5) := by
  simp [saved,save6,save5,save4,save3,save2,save1,X86Routine.pushWord,put,write,
    BitVec.sub_eq_add_neg,BitVec.add_assoc]

theorem saved_frame (s : X86Memory.State) (a : Word) (safe : Safe (s.regs 4) a) :
    load32 (saved s).memory a=load32 s.memory a := by
  rw [saved_memory]
  rw [load_store_apart _ _ _ _ (safe 24 (by simp)),load_store_apart _ _ _ _ (safe 20 (by simp)),
    load_store_apart _ _ _ _ (safe 16 (by simp)),load_store_apart _ _ _ _ (safe 12 (by simp)),
    load_store_apart _ _ _ _ (safe 8 (by simp)),load_store_apart _ _ _ _ (safe 4 (by simp))]

theorem saved_byte (s : X86Memory.State) (a : Word) (safe : Safe (s.regs 4) a) :
    (saved s).memory a=s.memory a := by
  have h := congrArg (fun w : Word => w.extractLsb' 0 8) (saved_frame s a safe)
  rw [E1M1PathCell.low_byte,E1M1PathCell.low_byte] at h
  exact h

theorem return_safe (sp : Word) : Safe sp sp := by
  intro off member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  have small : Apart (0#32) (-off) := by
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl <;> unfold Apart <;> decide
  simpa only [BitVec.sub_eq_add_neg,BitVec.add_zero] using
    OriginalPathXStep.apart_translate sp (0#32) (-off) small

/-- The actual callback's tag branch agrees with the live source's line/thing
split, using the reached record rather than a supplied branch result. -/
theorem entry_record (s : X86Memory.State) (hit : Collision.Intercept) (pointer : Word)
    (record : OriginalLineFinish.RecordAt s.memory (s.regs 0) hit pointer)
    (tagSafe : Safe (s.regs 4) (s.regs 0+4)) :
    (entry s).pc=(if hit.isLine then 0x2b772 else 0x2b81a) := by
  unfold entry kind
  have tag : load32 s.memory (s.regs 0+4)=(if hit.isLine then (1#32) else 0) := record.2.1
  rw [saved_frame s _ tagSafe,tag]
  cases hit.isLine <;> rfl

def returned (s : X86Memory.State) := stopped (lineCore (prepared s))

theorem returned_fields (s : X86Memory.State) :
    (returned s).core.regs 0=0 ∧ (returned s).core.regs 4=s.regs 4+4 ∧
    (returned s).core.memory=(saved s).memory ∧
    (returned s).pc=(load32 s.memory (s.regs 4)).toNat := by
  have keep := saved_frame s (s.regs 4) (return_safe _)
  simp [returned,stopped,u6,u5,u4,u3,u2,u1,u0,pop,lineCore,prepared,saved,
    save6,save5,save4,save3,save2,save1,X86Routine.pushWord,put,write,
    BitVec.sub_eq_add_neg,BitVec.add_assoc] at keep ⊢
  exact congrArg BitVec.toNat keep

/-- A one-sided wall takes the real false-return branch, including all six
saved registers and RET. This is a complete callback path, not a stub. -/
theorem execution (s : X86Memory.State) (f : Option Flags) (hit : Collision.Intercept) (pointer : Word)
    (record : OriginalLineFinish.RecordAt s.memory (s.regs 0) hit pointer)
    (isLine : hit.isLine=true)
    (tagSafe : Safe (s.regs 4) (s.regs 0+4))
    (pointerSafe : Safe (s.regs 4) (s.regs 0+8))
    (flagsSafe : Safe (s.regs 4) (pointer+16))
    (oneSided : s.memory (pointer+16) &&& (4#8)=0) :
    X86CodeMemory.Prefix FloorCaller.cm program [] 20 ⟨s,f,0x2b760⟩ (returned s) := by
  have pc : (entry s).pc=0x2b772 := by rw [entry_record s hit pointer record tagSafe,isLine]; rfl
  have ptr : line (prepared s)=pointer := by
    change load32 (saved s).memory (s.regs 0+8)=pointer
    rw [saved_frame s _ pointerSafe]; exact record.2.2
  have zero : bits (prepared s)=0 := by
    unfold bits
    rw [ptr]
    change (saved s).memory (pointer+16) &&& (4#8)=0
    rw [saved_byte s _ flagsSafe,oneSided]
  have gatePc : (lineGate (prepared s)).pc=0x2b8d2 := by simp [lineGate,zero]
  have middle := line_execution (prepared s) (entry s).flags
  change X86Routine.Prefix program [] 3 ⟨(entry s).core,(entry s).flags,0x2b772⟩ _ at middle
  rw [OriginalPathXStep.at_pc _ _ pc] at middle
  have tail := stop_execution (lineCore (prepared s)) (lineGate (prepared s)).flags
  change X86Routine.Prefix program [] 8
    ⟨(lineGate (prepared s)).core,(lineGate (prepared s)).flags,0x2b8d2⟩ _ at tail
  rw [OriginalPathXStep.at_pc _ _ gatePc] at tail
  exact X86CodeMemory.lift_success (OriginalGroupBounds.prefix_join
    (OriginalGroupBounds.prefix_join (entry_execution s f) middle) tail) FloorCaller.cm
end Doom.Proofs.E1M1AimWall
