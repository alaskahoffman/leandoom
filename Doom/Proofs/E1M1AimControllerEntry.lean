import Doom.Proofs.E1M1AimThreeCalls
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
namespace Doom.Proofs.E1M1AimControllerEntry
open Verification X86 X86Memory X86Control BlockSummary Collision
attribute [local irreducible] load32 store32

def entry := OriginalBulletSlope.firstCall

def writes (s : X86Memory.State) : List Word :=
  [s.regs 4-4,s.regs 4-8,s.regs 4-12,s.regs 4-16,s.regs 4-20]

/-- Execute the authenticated controller prologue and first CALL in the same
program used by all three complete aiming queries. -/
theorem execution (s : X86Memory.State) (f : Option Flags) :
    X86ReturnCleanup.Prefix FloorCaller.cm E1M1AimProgramLink.program [] 9
      ⟨s,f,0x2d7c0⟩ (entry s f) := by
  exact (X86ReturnCleanup.lift (X86CodeMemory.lift_success
    (OriginalBulletSlope.first_execution s f) FloorCaller.cm)).transfer
      E1M1AimProgramLink.program E1M1AimTargetDecision.contains

theorem memory (s : X86Memory.State) (f : Option Flags) :
    (entry s f).core.memory=
      store32 (store32 (store32 (store32 (store32 s.memory
        (s.regs 4-4) (s.regs 3)) (s.regs 4-8) (s.regs 1))
        (s.regs 4-12) (s.regs 2)) (s.regs 4-16) (s.regs 6)) (s.regs 4-20) 0x2d7d5 := by
  simp [entry,OriginalBulletSlope.firstCall,OriginalBulletSlope.saved,X86Routine.pushWord,
    put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc]

/-- Only the five actual stack writes constrain preserved original words. -/
theorem frame (s : X86Memory.State) (f : Option Flags) (a : Word)
    (safe : ∀ b∈writes s, Apart a b) :
    load32 (entry s f).core.memory a=load32 s.memory a := by
  rw [memory]
  repeat rw [load_store_apart _ _ _ _ (safe _ (by simp [writes]))]

/-- The controller's shooter, angle, range, saved registers and return word
come from executing its prologue, not from an assumed first-call request. -/
theorem arguments (s : X86Memory.State) (f : Option Flags) (angle : Angle)
    (value : load32 s.memory (s.regs 0+32)=angle.raw.toBitVec)
    (safe : ∀ b∈OriginalBulletSlope.saveWrites s, Apart (s.regs 0+32) b) :
    (entry s f).pc=0x2bb80 ∧ (entry s f).flags=f ∧
    (entry s f).core.regs 4=s.regs 4-20 ∧
    (entry s f).core.regs 0=s.regs 0 ∧
    (entry s f).core.regs 1=angle.raw.toBitVec ∧
    (entry s f).core.regs 2=angle.raw.toBitVec ∧
    (entry s f).core.regs 3=0x04000000 ∧
    (entry s f).core.regs 6=s.regs 0 ∧
    (entry s f).core.regs 5=s.regs 5 ∧ (entry s f).core.regs 7=s.regs 7 ∧
    load32 (entry s f).core.memory ((entry s f).core.regs 4)=0x2d7d5 := by
  simp [entry,OriginalBulletSlope.firstCall,OriginalBulletSlope.saved,X86Routine.pushWord,
    put,write,OriginalBulletSlope.initial_angle s angle value safe,BitVec.sub_sub,load_store]

/-- The saved caller registers survive the later first-query return-word push,
including wraparound of the stack pointer. -/
theorem saved (s : X86Memory.State) (f : Option Flags) :
    load32 (entry s f).core.memory (s.regs 4-16)=s.regs 6 ∧
    load32 (entry s f).core.memory (s.regs 4-12)=s.regs 2 ∧
    load32 (entry s f).core.memory (s.regs 4-8)=s.regs 1 ∧
    load32 (entry s f).core.memory (s.regs 4-4)=s.regs 3 ∧
    load32 (entry s f).core.memory (s.regs 4)=load32 s.memory (s.regs 4) := by
  rw [memory]
  have apart (a b : Fin 32) (h : a≠b) := DeathStack.slots_apart (s.regs 4) a b h
  constructor
  · rw [load_store_apart _ _ _ _ (show Apart (s.regs 4-16) (s.regs 4-20) from apart 4 5 (by decide)),load_store]
  constructor
  · rw [load_store_apart _ _ _ _ (show Apart (s.regs 4-12) (s.regs 4-20) from apart 3 5 (by decide)),
      load_store_apart _ _ _ _ (show Apart (s.regs 4-12) (s.regs 4-16) from apart 3 4 (by decide)),load_store]
  constructor
  · rw [load_store_apart _ _ _ _ (show Apart (s.regs 4-8) (s.regs 4-20) from apart 2 5 (by decide)),
      load_store_apart _ _ _ _ (show Apart (s.regs 4-8) (s.regs 4-16) from apart 2 4 (by decide)),
      load_store_apart _ _ _ _ (show Apart (s.regs 4-8) (s.regs 4-12) from apart 2 3 (by decide)),load_store]
  constructor
  · rw [load_store_apart _ _ _ _ (show Apart (s.regs 4-4) (s.regs 4-20) from apart 1 5 (by decide)),
      load_store_apart _ _ _ _ (show Apart (s.regs 4-4) (s.regs 4-16) from apart 1 4 (by decide)),
      load_store_apart _ _ _ _ (show Apart (s.regs 4-4) (s.regs 4-12) from apart 1 3 (by decide)),
      load_store_apart _ _ _ _ (show Apart (s.regs 4-4) (s.regs 4-8) from apart 1 2 (by decide)),load_store]
  · rw [load_store_apart _ _ _ _ (show Apart (s.regs 4) (s.regs 4-20) from by have k : Apart (s.regs 4-(0#32)) (s.regs 4-20) := apart 0 5 (by decide); rw [BitVec.sub_zero] at k; exact k),
      load_store_apart _ _ _ _ (show Apart (s.regs 4) (s.regs 4-16) from by have k : Apart (s.regs 4-(0#32)) (s.regs 4-16) := apart 0 4 (by decide); rw [BitVec.sub_zero] at k; exact k),
      load_store_apart _ _ _ _ (show Apart (s.regs 4) (s.regs 4-12) from by have k : Apart (s.regs 4-(0#32)) (s.regs 4-12) := apart 0 3 (by decide); rw [BitVec.sub_zero] at k; exact k),
      load_store_apart _ _ _ _ (show Apart (s.regs 4) (s.regs 4-8) from by have k : Apart (s.regs 4-(0#32)) (s.regs 4-8) := apart 0 2 (by decide); rw [BitVec.sub_zero] at k; exact k),
      load_store_apart _ _ _ _ (show Apart (s.regs 4) (s.regs 4-4) from by have k : Apart (s.regs 4-(0#32)) (s.regs 4-4) := apart 0 1 (by decide); rw [BitVec.sub_zero] at k; exact k)]
end Doom.Proofs.E1M1AimControllerEntry
