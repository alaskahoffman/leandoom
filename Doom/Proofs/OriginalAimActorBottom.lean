import Doom.Proofs.E1M1AimActorRejectCycle
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalAimActorBottom
open Verification X86 X86Memory X86Control BlockSummary Collision
attribute [local irreducible] load32 store32
def code : List UInt8 := [0x8b,0x15,0xa8,0xb9,0x2,0x0,0x8b,0x41,0x14,0x29,0xd0,0x89,0xda,0xe8,0xed,0x18,0xff,0xff,0x8b,0x1d,0xe8,0xc1,0x2,0x0,0x39,0xd8,0x7e,0xc]
def bytesProgram (bytes : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2b881≤pc ∧ pc<0x2b89d then X86Routine.decodeAt bytes (pc-0x2b881) else none
def program := bytesProgram code
def listed : X86Routine.Program
  | 0x2b881 => some (.control (.block (.load 2 ⟨none,none,0,0x2b9a8⟩)),6)
  | 0x2b887 => some (.control (.block (.legacy (.load 0 1 20))),3)
  | 0x2b88a => some (.control (.block (.arithmetic (.sub 0 2))),2)
  | 0x2b88c => some (.control (.block (.legacy (.mov 2 3))),2)
  | 0x2b88e => some (.call (-59155),5)
  | 0x2b893 => some (.control (.block (.load 3 ⟨none,none,0,0x2c1e8⟩)),6)
  | 0x2b899 => some (.compareRegisters 0 3,2)
  | 0x2b89b => some (.jumpSigned 1 12,2)
  | _ => none

theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def z (s : X86Memory.State) := load32 s.memory (s.regs 1+20)
def eye (s : X86Memory.State) := load32 s.memory (0x2b9a8#32)
def eyeLoaded (s : X86Memory.State) := put s 2 (eye s)
def loaded (s : X86Memory.State) := put (eyeLoaded s) 0 (z s)
def subtracted (s : X86Memory.State) := put (loaded s) 0 (z s-eye s)
def argument (s : X86Memory.State) := put (subtracted s) 2 (s.regs 3)
def called (s : X86Memory.State) := X86Routine.pushWord (argument s) 0x2b893

def upper (s : X86Memory.State) := load32 s.memory (0x2c1e8#32)
def loadedUpper (s : X86Memory.State) := put s 3 (upper s)
def gate (s : X86Memory.State) : X86Control.State :=
  ⟨loadedUpper s,some (compare32 (s.regs 0) (upper s)),
    if (upper s).toInt < (s.regs 0).toInt then 0x2b89d else 0x2b8a9⟩

/-- Reuse the saved distance and compute the wrapped bottom numerator before
calling the real FixedDiv routine. -/
theorem call_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 5 ⟨s,f,0x2b881⟩ ⟨called s,none,0x1d180⟩ := by
  have run : X86Routine.Prefix listed [] 5 ⟨s,f,0x2b881⟩ ⟨called s,none,0x1d180⟩ := by
    apply X86Routine.Prefix.step (middle := ⟨eyeLoaded s,f,0x2b887⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,X86.write,z,eye,eyeLoaded,loaded,subtracted,argument,called,X86Routine.pushWord,upper,loadedUpper,gate,cmp32_signed_le])
    apply X86Routine.Prefix.step (middle := ⟨loaded s,f,0x2b88a⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,X86.write,z,eye,eyeLoaded,loaded,subtracted,argument,called,X86Routine.pushWord,upper,loadedUpper,gate,cmp32_signed_le])
    apply X86Routine.Prefix.step (middle := ⟨subtracted s,none,0x2b88c⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,X86.write,z,eye,eyeLoaded,loaded,subtracted,argument,called,X86Routine.pushWord,upper,loadedUpper,gate,cmp32_signed_le])
    apply X86Routine.Prefix.step (middle := ⟨argument s,none,0x2b88e⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,X86.write,z,eye,eyeLoaded,loaded,subtracted,argument,called,X86Routine.pushWord,upper,loadedUpper,gate,cmp32_signed_le])
    apply X86Routine.Prefix.step (middle := ⟨called s,none,0x1d180⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,X86.write,z,eye,eyeLoaded,loaded,subtracted,argument,called,X86Routine.pushWord,upper,loadedUpper,gate,cmp32_signed_le])
    exact .nil _
  exact run.transfer program [] decoded (by simp)

/-- A strictly greater bottom slope rejects; equality proceeds to selection. -/
theorem gate_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 3 ⟨s,f,0x2b893⟩ (gate s) := by
  have run : X86Routine.Prefix listed [] 3 ⟨s,f,0x2b893⟩ (gate s) := by
    apply X86Routine.Prefix.step (middle := ⟨loadedUpper s,f,0x2b899⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,X86.write,z,eye,eyeLoaded,loaded,subtracted,argument,called,X86Routine.pushWord,upper,loadedUpper,gate,cmp32_signed_le]
      all_goals split <;> simp_all)
    apply X86Routine.Prefix.step (middle := ⟨loadedUpper s,some (compare32 (s.regs 0) (upper s)),0x2b89b⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,X86.write,z,eye,eyeLoaded,loaded,subtracted,argument,called,X86Routine.pushWord,upper,loadedUpper,gate,cmp32_signed_le]
      all_goals split <;> simp_all)
    apply X86Routine.Prefix.step (middle := gate s) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,X86.write,z,eye,eyeLoaded,loaded,subtracted,argument,called,X86Routine.pushWord,upper,loadedUpper,gate,cmp32_signed_le]
      all_goals split <;> simp_all)
    exact .nil _
  exact run.transfer program [] decoded (by simp)

theorem operands (s : X86Memory.State) (distance targetZ shootZ : Fixed)
    (dist : s.regs 3=distance.raw.toBitVec)
    (z0 : z s=targetZ.raw.toBitVec) (eye0 : eye s=shootZ.raw.toBitVec) :
    (called s).regs 0=(targetZ-shootZ).raw.toBitVec ∧
    (called s).regs 2=distance.raw.toBitVec ∧
    (called s).regs 1=s.regs 1 ∧ (called s).regs 6=s.regs 6 ∧ (called s).regs 7=s.regs 7 ∧
    (called s).regs 4=s.regs 4-4 := by
  simp [called,argument,subtracted,loaded,eyeLoaded,X86Routine.pushWord,put,write,dist,z0,eye0]
  rfl
end Doom.Proofs.OriginalAimActorBottom
