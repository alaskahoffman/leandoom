import Doom.Proofs.E1M1AimDistance
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalAimFloor
open Verification X86 X86Memory X86Control BlockSummary
attribute [local irreducible] load32 store32
def code : List UInt8 := [0x8b,0x71,0x32,0x89,0xc3,0x8b,0x41,0x2e,0x8b,0x3e,0x3b,0x38,0x74,0x1d,0xa1,0x30,0xc0,0x2,0x0,0x2b,0x5,0xa8,0xb9,0x2,0x0,0xe8,0xbc,0x19,0xff,0xff,0x3b,0x5,0xe4,0xc1,0x2,0x0,0x7e,0x5,0xa3,0xe4,0xc1,0x2,0x0]
def bytesProgram (bytes : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2b7a6≤pc ∧ pc<0x2b7d1 then X86Routine.decodeAt bytes (pc-0x2b7a6) else none
def program := bytesProgram code
def listed : X86Routine.Program
  | 0x2b7a6 => some (.control (.block (.legacy (.load 6 1 50))),3)
  | 0x2b7a9 => some (.control (.block (.legacy (.mov 3 0))),2)
  | 0x2b7ab => some (.control (.block (.legacy (.load 0 1 46))),3)
  | 0x2b7ae => some (.control (.block (.legacy (.load 7 6 0))),2)
  | 0x2b7b0 => some (.control (.cmpMemory 7 ⟨some 0,none,0,0⟩),2)
  | 0x2b7b2 => some (.control (.jumpZero true 29),2)
  | 0x2b7b4 => some (.control (.block (.load 0 ⟨none,none,0,0x2c030⟩)),5)
  | 0x2b7b9 => some (.subMemory 0 ⟨none,none,0,0x2b9a8⟩,6)
  | 0x2b7bf => some (.call (-58948),5)
  | 0x2b7c4 => some (.control (.cmpMemory 0 ⟨none,none,0,0x2c1e4⟩),6)
  | 0x2b7ca => some (.jumpSigned 1 5,2)
  | 0x2b7cc => some (.control (.storeEax 0x2c1e4),5)
  | _ => none

theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def back (s : X86Memory.State) := load32 s.memory (s.regs 1+(50#32))
def front (s : X86Memory.State) := load32 s.memory (s.regs 1+(46#32))
def bf (s : X86Memory.State) := load32 s.memory (back s)
def ff (s : X86Memory.State) := load32 s.memory (front s)
def c1 (s : X86Memory.State) := put s 6 (back s)
def c2 (s : X86Memory.State) := put (c1 s) 3 (s.regs 0)
def c3 (s : X86Memory.State) := put (c2 s) 0 (front s)
def c4 (s : X86Memory.State) := put (c3 s) 7 (bf s)
def gate (s : X86Memory.State) : X86Control.State :=
  ⟨c4 s,some (compare32 (bf s) (ff s)),if bf s=ff s then 0x2b7d1 else 0x2b7b4⟩
def low (s : X86Memory.State) := load32 s.memory (0x2c030#32)
def shootZ (s : X86Memory.State) := load32 s.memory (0x2b9a8#32)
def numerator (s : X86Memory.State) := low s-shootZ s
def loaded (s : X86Memory.State) := put s 0 (low s)
def argument (s : X86Memory.State) := put s 0 (numerator s)
def called (s : X86Memory.State) := X86Routine.pushWord (argument s) 0x2b7c4
def old (s : X86Memory.State) := load32 s.memory (0x2c1e4#32)
def raised (s : X86Memory.State) := {s with memory:=store32 s.memory (0x2c1e4#32) (s.regs 0)}
def clipped (s : X86Memory.State) : X86Control.State :=
  ⟨if (s.regs 0).toInt≤(old s).toInt then s else raised s,
    some (compare32 (s.regs 0) (old s)),0x2b7d1⟩

theorem gate_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 6 ⟨s,f,0x2b7a6⟩ (gate s) := by
  have run : X86Routine.Prefix listed [] 6 ⟨s,f,0x2b7a6⟩ (gate s) := by
    apply X86Routine.Prefix.step (middle := ⟨c1 s,f,0x2b7a9⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,back,front,bf,ff,c1,c2,c3,c4,gate,low,shootZ,numerator,loaded,argument,called,X86Routine.pushWord,old,raised,clipped,cmp32_zero,cmp32_signed_le]
      all_goals split <;> simp_all)
    apply X86Routine.Prefix.step (middle := ⟨c2 s,f,0x2b7ab⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,back,front,bf,ff,c1,c2,c3,c4,gate,low,shootZ,numerator,loaded,argument,called,X86Routine.pushWord,old,raised,clipped,cmp32_zero,cmp32_signed_le]
      all_goals split <;> simp_all)
    apply X86Routine.Prefix.step (middle := ⟨c3 s,f,0x2b7ae⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,back,front,bf,ff,c1,c2,c3,c4,gate,low,shootZ,numerator,loaded,argument,called,X86Routine.pushWord,old,raised,clipped,cmp32_zero,cmp32_signed_le]
      all_goals split <;> simp_all)
    apply X86Routine.Prefix.step (middle := ⟨c4 s,f,0x2b7b0⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,back,front,bf,ff,c1,c2,c3,c4,gate,low,shootZ,numerator,loaded,argument,called,X86Routine.pushWord,old,raised,clipped,cmp32_zero,cmp32_signed_le]
      all_goals split <;> simp_all)
    apply X86Routine.Prefix.step (middle := ⟨c4 s,some (compare32 (bf s) (ff s)),0x2b7b2⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,back,front,bf,ff,c1,c2,c3,c4,gate,low,shootZ,numerator,loaded,argument,called,X86Routine.pushWord,old,raised,clipped,cmp32_zero,cmp32_signed_le]
      all_goals split <;> simp_all)
    apply X86Routine.Prefix.step (middle := gate s) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,back,front,bf,ff,c1,c2,c3,c4,gate,low,shootZ,numerator,loaded,argument,called,X86Routine.pushWord,old,raised,clipped,cmp32_zero,cmp32_signed_le]
      all_goals split <;> simp_all)
    exact .nil _
  exact run.transfer program [] decoded (by simp)

theorem call_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 3 ⟨s,f,0x2b7b4⟩ (⟨called s,none,0x1d180⟩) := by
  have run : X86Routine.Prefix listed [] 3 ⟨s,f,0x2b7b4⟩ (⟨called s,none,0x1d180⟩) := by
    apply X86Routine.Prefix.step (middle := ⟨loaded s,f,0x2b7b9⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,back,front,bf,ff,c1,c2,c3,c4,gate,low,shootZ,numerator,loaded,argument,called,X86Routine.pushWord,old,raised,clipped,cmp32_zero,cmp32_signed_le]
      all_goals split <;> simp_all)
    apply X86Routine.Prefix.step (middle := ⟨argument s,none,0x2b7bf⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,back,front,bf,ff,c1,c2,c3,c4,gate,low,shootZ,numerator,loaded,argument,called,X86Routine.pushWord,old,raised,clipped,cmp32_zero,cmp32_signed_le]
      all_goals split <;> simp_all)
    apply X86Routine.Prefix.step (middle := ⟨called s,none,0x1d180⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,back,front,bf,ff,c1,c2,c3,c4,gate,low,shootZ,numerator,loaded,argument,called,X86Routine.pushWord,old,raised,clipped,cmp32_zero,cmp32_signed_le]
      all_goals split <;> simp_all)
    exact .nil _
  exact run.transfer program [] decoded (by simp)

theorem clip_execution (s : X86Memory.State) (f : Option Flags) :
    ∃ n, n≤3 ∧ X86Routine.Prefix program [] n ⟨s,f,0x2b7c4⟩ (clipped s) := by
  by_cases le : (s.regs 0).toInt≤(old s).toInt
  · simp only [old] at le
    have run : X86Routine.Prefix listed [] 2 ⟨s,f,0x2b7c4⟩ (clipped s) := by
      apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (s.regs 0) (old s)),0x2b7ca⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,back,front,bf,ff,c1,c2,c3,c4,gate,low,shootZ,numerator,loaded,argument,called,X86Routine.pushWord,old,raised,clipped,cmp32_zero,cmp32_signed_le,le])
      apply X86Routine.Prefix.step (middle := clipped s) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,back,front,bf,ff,c1,c2,c3,c4,gate,low,shootZ,numerator,loaded,argument,called,X86Routine.pushWord,old,raised,clipped,cmp32_zero,cmp32_signed_le,le])
      exact .nil _
    exact ⟨2,by omega,run.transfer program [] decoded (by simp)⟩
  · simp only [old] at le
    have run : X86Routine.Prefix listed [] 3 ⟨s,f,0x2b7c4⟩ (clipped s) := by
      apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (s.regs 0) (old s)),0x2b7ca⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,back,front,bf,ff,c1,c2,c3,c4,gate,low,shootZ,numerator,loaded,argument,called,X86Routine.pushWord,old,raised,clipped,cmp32_zero,cmp32_signed_le,le])
      apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (s.regs 0) (old s)),0x2b7cc⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,back,front,bf,ff,c1,c2,c3,c4,gate,low,shootZ,numerator,loaded,argument,called,X86Routine.pushWord,old,raised,clipped,cmp32_zero,cmp32_signed_le,le])
      apply X86Routine.Prefix.step (middle := clipped s) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,back,front,bf,ff,c1,c2,c3,c4,gate,low,shootZ,numerator,loaded,argument,called,X86Routine.pushWord,old,raised,clipped,cmp32_zero,cmp32_signed_le,le])
      exact .nil _
    exact ⟨3,by omega,run.transfer program [] decoded (by simp)⟩
end Doom.Proofs.OriginalAimFloor
