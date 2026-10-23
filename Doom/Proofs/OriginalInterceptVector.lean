import Doom.Proofs.OriginalLineSecondPoint
import Doom.Proofs.OriginalDivMemory
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalInterceptVector
open Verification X86 X86Memory X86Control BlockSummary
def code : List UInt8 := [0x53,0x51,0x56,0x57,0x55,0x89,0xc6,0x89,0xd1,0x8b,0x58,0x8,0x8b,0x42,0xc,0xc1,0xf8,0x8,0xf7,0xeb,0xf,0xac,0xd0,0x10,0x89,0xc7,0x8b,0x41,0x8,0x8b,0x5e,0xc,0xc1,0xf8,0x8,0xf7,0xeb,0xf,0xac,0xd0,0x10,0x29,0xc7,0x75,0x4,0x31,0xc0,0xeb,0x2d,0x8b,0x1,0x2b,0x6,0x8b,0x59,0xc,0xc1,0xf8,0x8,0xf7,0xeb,0xf,0xac,0xd0,0x10,0x89,0xc5,0x8b,0x46,0x4,0x2b,0x41,0x4,0x8b,0x59,0x8,0xc1,0xf8,0x8,0xf7,0xeb,0xf,0xac,0xd0,0x10,0x89,0xfa,0x1,0xe8,0xe8,0x52,0xe,0xff,0xff,0x5d,0x5f,0x5e,0x59,0x5b,0xc3]
def bytesProgram (bytes : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2c2d0≤pc ∧ pc<0x2c334 then X86Routine.decodeAtWithSubFlags bytes (pc-0x2c2d0)
  else OriginalDivMemory.program pc
def program := bytesProgram code

def listed : X86Routine.Program
  | 0x2c2d0 => some (.push 3,1)
  | 0x2c2d1 => some (.push 1,1)
  | 0x2c2d2 => some (.push 6,1)
  | 0x2c2d3 => some (.push 7,1)
  | 0x2c2d4 => some (.push 5,1)
  | 0x2c2d5 => some (.control (.block (.legacy (.mov 6 0))),2)
  | 0x2c2d7 => some (.control (.block (.legacy (.mov 1 2))),2)
  | 0x2c2d9 => some (.control (.block (.legacy (.load 3 0 8))),3)
  | 0x2c2dc => some (.control (.block (.legacy (.load 0 2 12))),3)
  | 0x2c2df => some (.sar 0 8,3)
  | 0x2c2e2 => some (.control (.block (.arithmetic (.imul 3))),2)
  | 0x2c2e4 => some (.control (.block (.arithmetic (.shrd 0 2 16))),4)
  | 0x2c2e8 => some (.control (.block (.legacy (.mov 7 0))),2)
  | 0x2c2ea => some (.control (.block (.legacy (.load 0 1 8))),3)
  | 0x2c2ed => some (.control (.block (.legacy (.load 3 6 12))),3)
  | 0x2c2f0 => some (.sar 0 8,3)
  | 0x2c2f3 => some (.control (.block (.arithmetic (.imul 3))),2)
  | 0x2c2f5 => some (.control (.block (.arithmetic (.shrd 0 2 16))),4)
  | 0x2c2f9 => some (.subRegistersWithFlags 7 0,2)
  | 0x2c2fb => some (.control (.jumpZero false 4),2)
  | 0x2c2fd => some (.xorRegister 0 0,2)
  | 0x2c2ff => some (.jump 45,2)
  | 0x2c301 => some (.control (.block (.legacy (.load 0 1 0))),2)
  | 0x2c303 => some (.subMemory 0 ⟨some 6,none,0,0⟩,2)
  | 0x2c305 => some (.control (.block (.legacy (.load 3 1 12))),3)
  | 0x2c308 => some (.sar 0 8,3)
  | 0x2c30b => some (.control (.block (.arithmetic (.imul 3))),2)
  | 0x2c30d => some (.control (.block (.arithmetic (.shrd 0 2 16))),4)
  | 0x2c311 => some (.control (.block (.legacy (.mov 5 0))),2)
  | 0x2c313 => some (.control (.block (.legacy (.load 0 6 4))),3)
  | 0x2c316 => some (.subMemory 0 ⟨some 1,none,0,4⟩,3)
  | 0x2c319 => some (.control (.block (.legacy (.load 3 1 8))),3)
  | 0x2c31c => some (.sar 0 8,3)
  | 0x2c31f => some (.control (.block (.arithmetic (.imul 3))),2)
  | 0x2c321 => some (.control (.block (.arithmetic (.shrd 0 2 16))),4)
  | 0x2c325 => some (.control (.block (.legacy (.mov 2 7))),2)
  | 0x2c327 => some (.control (.block (.arithmetic (.add 0 5))),2)
  | 0x2c329 => some (.call (-61870),5)
  | 0x2c32e => some (.pop 5,1)
  | 0x2c32f => some (.pop 7,1)
  | 0x2c330 => some (.pop 6,1)
  | 0x2c331 => some (.pop 1,1)
  | 0x2c332 => some (.pop 3,1)
  | 0x2c333 => some (.ret,1)
  | _ => none

theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

theorem contains_div (pc : Nat) (h : OriginalDivMemory.program pc≠none) :
    program pc=OriginalDivMemory.program pc := by
  have range : 0x1d180≤pc ∧ pc<0x1d1c1 := by
    by_cases r : 0x1d180≤pc ∧ pc<0x1d1c1
    · exact r
    · simp [OriginalDivMemory.program,OriginalDivMemory.bytesProgram,r] at h
  simp [program,bytesProgram,show ¬(0x2c2d0≤pc ∧ pc<0x2c334) by omega]
def prepare1 (s : X86Memory.State) := X86Routine.pushWord s (s.regs 3)
def prepare2 (s : X86Memory.State) := X86Routine.pushWord (prepare1 s) ((prepare1 s).regs 1)
def prepare3 (s : X86Memory.State) := X86Routine.pushWord (prepare2 s) ((prepare2 s).regs 6)
def prepare4 (s : X86Memory.State) := X86Routine.pushWord (prepare3 s) ((prepare3 s).regs 7)
def prepare5 (s : X86Memory.State) := X86Routine.pushWord (prepare4 s) ((prepare4 s).regs 5)
def prepare6 (s : X86Memory.State) := put (prepare5 s) 6 ((prepare5 s).regs 0)
def prepare7 (s : X86Memory.State) := put (prepare6 s) 1 ((prepare6 s).regs 2)
def prepare := prepare7
theorem prepare_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 7 ⟨s,f,0x2c2d0⟩ ⟨prepare s,f,0x2c2d9⟩ := by
  have path : X86Routine.Prefix listed [] 7 ⟨s,f,0x2c2d0⟩ ⟨prepare s,f,0x2c2d9⟩ := by
    apply X86Routine.Prefix.step (middle := ⟨prepare1 s,f,0x2c2d1⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,prepare1])
    apply X86Routine.Prefix.step (middle := ⟨prepare2 s,f,0x2c2d2⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,prepare1,prepare2])
    apply X86Routine.Prefix.step (middle := ⟨prepare3 s,f,0x2c2d3⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,prepare1,prepare2,prepare3])
    apply X86Routine.Prefix.step (middle := ⟨prepare4 s,f,0x2c2d4⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,prepare1,prepare2,prepare3,prepare4])
    apply X86Routine.Prefix.step (middle := ⟨prepare5 s,f,0x2c2d5⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,prepare1,prepare2,prepare3,prepare4,prepare5])
    apply X86Routine.Prefix.step (middle := ⟨prepare6 s,f,0x2c2d7⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,prepare1,prepare2,prepare3,prepare4,prepare5,prepare6])
    apply X86Routine.Prefix.step (middle := ⟨prepare7 s,f,0x2c2d9⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,prepare1,prepare2,prepare3,prepare4,prepare5,prepare6,prepare7])
    exact .nil _
  exact path.transfer program [] decoded (by simp)

def den1 (s : X86Memory.State) := put s 3 (load32 s.memory (s.regs 0+(8#32)))
def den2 (s : X86Memory.State) := put (den1 s) 0 (load32 (den1 s).memory ((den1 s).regs 2+(12#32)))
def den3 (s : X86Memory.State) := put (den2 s) 0 (((den2 s).regs 0).sshiftRight 8)
def den4 (s : X86Memory.State) := X86Block.execute (.arithmetic (.imul 3)) (den3 s)
def den5 (s : X86Memory.State) := multiply (den3 s)
def den6 (s : X86Memory.State) := put (den5 s) 7 ((den5 s).regs 0)
def den7 (s : X86Memory.State) := put (den6 s) 0 (load32 (den6 s).memory ((den6 s).regs 1+(8#32)))
def den8 (s : X86Memory.State) := put (den7 s) 3 (load32 (den7 s).memory ((den7 s).regs 6+(12#32)))
def den9 (s : X86Memory.State) := put (den8 s) 0 (((den8 s).regs 0).sshiftRight 8)
def den10 (s : X86Memory.State) := X86Block.execute (.arithmetic (.imul 3)) (den9 s)
def den11 (s : X86Memory.State) := multiply (den9 s)
def den12 (s : X86Memory.State) := put (den11 s) 7 ((den11 s).regs 7-(den11 s).regs 0)
def den := den12
theorem den_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 12 ⟨s,f,0x2c2d9⟩ ⟨den s,some (compare32 ((den11 s).regs 7) ((den11 s).regs 0)),0x2c2fb⟩ := by
  have path : X86Routine.Prefix listed [] 12 ⟨s,f,0x2c2d9⟩ ⟨den s,some (compare32 ((den11 s).regs 7) ((den11 s).regs 0)),0x2c2fb⟩ := by
    apply X86Routine.Prefix.step (middle := ⟨den1 s,f,0x2c2dc⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,den1])
    apply X86Routine.Prefix.step (middle := ⟨den2 s,f,0x2c2df⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,den1,den2])
    apply X86Routine.Prefix.step (middle := ⟨den3 s,none,0x2c2e2⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,den1,den2,den3])
    apply X86Routine.Prefix.step (middle := ⟨den4 s,none,0x2c2e4⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,den1,den2,den3,den4])
    apply X86Routine.Prefix.step (middle := ⟨den5 s,none,0x2c2e8⟩) (by simp) (by rfl) (by simpa [X86Routine.execute,X86Control.execute,den5,den4,blockPreservesFlags] using congrArg (fun c => some (X86Control.State.mk c none 0x2c2e8)) (multiply_correct (den3 s)))
    apply X86Routine.Prefix.step (middle := ⟨den6 s,none,0x2c2ea⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,den1,den2,den3,den4,den5,den6])
    apply X86Routine.Prefix.step (middle := ⟨den7 s,none,0x2c2ed⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,den1,den2,den3,den4,den5,den6,den7])
    apply X86Routine.Prefix.step (middle := ⟨den8 s,none,0x2c2f0⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,den1,den2,den3,den4,den5,den6,den7,den8])
    apply X86Routine.Prefix.step (middle := ⟨den9 s,none,0x2c2f3⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,den1,den2,den3,den4,den5,den6,den7,den8,den9])
    apply X86Routine.Prefix.step (middle := ⟨den10 s,none,0x2c2f5⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,den1,den2,den3,den4,den5,den6,den7,den8,den9,den10])
    apply X86Routine.Prefix.step (middle := ⟨den11 s,none,0x2c2f9⟩) (by simp) (by rfl) (by simpa [X86Routine.execute,X86Control.execute,den11,den10,blockPreservesFlags] using congrArg (fun c => some (X86Control.State.mk c none 0x2c2f9)) (multiply_correct (den9 s)))
    apply X86Routine.Prefix.step (middle := ⟨den12 s,some (compare32 ((den11 s).regs 7) ((den11 s).regs 0)),0x2c2fb⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,den1,den2,den3,den4,den5,den6,den7,den8,den9,den10,den11,den12])
    exact .nil _
  exact path.transfer program [] decoded (by simp)

def num1 (s : X86Memory.State) := put s 0 (load32 s.memory (s.regs 1+(0#32)))
def num2 (s : X86Memory.State) := put (num1 s) 0 ((num1 s).regs 0-load32 (num1 s).memory ((num1 s).regs 6))
def num3 (s : X86Memory.State) := put (num2 s) 3 (load32 (num2 s).memory ((num2 s).regs 1+(12#32)))
def num4 (s : X86Memory.State) := put (num3 s) 0 (((num3 s).regs 0).sshiftRight 8)
def num5 (s : X86Memory.State) := X86Block.execute (.arithmetic (.imul 3)) (num4 s)
def num6 (s : X86Memory.State) := multiply (num4 s)
def num7 (s : X86Memory.State) := put (num6 s) 5 ((num6 s).regs 0)
def num8 (s : X86Memory.State) := put (num7 s) 0 (load32 (num7 s).memory ((num7 s).regs 6+(4#32)))
def num9 (s : X86Memory.State) := put (num8 s) 0 ((num8 s).regs 0-load32 (num8 s).memory ((num8 s).regs 1+(4#32)))
def num10 (s : X86Memory.State) := put (num9 s) 3 (load32 (num9 s).memory ((num9 s).regs 1+(8#32)))
def num11 (s : X86Memory.State) := put (num10 s) 0 (((num10 s).regs 0).sshiftRight 8)
def num12 (s : X86Memory.State) := X86Block.execute (.arithmetic (.imul 3)) (num11 s)
def num13 (s : X86Memory.State) := multiply (num11 s)
def num14 (s : X86Memory.State) := put (num13 s) 2 ((num13 s).regs 7)
def num15 (s : X86Memory.State) := put (num14 s) 0 ((num14 s).regs 0+(num14 s).regs 5)
def num16 (s : X86Memory.State) := X86Routine.pushWord (num15 s) 0x2c32e
def num := num16
theorem num_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 16 ⟨s,f,0x2c301⟩ ⟨num s,none,0x1d180⟩ := by
  have path : X86Routine.Prefix listed [] 16 ⟨s,f,0x2c301⟩ ⟨num s,none,0x1d180⟩ := by
    apply X86Routine.Prefix.step (middle := ⟨num1 s,f,0x2c303⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,num1])
    apply X86Routine.Prefix.step (middle := ⟨num2 s,none,0x2c305⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,num1,num2])
    apply X86Routine.Prefix.step (middle := ⟨num3 s,none,0x2c308⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,num1,num2,num3])
    apply X86Routine.Prefix.step (middle := ⟨num4 s,none,0x2c30b⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,num1,num2,num3,num4])
    apply X86Routine.Prefix.step (middle := ⟨num5 s,none,0x2c30d⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,num1,num2,num3,num4,num5])
    apply X86Routine.Prefix.step (middle := ⟨num6 s,none,0x2c311⟩) (by simp) (by rfl) (by simpa [X86Routine.execute,X86Control.execute,num6,num5,blockPreservesFlags] using congrArg (fun c => some (X86Control.State.mk c none 0x2c311)) (multiply_correct (num4 s)))
    apply X86Routine.Prefix.step (middle := ⟨num7 s,none,0x2c313⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,num1,num2,num3,num4,num5,num6,num7])
    apply X86Routine.Prefix.step (middle := ⟨num8 s,none,0x2c316⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,num1,num2,num3,num4,num5,num6,num7,num8])
    apply X86Routine.Prefix.step (middle := ⟨num9 s,none,0x2c319⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,num1,num2,num3,num4,num5,num6,num7,num8,num9])
    apply X86Routine.Prefix.step (middle := ⟨num10 s,none,0x2c31c⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,num1,num2,num3,num4,num5,num6,num7,num8,num9,num10])
    apply X86Routine.Prefix.step (middle := ⟨num11 s,none,0x2c31f⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,num1,num2,num3,num4,num5,num6,num7,num8,num9,num10,num11])
    apply X86Routine.Prefix.step (middle := ⟨num12 s,none,0x2c321⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,num1,num2,num3,num4,num5,num6,num7,num8,num9,num10,num11,num12])
    apply X86Routine.Prefix.step (middle := ⟨num13 s,none,0x2c325⟩) (by simp) (by rfl) (by simpa [X86Routine.execute,X86Control.execute,num13,num12,blockPreservesFlags] using congrArg (fun c => some (X86Control.State.mk c none 0x2c325)) (multiply_correct (num11 s)))
    apply X86Routine.Prefix.step (middle := ⟨num14 s,none,0x2c327⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,num1,num2,num3,num4,num5,num6,num7,num8,num9,num10,num11,num12,num13,num14])
    apply X86Routine.Prefix.step (middle := ⟨num15 s,none,0x2c329⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,num1,num2,num3,num4,num5,num6,num7,num8,num9,num10,num11,num12,num13,num14,num15])
    apply X86Routine.Prefix.step (middle := ⟨num16 s,none,0x1d180⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,num1,num2,num3,num4,num5,num6,num7,num8,num9,num10,num11,num12,num13,num14,num15,num16])
    exact .nil _
  exact path.transfer program [] decoded (by simp)

def pops1 (s : X86Memory.State) := put (put s 4 (s.regs 4+(4#32))) 5 (load32 s.memory (s.regs 4))
def pops2 (s : X86Memory.State) := put (put (pops1 s) 4 ((pops1 s).regs 4+(4#32))) 7 (load32 (pops1 s).memory ((pops1 s).regs 4))
def pops3 (s : X86Memory.State) := put (put (pops2 s) 4 ((pops2 s).regs 4+(4#32))) 6 (load32 (pops2 s).memory ((pops2 s).regs 4))
def pops4 (s : X86Memory.State) := put (put (pops3 s) 4 ((pops3 s).regs 4+(4#32))) 1 (load32 (pops3 s).memory ((pops3 s).regs 4))
def pops5 (s : X86Memory.State) := put (put (pops4 s) 4 ((pops4 s).regs 4+(4#32))) 3 (load32 (pops4 s).memory ((pops4 s).regs 4))
def pops := pops5
theorem pops_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 5 ⟨s,f,0x2c32e⟩ ⟨pops s,f,0x2c333⟩ := by
  have path : X86Routine.Prefix listed [] 5 ⟨s,f,0x2c32e⟩ ⟨pops s,f,0x2c333⟩ := by
    apply X86Routine.Prefix.step (middle := ⟨pops1 s,f,0x2c32f⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,pops1])
    apply X86Routine.Prefix.step (middle := ⟨pops2 s,f,0x2c330⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,pops1,pops2])
    apply X86Routine.Prefix.step (middle := ⟨pops3 s,f,0x2c331⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,pops1,pops2,pops3])
    apply X86Routine.Prefix.step (middle := ⟨pops4 s,f,0x2c332⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,pops1,pops2,pops3,pops4])
    apply X86Routine.Prefix.step (middle := ⟨pops5 s,f,0x2c333⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,pops1,pops2,pops3,pops4,pops5])
    exact .nil _
  exact path.transfer program [] decoded (by simp)

def finish (s : X86Memory.State) (f : Option Flags) : X86Control.State :=
  ⟨put (pops s) 4 (s.regs 4+(24#32)), f, (load32 s.memory (s.regs 4+(20#32))).toNat⟩
theorem finish_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 6 ⟨s,f,0x2c32e⟩ (finish s f) := by
  have last : X86Routine.Prefix listed [] 1 ⟨pops s,f,0x2c333⟩ (finish s f) := by
    apply X86Routine.Prefix.step (middle:=finish s f) (by simp) (by rfl) (by
      simp [X86Routine.execute,finish,pops,pops1,pops2,pops3,pops4,pops5,put,write,BitVec.add_assoc])
    exact .nil _
  exact OriginalGroupBounds.prefix_join (pops_execution s f) (last.transfer program [] decoded (by simp))

def denFlags (s : X86Memory.State) := compare32 ((den11 s).regs 7) ((den11 s).regs 0)
def zero (s : X86Memory.State) := finish (put s 0 0) (some (logical32 0))
def divided (s : X86Memory.State) := finish (OriginalDivMemory.result (num s)).core none

theorem num_stack (s : X86Memory.State) :
    (num s).regs 4=s.regs 4-(4#32) ∧
    (num s).memory=store32 s.memory (s.regs 4-(4#32)) 0x2c32e := by
  simp [num,num1,num2,num3,num4,num5,num6,num7,num8,num9,num10,num11,num12,num13,num14,num15,num16,
    multiply,put,write,eax,ebx,edx,X86Routine.pushWord]
theorem div_return (s : X86Memory.State) : (OriginalDivMemory.result (num s)).pc=0x2c32e := by
  rw [(OriginalDivMemory.restored_registers (num s)).2.2.2.2,(num_stack s).1,(num_stack s).2,load_store]
  rfl

theorem divided_execution (s : X86Memory.State) (f : Option Flags)
    (safe : OriginalDivMemory.Safe (num s)) :
    ∃ n≤47, X86Routine.Prefix program [] n ⟨s,f,0x2c301⟩ (divided s) := by
  obtain ⟨n,hn,hp⟩ := OriginalDivMemory.execution_path (num s) none safe
  have hp := hp.transfer program [] contains_div (by simp)
  have last := finish_execution (OriginalDivMemory.result (num s)).core none
  have state : (⟨(OriginalDivMemory.result (num s)).core,none,0x2c32e⟩ : X86Control.State)=OriginalDivMemory.result (num s) := by
    rw [←div_return s]; rfl
  rw [state] at last
  exact ⟨16+n+6,by omega,OriginalGroupBounds.prefix_join (OriginalGroupBounds.prefix_join (num_execution s f) hp) last⟩

theorem zero_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 8 ⟨s,f,0x2c2fd⟩ (zero s) := by
  have path : X86Routine.Prefix listed [] 2 ⟨s,f,0x2c2fd⟩ ⟨put s 0 0,some (logical32 0),0x2c32e⟩ := by
    apply X86Routine.Prefix.step (middle:=⟨put s 0 0,some (logical32 0),0x2c2ff⟩) (by simp) (by rfl) (by simp [X86Routine.execute,logical32])
    apply X86Routine.Prefix.step (middle:=⟨put s 0 0,some (logical32 0),0x2c32e⟩) (by simp) (by rfl) (by rfl)
    exact .nil _
  exact OriginalGroupBounds.prefix_join (path.transfer program [] decoded (by simp)) (finish_execution _ _)

theorem den_zero (s : X86Memory.State) : (denFlags s).zero=((den s).regs 7==(0#32)) := by
  rfl

def body (s : X86Memory.State) := if (den s).regs 7=(0#32) then zero (den s) else divided (den s)
def Safe (s : X86Memory.State) : Prop := (den (prepare s)).regs 7≠(0#32) → OriginalDivMemory.Safe (num (den (prepare s)))
def result (s : X86Memory.State) := body (prepare s)

theorem body_execution (s : X86Memory.State) (f : Option Flags)
    (safe : (den s).regs 7≠(0#32) → OriginalDivMemory.Safe (num (den s))) :
    ∃ n≤60, X86Routine.Prefix program [] n ⟨s,f,0x2c2d9⟩ (body s) := by
  by_cases hz : (den s).regs 7=(0#32)
  · have jump : X86Routine.Prefix listed [] 1 ⟨den s,some (denFlags s),0x2c2fb⟩ ⟨den s,some (denFlags s),0x2c2fd⟩ := by
      apply X86Routine.Prefix.step (middle:=⟨den s,some (denFlags s),0x2c2fd⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,den_zero,hz])
      exact .nil _
    exact ⟨21,by omega,by simpa only [body,if_pos hz] using
        (OriginalGroupBounds.prefix_join (den_execution s f)
        (OriginalGroupBounds.prefix_join (jump.transfer program [] decoded (by simp)) (zero_execution _ _)))⟩
  · have zb : ((den s).regs 7 == 0)=false := beq_eq_false_iff_ne.mpr hz
    have jump : X86Routine.Prefix listed [] 1 ⟨den s,some (denFlags s),0x2c2fb⟩ ⟨den s,some (denFlags s),0x2c301⟩ := by
      apply X86Routine.Prefix.step (middle:=⟨den s,some (denFlags s),0x2c301⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,den_zero,zb,hz])
      exact .nil _
    obtain ⟨n,hn,hp⟩ := divided_execution (den s) (some (denFlags s)) (safe hz)
    exact ⟨12+1+n,by omega,by simpa only [body,if_neg hz,Nat.add_assoc] using
        (OriginalGroupBounds.prefix_join (den_execution s f)
        (OriginalGroupBounds.prefix_join (jump.transfer program [] decoded (by simp)) hp))⟩

/-- The complete original helper, including FixedDiv, under its actual IDIV
success condition. Memory may be unaligned and addresses wrap at 32 bits. -/
theorem execution (s : X86Memory.State) (f : Option Flags) (safe : Safe s) :
    ∃ n≤67, X86Routine.Prefix program [] n ⟨s,f,0x2c2d0⟩ (result s) := by
  obtain ⟨n,hn,hp⟩ := body_execution (prepare s) f safe
  exact ⟨7+n,by omega,OriginalGroupBounds.prefix_join (prepare_execution s f) hp⟩

def saved (s : X86Memory.State) : Memory :=
  store32 (store32 (store32 (store32 (store32 s.memory (s.regs 4-(4#32)) (s.regs 3))
    (s.regs 4-(8#32)) (s.regs 1)) (s.regs 4-(12#32)) (s.regs 6)) (s.regs 4-(16#32)) (s.regs 7)) (s.regs 4-(20#32)) (s.regs 5)
theorem prepare_memory (s : X86Memory.State) : (prepare s).memory=saved s := by
  simp [prepare,prepare1,prepare2,prepare3,prepare4,prepare5,prepare6,prepare7,X86Routine.pushWord,saved,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc]
theorem prepare_frame (s : X86Memory.State) (a : Word)
    (safe : ∀ off∈[(4#32),8,12,16,20], Apart a (s.regs 4-off)) :
    load32 (prepare s).memory a=load32 s.memory a := by
  rw [prepare_memory]; unfold saved
  repeat rw [load_store_apart _ _ _ _ (safe _ (by simp))]

def denominator (v2 v1 : Collision.Divline) : Fixed :=
  (⟨v1.dy.raw >>> 8⟩ : Fixed) * v2.dx - (⟨v1.dx.raw >>> 8⟩ : Fixed) * v2.dy
def numerator (v2 v1 : Collision.Divline) : Fixed :=
  (⟨(v1.x-v2.x).raw >>> 8⟩ : Fixed) * v1.dy + (⟨(v2.y-v1.y).raw >>> 8⟩ : Fixed) * v1.dx

structure Inputs (s : X86Memory.State) (v2 v1 : Collision.Divline) (p q : Word) : Prop where
  pointer2 : s.regs 0=p
  pointer1 : s.regs 2=q
  x2 : load32 s.memory p=v2.x.raw.toBitVec
  y2 : load32 s.memory (p+4)=v2.y.raw.toBitVec
  dx2 : load32 s.memory (p+8)=v2.dx.raw.toBitVec
  dy2 : load32 s.memory (p+12)=v2.dy.raw.toBitVec
  x1 : load32 s.memory q=v1.x.raw.toBitVec
  y1 : load32 s.memory (q+4)=v1.y.raw.toBitVec
  dx1 : load32 s.memory (q+8)=v1.dx.raw.toBitVec
  dy1 : load32 s.memory (q+12)=v1.dy.raw.toBitVec
  safe : ∀ a∈[p,p+4,p+8,p+12,q,q+4,q+8,q+12],
    ∀ off∈[(4#32),8,12,16,20], Apart a (s.regs 4-off)

theorem operands (s : X86Memory.State) (v2 v1 : Collision.Divline) (p q : Word)
    (h : Inputs s v2 v1 p q) :
    (den (prepare s)).regs 7=(denominator v2 v1).raw.toBitVec ∧
    (num (den (prepare s))).regs 0=(numerator v2 v1).raw.toBitVec ∧
    (num (den (prepare s))).regs 2=(denominator v2 v1).raw.toBitVec := by
  have keep (a : Word) (ha : a∈[p,p+4,p+8,p+12,q,q+4,q+8,q+12]) := prepare_frame s a (h.safe a ha)
  have regs : (prepare s).regs 0=p ∧ (prepare s).regs 2=q ∧
      (prepare s).regs 6=p ∧ (prepare s).regs 1=q := by
    simp [prepare,prepare1,prepare2,prepare3,prepare4,prepare5,prepare6,prepare7,X86Routine.pushWord,put,write,h.pointer2,h.pointer1]
  have a0 := (keep p (by simp)).trans h.x2
  have a4 := (keep (p+4) (by simp)).trans h.y2
  have a8 := (keep (p+8) (by simp)).trans h.dx2
  have a12 := (keep (p+12) (by simp)).trans h.dy2
  have b0 := (keep q (by simp)).trans h.x1
  have b4 := (keep (q+4) (by simp)).trans h.y1
  have b8 := (keep (q+8) (by simp)).trans h.dx1
  have b12 := (keep (q+12) (by simp)).trans h.dy1
  change load32 (prepare s).memory (p+(4#32))=v2.y.raw.toBitVec at a4
  change load32 (prepare s).memory (p+(8#32))=v2.dx.raw.toBitVec at a8
  change load32 (prepare s).memory (p+(12#32))=v2.dy.raw.toBitVec at a12
  change load32 (prepare s).memory (q+(4#32))=v1.y.raw.toBitVec at b4
  change load32 (prepare s).memory (q+(8#32))=v1.dx.raw.toBitVec at b8
  change load32 (prepare s).memory (q+(12#32))=v1.dy.raw.toBitVec at b12
  simp [den,den1,den2,den3,den4,den5,den6,den7,den8,den9,den10,den11,den12,num,num1,num2,num3,num4,num5,num6,num7,num8,num9,num10,num11,num12,num13,num14,num15,num16,multiply,put,write,eax,ebx,edx,X86Routine.pushWord,
    ↓reduceIte,BitVec.add_zero,regs.1,regs.2.1,regs.2.2.1,regs.2.2.2,a0,a4,a8,a12,b0,b4,b8,b12]
  simp only [denominator,numerator,mulWord,Fixed.sub,Fixed.add,
    Int32.toBitVec_sub,Int32.toBitVec_add,Int32.ofBitVec_toBitVec]
  exact ⟨rfl,BitVec.add_comm _ _,rfl⟩

theorem finish_value (s : X86Memory.State) (f : Option Flags) : (finish s f).core.regs 0=s.regs 0 := by
  simp [finish,pops,pops1,pops2,pops3,pops4,pops5,put,write]

/-- Successful production arithmetic supplies the actual machine division
precondition; it is not assumed independently by the caller. -/
theorem safe_of_success (s : X86Memory.State) (v2 v1 : Collision.Divline) (p q : Word)
    (h : Inputs s v2 v1 p q) (ok : (Collision.interceptVector v2 v1).isOk=true) : Safe s := by
  intro nz
  have values := operands s v2 v1 p q h
  have nz' : (denominator v2 v1).raw≠0 := by
    intro hz; apply nz; rw [values.1,hz]; rfl
  apply OriginalDivMemory.safe_of_fixed_success
  rw [values.2.1,values.2.2]
  simp only [Int32.ofBitVec_toBitVec]
  change (Fixed.divChecked (numerator v2 v1) (denominator v2 v1)).isOk=true
  change (if (denominator v2 v1).raw==0 then Except.ok (⟨0⟩ : Fixed)
    else Collision.checkedPathDiv (numerator v2 v1) (denominator v2 v1)).isOk=true at ok
  simp only [beq_eq_false_iff_ne.mpr nz',Bool.false_eq_true,if_false] at ok
  cases hd : Fixed.divChecked (numerator v2 v1) (denominator v2 v1) <;>
    simp_all [Collision.checkedPathDiv,Except.isOk,Except.toBool,Except.mapError]

/-- The returned raw fixed-point fraction equals the live engine function,
including the zero-denominator branch, provided that function succeeds. -/
theorem live (s : X86Memory.State) (v2 v1 : Collision.Divline) (p q : Word)
    (h : Inputs s v2 v1 p q) (ok : (Collision.interceptVector v2 v1).isOk=true) :
    (Collision.interceptVector v2 v1).toOption.map (fun v => v.raw.toBitVec)=some ((result s).core.regs 0) := by
  have values := operands s v2 v1 p q h
  unfold result body
  by_cases hz : (denominator v2 v1).raw=0
  · have hz' : (den (prepare s)).regs 7=(0#32) := by rw [values.1,hz]; rfl
    simp only [if_pos hz',zero,finish_value,put,write,↓reduceIte]
    change (if (denominator v2 v1).raw==0 then Except.ok (⟨0⟩ : Fixed)
      else Collision.checkedPathDiv (numerator v2 v1) (denominator v2 v1)).toOption.map _=some 0
    simp [hz,Except.toOption]
  · have hz' : (den (prepare s)).regs 7≠(0#32) := by
      intro e
      apply hz
      rw [values.1] at e
      exact Int32.toBitVec_inj.mp e
    simp only [if_neg hz',divided,finish_value]
    have eq := OriginalDivMemory.result_matches_fixed _ (safe_of_success s v2 v1 p q h ok hz')
    rw [values.2.1,values.2.2] at eq
    simp only [Int32.ofBitVec_toBitVec] at eq
    change (if (denominator v2 v1).raw==0 then Except.ok (⟨0⟩ : Fixed)
      else Collision.checkedPathDiv (numerator v2 v1) (denominator v2 v1)).toOption.map _=_
    simp only [beq_eq_false_iff_ne.mpr hz,Bool.false_eq_true,if_false,Collision.checkedPathDiv]
    cases hd : Fixed.divChecked (numerator v2 v1) (denominator v2 v1) <;> simpa [hd,Except.mapError,Except.toOption] using eq

theorem den_frame (s : X86Memory.State) : (den s).memory=s.memory ∧ (den s).regs 4=s.regs 4 := by
  simp [den,den1,den2,den3,den4,den5,den6,den7,den8,den9,den10,den11,den12,multiply,put,write,eax,ebx,edx]
theorem inner_sp (s : X86Memory.State) : (OriginalDivMemory.result (num s)).core.regs 4=s.regs 4 := by
  rw [(OriginalDivMemory.restored_registers _).2.2.2.1,(num_stack s).1]
  simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
theorem inner_frame (s : X86Memory.State) (a : Word)
    (safe : ∀ off∈[(4#32),8,12,16], Apart a (s.regs 4-off)) :
    load32 (OriginalDivMemory.result (num s)).core.memory a=load32 s.memory a := by
  rw [OriginalDivMemory.result_frame]
  · rw [(num_stack s).2]
    exact load_store_apart _ _ _ _ (safe (4#32) (by simp))
  · intro off ho
    rw [(num_stack s).1]
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
    rcases ho with rfl|rfl|rfl
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe 8 (by simp)
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe 12 (by simp)
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe 16 (by simp)

theorem inner_saved (s : X86Memory.State) (off : Word) (ho : off∈[(0#32),4,8,12,16,20]) :
    load32 (OriginalDivMemory.result (num s)).core.memory (s.regs 4+off)=load32 s.memory (s.regs 4+off) := by
  apply inner_frame
  intro down hd
  have base : Apart off (-down) := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ho hd
    rcases ho with rfl|rfl|rfl|rfl|rfl|rfl <;> rcases hd with rfl|rfl|rfl|rfl <;> unfold Apart <;> decide
  simpa [BitVec.sub_eq_add_neg] using OriginalPathXStep.apart_translate (s.regs 4) off (-down) base

theorem finish_regs (s : X86Memory.State) (f : Option Flags) :
    (finish s f).core.regs 4=s.regs 4+(24#32) ∧
    (finish s f).core.regs 5=load32 s.memory (s.regs 4) ∧
    (finish s f).core.regs 7=load32 s.memory (s.regs 4+(4#32)) ∧
    (finish s f).core.regs 6=load32 s.memory (s.regs 4+(8#32)) ∧
    (finish s f).core.regs 1=load32 s.memory (s.regs 4+(12#32)) ∧
    (finish s f).core.regs 3=load32 s.memory (s.regs 4+(16#32)) ∧
    (finish s f).pc=(load32 s.memory (s.regs 4+(20#32))).toNat := by
  simp [finish,pops,pops1,pops2,pops3,pops4,pops5,put,write,BitVec.add_assoc]

theorem body_regs (s : X86Memory.State) :
    (body s).core.regs 4=s.regs 4+(24#32) ∧
    (body s).core.regs 5=load32 s.memory (s.regs 4) ∧
    (body s).core.regs 7=load32 s.memory (s.regs 4+(4#32)) ∧
    (body s).core.regs 6=load32 s.memory (s.regs 4+(8#32)) ∧
    (body s).core.regs 1=load32 s.memory (s.regs 4+(12#32)) ∧
    (body s).core.regs 3=load32 s.memory (s.regs 4+(16#32)) ∧
    (body s).pc=(load32 s.memory (s.regs 4+(20#32))).toNat := by
  unfold body
  split
  · simpa [zero,put,write,(den_frame s).1,(den_frame s).2] using finish_regs (put (den s) 0 0) (some (logical32 0))
  · have k := finish_regs (OriginalDivMemory.result (num (den s))).core none
    simp only [inner_sp] at k
    have keep (off : Word) (ho : off∈[(0#32),4,8,12,16,20]) := inner_saved (den s) off ho
    have keep0 := keep (0#32) (by simp)
    simp only [BitVec.add_zero] at keep0
    rw [keep0,keep (4#32) (by simp),keep (8#32) (by simp),keep (12#32) (by simp),keep (16#32) (by simp),keep (20#32) (by simp)] at k
    simpa only [divided,(den_frame s).1,(den_frame s).2] using k


theorem saved_0 (s : X86Memory.State) : load32 (saved s) (s.regs 4-(0#32))=load32 s.memory (s.regs 4) := by
  unfold saved
  rw [load_store_apart _ _ _ _ (OriginalLineSide.slots_apart (s.regs 4) (0#32) (20#32) (by unfold Apart; decide))]
  rw [load_store_apart _ _ _ _ (OriginalLineSide.slots_apart (s.regs 4) (0#32) (16#32) (by unfold Apart; decide))]
  rw [load_store_apart _ _ _ _ (OriginalLineSide.slots_apart (s.regs 4) (0#32) (12#32) (by unfold Apart; decide))]
  rw [load_store_apart _ _ _ _ (OriginalLineSide.slots_apart (s.regs 4) (0#32) (8#32) (by unfold Apart; decide))]
  rw [load_store_apart _ _ _ _ (OriginalLineSide.slots_apart (s.regs 4) (0#32) (4#32) (by unfold Apart; decide))]
  simp
theorem saved_4 (s : X86Memory.State) : load32 (saved s) (s.regs 4-(4#32))=s.regs 3 := by
  unfold saved
  rw [load_store_apart _ _ _ _ (OriginalLineSide.slots_apart (s.regs 4) (4#32) (20#32) (by unfold Apart; decide))]
  rw [load_store_apart _ _ _ _ (OriginalLineSide.slots_apart (s.regs 4) (4#32) (16#32) (by unfold Apart; decide))]
  rw [load_store_apart _ _ _ _ (OriginalLineSide.slots_apart (s.regs 4) (4#32) (12#32) (by unfold Apart; decide))]
  rw [load_store_apart _ _ _ _ (OriginalLineSide.slots_apart (s.regs 4) (4#32) (8#32) (by unfold Apart; decide))]
  rw [load_store]
theorem saved_8 (s : X86Memory.State) : load32 (saved s) (s.regs 4-(8#32))=s.regs 1 := by
  unfold saved
  rw [load_store_apart _ _ _ _ (OriginalLineSide.slots_apart (s.regs 4) (8#32) (20#32) (by unfold Apart; decide))]
  rw [load_store_apart _ _ _ _ (OriginalLineSide.slots_apart (s.regs 4) (8#32) (16#32) (by unfold Apart; decide))]
  rw [load_store_apart _ _ _ _ (OriginalLineSide.slots_apart (s.regs 4) (8#32) (12#32) (by unfold Apart; decide))]
  rw [load_store]
theorem saved_12 (s : X86Memory.State) : load32 (saved s) (s.regs 4-(12#32))=s.regs 6 := by
  unfold saved
  rw [load_store_apart _ _ _ _ (OriginalLineSide.slots_apart (s.regs 4) (12#32) (20#32) (by unfold Apart; decide))]
  rw [load_store_apart _ _ _ _ (OriginalLineSide.slots_apart (s.regs 4) (12#32) (16#32) (by unfold Apart; decide))]
  rw [load_store]
theorem saved_16 (s : X86Memory.State) : load32 (saved s) (s.regs 4-(16#32))=s.regs 7 := by
  unfold saved
  rw [load_store_apart _ _ _ _ (OriginalLineSide.slots_apart (s.regs 4) (16#32) (20#32) (by unfold Apart; decide))]
  rw [load_store]
theorem saved_20 (s : X86Memory.State) : load32 (saved s) (s.regs 4-(20#32))=s.regs 5 := by
  unfold saved
  rw [load_store]

theorem returned (s : X86Memory.State) :
    (result s).core.regs 4=s.regs 4+(4#32) ∧
    (result s).core.regs 5=s.regs 5 ∧ (result s).core.regs 7=s.regs 7 ∧
    (result s).core.regs 6=s.regs 6 ∧ (result s).core.regs 1=s.regs 1 ∧
    (result s).core.regs 3=s.regs 3 ∧ (result s).pc=(load32 s.memory (s.regs 4)).toNat := by
  have sp : (prepare s).regs 4=s.regs 4-(20#32) := by
    simp [prepare,prepare1,prepare2,prepare3,prepare4,prepare5,prepare6,prepare7,X86Routine.pushWord,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc]
  have k := body_regs (prepare s)
  rw [sp,prepare_memory] at k
  simp [BitVec.sub_eq_add_neg,BitVec.add_assoc] at k
  have a := saved_20 s
  have b := saved_16 s
  have c := saved_12 s
  have d := saved_8 s
  have e := saved_4 s
  have ret := saved_0 s
  simp [BitVec.sub_eq_add_neg] at a b c d e ret
  rw [a,b,c,d,e,ret] at k
  exact k

theorem finish_memory (s : X86Memory.State) (f : Option Flags) : (finish s f).core.memory=s.memory := rfl

attribute [local irreducible] num den prepare OriginalDivMemory.result

/-- The complete helper writes only its five saves, FixedDiv's call word, and
that callee's three saves. Both return paths preserve every separated word. -/
theorem frame (s : X86Memory.State) (a : Word)
    (safe : ∀ off∈[(4#32),8,12,16,20,24,28,32,36], Apart a (s.regs 4-off)) :
    load32 (result s).core.memory a=load32 s.memory a := by
  have prep := prepare_frame s a (by
    intro off ho
    apply safe off
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ho ⊢
    rcases ho with rfl|rfl|rfl|rfl|rfl <;> simp)
  have sp : (den (prepare s)).regs 4=s.regs 4-(20#32) := by
    rw [(den_frame _).2]
    simp [prepare,prepare1,prepare2,prepare3,prepare4,prepare5,prepare6,prepare7,
      X86Routine.pushWord,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc]
  unfold result body
  split
  · simp only [zero,finish_memory,put]
    rw [(den_frame _).1]; exact prep
  · simp only [divided,finish_memory]
    rw [inner_frame]
    · rw [(den_frame _).1]; exact prep
    · intro off ho
      rw [sp]
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
      rcases ho with rfl|rfl|rfl|rfl
      · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe (24#32) (by simp)
      · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe (28#32) (by simp)
      · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe (32#32) (by simp)
      · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe (36#32) (by simp)
end Doom.Proofs.OriginalInterceptVector
