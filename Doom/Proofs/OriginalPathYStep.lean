import Doom.Proofs.OriginalAbs
import Doom.Proofs.OriginalPathIntercept
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalPathYStep
open Verification X86 X86Memory X86Control BlockSummary
def code : List UInt8 := [0x7e,0x22,0xba,0x0,0x0,0x1,0x0,0xe8,0xbc,0x4e,0x1,0x0,0x29,0xda,0xb9,0x1,0x0,0x0,0x0,0x89,0xd3,0x89,0xc2,0x89,0xe8,0x89,0x4c,0x24,0x1c,0xe8,0x4e,0x7,0xff,0xff,0xeb,0x2b,0x7d,0x19,0xba,0xff,0xff,0xff,0xff,0xe8,0x98,0x4e,0x1,0x0,0x89,0x54,0x24,0x1c,0x89,0xc2,0x89,0xe8,0xe8,0x33,0x7,0xff,0xff,0xeb,0x10,0xbb,0x0,0x0,0x1,0x0,0x31,0xed,0xb8,0x0,0x0,0x0,0x1,0x89,0x6c,0x24,0x1c]
def bytesProgram (bytes : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2ca10≤pc ∧ pc<0x2ca5f then X86Routine.decodeAt bytes (pc-0x2ca10) else none
def localProgram := bytesProgram code
def listed : X86Routine.Program
  | 0x2ca10 => some (.jumpSigned 1 34,2)
  | 0x2ca12 => some (.immediate 2 0x10000,5)
  | 0x2ca17 => some (.call (85692),5)
  | 0x2ca1c => some (.control (.block (.arithmetic (.sub 2 3))),2)
  | 0x2ca1e => some (.immediate 1 0x1,5)
  | 0x2ca23 => some (.control (.block (.legacy (.mov 3 2))),2)
  | 0x2ca25 => some (.control (.block (.legacy (.mov 2 0))),2)
  | 0x2ca27 => some (.control (.block (.legacy (.mov 0 5))),2)
  | 0x2ca29 => some (.control (.block (.store ⟨some 4,none,0,28⟩ 1)),4)
  | 0x2ca2d => some (.call (-63666),5)
  | 0x2ca32 => some (.jump 43,2)
  | 0x2ca34 => some (.jumpSigned 0 25,2)
  | 0x2ca36 => some (.immediate 2 0xffffffff,5)
  | 0x2ca3b => some (.call (85656),5)
  | 0x2ca40 => some (.control (.block (.store ⟨some 4,none,0,28⟩ 2)),4)
  | 0x2ca44 => some (.control (.block (.legacy (.mov 2 0))),2)
  | 0x2ca46 => some (.control (.block (.legacy (.mov 0 5))),2)
  | 0x2ca48 => some (.call (-63693),5)
  | 0x2ca4d => some (.jump 16,2)
  | 0x2ca4f => some (.immediate 3 0x10000,5)
  | 0x2ca54 => some (.xorRegister 5 5,2)
  | 0x2ca56 => some (.immediate 0 0x1000000,5)
  | 0x2ca5b => some (.control (.block (.store ⟨some 4,none,0,28⟩ 5)),4)
  | _ => none
theorem decoded (pc : Nat) (h : listed pc≠none) : localProgram pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def rightCall_1 (s : X86Memory.State) : X86Memory.State := put (s) 2 (0x10000)
def rightCall_m1 (s : X86Memory.State) : Memory := store32 (s.memory) (s.regs 4-4) 0x2ca1c
def rightCall_2 (s : X86Memory.State) : X86Memory.State := {regs:=write (rightCall_1 s).regs 4 (s.regs 4-4),memory:=rightCall_m1 s}
def rightCall (s : X86Memory.State) (f : Option Flags) : X86Control.State := ⟨rightCall_2 s,f,0x418d8⟩
theorem rightCall_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix localProgram [] 2 ⟨s,f,0x2ca12⟩ (rightCall s f) := by
  have path : X86Routine.Prefix listed [] 2 ⟨s,f,0x2ca12⟩ (rightCall s f) := by
    apply X86Routine.Prefix.step (middle := ⟨rightCall_1 s,f,0x2ca17⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,rightCall_2,rightCall_m1,rightCall_1,rightCall])
    apply X86Routine.Prefix.step (middle := ⟨rightCall_2 s,f,0x418d8⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,rightCall_2,rightCall_m1,rightCall_1,rightCall])
    exact .nil _
  exact path.transfer localProgram [] decoded (by simp)

def leftCall_1 (s : X86Memory.State) : X86Memory.State := put (s) 2 (0xffffffff)
def leftCall_m1 (s : X86Memory.State) : Memory := store32 (s.memory) (s.regs 4-4) 0x2ca40
def leftCall_2 (s : X86Memory.State) : X86Memory.State := {regs:=write (leftCall_1 s).regs 4 (s.regs 4-4),memory:=leftCall_m1 s}
def leftCall (s : X86Memory.State) (f : Option Flags) : X86Control.State := ⟨leftCall_2 s,f,0x418d8⟩
theorem leftCall_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix localProgram [] 2 ⟨s,f,0x2ca36⟩ (leftCall s f) := by
  have path : X86Routine.Prefix listed [] 2 ⟨s,f,0x2ca36⟩ (leftCall s f) := by
    apply X86Routine.Prefix.step (middle := ⟨leftCall_1 s,f,0x2ca3b⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,leftCall_2,leftCall_m1,leftCall_1,leftCall])
    apply X86Routine.Prefix.step (middle := ⟨leftCall_2 s,f,0x418d8⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,leftCall_2,leftCall_m1,leftCall_1,leftCall])
    exact .nil _
  exact path.transfer localProgram [] decoded (by simp)

def rightDivide_1 (s : X86Memory.State) : X86Memory.State := put (s) 2 ((s.regs 2)-(s.regs 3))
def rightDivide_2 (s : X86Memory.State) : X86Memory.State := put (rightDivide_1 s) 1 (0x1)
def rightDivide_3 (s : X86Memory.State) : X86Memory.State := put (rightDivide_2 s) 3 ((s.regs 2)-(s.regs 3))
def rightDivide_4 (s : X86Memory.State) : X86Memory.State := put (rightDivide_3 s) 2 (s.regs 0)
def rightDivide_5 (s : X86Memory.State) : X86Memory.State := put (rightDivide_4 s) 0 (s.regs 5)
def rightDivide_m5 (s : X86Memory.State) : Memory := store32 (s.memory) ((s.regs 4)+28) (0x1)
def rightDivide_6 (s : X86Memory.State) : X86Memory.State := {regs:=(rightDivide_5 s).regs,memory:=rightDivide_m5 s}
def rightDivide_m6 (s : X86Memory.State) : Memory := store32 (rightDivide_m5 s) (s.regs 4-4) 0x2ca32
def rightDivide_7 (s : X86Memory.State) : X86Memory.State := {regs:=write (rightDivide_6 s).regs 4 (s.regs 4-4),memory:=rightDivide_m6 s}
def rightDivide (s : X86Memory.State) (f : Option Flags) : X86Control.State := ⟨rightDivide_7 s,none,0x1d180⟩
theorem rightDivide_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix localProgram [] 7 ⟨s,f,0x2ca1c⟩ (rightDivide s f) := by
  have path : X86Routine.Prefix listed [] 7 ⟨s,f,0x2ca1c⟩ (rightDivide s f) := by
    apply X86Routine.Prefix.step (middle := ⟨rightDivide_1 s,none,0x2ca1e⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,rightDivide_7,rightDivide_m6,rightDivide_6,rightDivide_m5,rightDivide_5,rightDivide_4,rightDivide_3,rightDivide_2,rightDivide_1,rightDivide])
    apply X86Routine.Prefix.step (middle := ⟨rightDivide_2 s,none,0x2ca23⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,rightDivide_7,rightDivide_m6,rightDivide_6,rightDivide_m5,rightDivide_5,rightDivide_4,rightDivide_3,rightDivide_2,rightDivide_1,rightDivide])
    apply X86Routine.Prefix.step (middle := ⟨rightDivide_3 s,none,0x2ca25⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,rightDivide_7,rightDivide_m6,rightDivide_6,rightDivide_m5,rightDivide_5,rightDivide_4,rightDivide_3,rightDivide_2,rightDivide_1,rightDivide])
    apply X86Routine.Prefix.step (middle := ⟨rightDivide_4 s,none,0x2ca27⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,rightDivide_7,rightDivide_m6,rightDivide_6,rightDivide_m5,rightDivide_5,rightDivide_4,rightDivide_3,rightDivide_2,rightDivide_1,rightDivide])
    apply X86Routine.Prefix.step (middle := ⟨rightDivide_5 s,none,0x2ca29⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,rightDivide_7,rightDivide_m6,rightDivide_6,rightDivide_m5,rightDivide_5,rightDivide_4,rightDivide_3,rightDivide_2,rightDivide_1,rightDivide])
    apply X86Routine.Prefix.step (middle := ⟨rightDivide_6 s,none,0x2ca2d⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,rightDivide_7,rightDivide_m6,rightDivide_6,rightDivide_m5,rightDivide_5,rightDivide_4,rightDivide_3,rightDivide_2,rightDivide_1,rightDivide])
    apply X86Routine.Prefix.step (middle := ⟨rightDivide_7 s,none,0x1d180⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,rightDivide_7,rightDivide_m6,rightDivide_6,rightDivide_m5,rightDivide_5,rightDivide_4,rightDivide_3,rightDivide_2,rightDivide_1,rightDivide])
    exact .nil _
  exact path.transfer localProgram [] decoded (by simp)

def leftDivide_m0 (s : X86Memory.State) : Memory := store32 (s.memory) ((s.regs 4)+28) (s.regs 2)
def leftDivide_1 (s : X86Memory.State) : X86Memory.State := {regs:=(s).regs,memory:=leftDivide_m0 s}
def leftDivide_2 (s : X86Memory.State) : X86Memory.State := put (leftDivide_1 s) 2 (s.regs 0)
def leftDivide_3 (s : X86Memory.State) : X86Memory.State := put (leftDivide_2 s) 0 (s.regs 5)
def leftDivide_m3 (s : X86Memory.State) : Memory := store32 (leftDivide_m0 s) (s.regs 4-4) 0x2ca4d
def leftDivide_4 (s : X86Memory.State) : X86Memory.State := {regs:=write (leftDivide_3 s).regs 4 (s.regs 4-4),memory:=leftDivide_m3 s}
def leftDivide (s : X86Memory.State) (f : Option Flags) : X86Control.State := ⟨leftDivide_4 s,f,0x1d180⟩
theorem leftDivide_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix localProgram [] 4 ⟨s,f,0x2ca40⟩ (leftDivide s f) := by
  have path : X86Routine.Prefix listed [] 4 ⟨s,f,0x2ca40⟩ (leftDivide s f) := by
    apply X86Routine.Prefix.step (middle := ⟨leftDivide_1 s,f,0x2ca44⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,leftDivide_4,leftDivide_m3,leftDivide_3,leftDivide_2,leftDivide_1,leftDivide_m0,leftDivide])
    apply X86Routine.Prefix.step (middle := ⟨leftDivide_2 s,f,0x2ca46⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,leftDivide_4,leftDivide_m3,leftDivide_3,leftDivide_2,leftDivide_1,leftDivide_m0,leftDivide])
    apply X86Routine.Prefix.step (middle := ⟨leftDivide_3 s,f,0x2ca48⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,leftDivide_4,leftDivide_m3,leftDivide_3,leftDivide_2,leftDivide_1,leftDivide_m0,leftDivide])
    apply X86Routine.Prefix.step (middle := ⟨leftDivide_4 s,f,0x1d180⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,leftDivide_4,leftDivide_m3,leftDivide_3,leftDivide_2,leftDivide_1,leftDivide_m0,leftDivide])
    exact .nil _
  exact path.transfer localProgram [] decoded (by simp)

def same_1 (s : X86Memory.State) : X86Memory.State := put (s) 3 (0x10000)
def same_2 (s : X86Memory.State) : X86Memory.State := put (same_1 s) 5 (0)
def same_3 (s : X86Memory.State) : X86Memory.State := put (same_2 s) 0 (0x1000000)
def same_m3 (s : X86Memory.State) : Memory := store32 (s.memory) ((s.regs 4)+28) (0)
def same_4 (s : X86Memory.State) : X86Memory.State := {regs:=(same_3 s).regs,memory:=same_m3 s}
def same (s : X86Memory.State) (f : Option Flags) : X86Control.State := ⟨same_4 s,some {(logical32 0) with carry:=some false},0x2ca5f⟩
theorem same_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix localProgram [] 4 ⟨s,f,0x2ca4f⟩ (same s f) := by
  have path : X86Routine.Prefix listed [] 4 ⟨s,f,0x2ca4f⟩ (same s f) := by
    apply X86Routine.Prefix.step (middle := ⟨same_1 s,f,0x2ca54⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,same_4,same_m3,same_3,same_2,same_1,same])
    apply X86Routine.Prefix.step (middle := ⟨same_2 s,some {(logical32 0) with carry:=some false},0x2ca56⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,same_4,same_m3,same_3,same_2,same_1,same])
    apply X86Routine.Prefix.step (middle := ⟨same_3 s,some {(logical32 0) with carry:=some false},0x2ca5b⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,same_4,same_m3,same_3,same_2,same_1,same])
    apply X86Routine.Prefix.step (middle := ⟨same_4 s,some {(logical32 0) with carry:=some false},0x2ca5f⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,same_4,same_m3,same_3,same_2,same_1,same])
    exact .nil _
  exact path.transfer localProgram [] decoded (by simp)

def rightTail_1 (s : X86Memory.State) : X86Memory.State := s
def rightTail (s : X86Memory.State) (f : Option Flags) : X86Control.State := ⟨rightTail_1 s,f,0x2ca5f⟩
theorem rightTail_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix localProgram [] 1 ⟨s,f,0x2ca32⟩ (rightTail s f) := by
  have path : X86Routine.Prefix listed [] 1 ⟨s,f,0x2ca32⟩ (rightTail s f) := by
    apply X86Routine.Prefix.step (middle := ⟨rightTail_1 s,f,0x2ca5f⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,rightTail_1,rightTail])
    exact .nil _
  exact path.transfer localProgram [] decoded (by simp)

def leftTail_1 (s : X86Memory.State) : X86Memory.State := s
def leftTail (s : X86Memory.State) (f : Option Flags) : X86Control.State := ⟨leftTail_1 s,f,0x2ca5f⟩
theorem leftTail_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix localProgram [] 1 ⟨s,f,0x2ca4d⟩ (leftTail s f) := by
  have path : X86Routine.Prefix listed [] 1 ⟨s,f,0x2ca4d⟩ (leftTail s f) := by
    apply X86Routine.Prefix.step (middle := ⟨leftTail_1 s,f,0x2ca5f⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,leftTail_1,leftTail])
    exact .nil _
  exact path.transfer localProgram [] decoded (by simp)


def program (pc : Nat) : Option (X86Routine.Op × Nat) :=
  if 0x2ca10≤pc ∧ pc<0x2ca5f then localProgram pc
  else if 0x418d8≤pc ∧ pc<0x418df then OriginalAbs.program pc
  else OriginalDivMemory.program pc

theorem contains_local (pc : Nat) (h : localProgram pc≠none) : program pc=localProgram pc := by
  by_cases a : 0x2ca10≤pc ∧ pc<0x2ca5f
  · simp [program,a]
  · simp [localProgram,bytesProgram,a] at h

theorem contains_abs (pc : Nat) (h : OriginalAbs.program pc≠none) : program pc=OriginalAbs.program pc := by
  have a : 0x418d8≤pc ∧ pc<0x418df := by
    by_cases a : 0x418d8≤pc ∧ pc<0x418df
    · exact a
    · simp [OriginalAbs.program,OriginalAbs.bytesProgram,a] at h
  simp [program,a,show ¬(0x2ca10≤pc ∧ pc<0x2ca5f) by omega]

theorem contains_div (pc : Nat) (h : OriginalDivMemory.program pc≠none) : program pc=OriginalDivMemory.program pc := by
  have a : 0x1d180≤pc ∧ pc<0x1d1c1 := by
    by_cases a : 0x1d180≤pc ∧ pc<0x1d1c1
    · exact a
    · simp [OriginalDivMemory.program,OriginalDivMemory.bytesProgram,a] at h
  simp [program,show ¬(0x2ca10≤pc ∧ pc<0x2ca5f) by omega,show ¬(0x418d8≤pc ∧ pc<0x418df) by omega]

def Forward (s : X86Memory.State) : Prop := (s.regs 1).toInt<(s.regs 2).toInt
def Backward (s : X86Memory.State) : Prop := (s.regs 2).toInt<(s.regs 1).toInt
instance (s : X86Memory.State) : Decidable (Forward s) := inferInstanceAs (Decidable (_<_))
instance (s : X86Memory.State) : Decidable (Backward s) := inferInstanceAs (Decidable (_<_))
def Still (s : X86Memory.State) : Prop := ¬Forward s ∧ ¬Backward s
instance (s : X86Memory.State) : Decidable (Still s) := inferInstanceAs (Decidable (_∧_))
def comparison (s : X86Memory.State) := some (compare32 (s.regs 2) (s.regs 1))
def selection (s : X86Memory.State) : X86Control.State :=
  ⟨s,comparison s,if Forward s then 0x2ca12 else if Backward s then 0x2ca36 else 0x2ca4f⟩

theorem selection_execution (s : X86Memory.State) :
    ∃ n, n≤2 ∧ X86Routine.Prefix program [] n ⟨s,comparison s,0x2ca10⟩ (selection s) := by
  have branch : ∃ n, n≤2 ∧ X86Routine.Prefix listed [] n ⟨s,comparison s,0x2ca10⟩ (selection s) := by
    by_cases hf : Forward s
    · refine ⟨1,by omega,?_⟩
      have less : ¬(s.regs 2).toInt≤(s.regs 1).toInt := by unfold Forward at hf; omega
      apply X86Routine.Prefix.step (middle := selection s) (by simp) (by rfl) (by
        simp [comparison,selection,X86Routine.execute,cmp32_signed_le,less,hf])
      exact .nil _
    · by_cases hb : Backward s
      · refine ⟨2,by omega,?_⟩
        have le : (s.regs 2).toInt≤(s.regs 1).toInt := by unfold Backward at hb; omega
        have notge : ¬(s.regs 1).toInt≤(s.regs 2).toInt := by unfold Backward at hb; omega
        apply X86Routine.Prefix.step (middle := ⟨s,comparison s,0x2ca34⟩) (by simp) (by rfl) (by
          simp [comparison,X86Routine.execute,cmp32_signed_le,le])
        apply X86Routine.Prefix.step (middle := selection s) (by simp) (by rfl) (by
          simp [comparison,selection,X86Routine.execute,PlayerHeight.cmp_ge_prop,notge,hf,hb])
        exact .nil _
      · refine ⟨2,by omega,?_⟩
        have le : (s.regs 2).toInt≤(s.regs 1).toInt := by unfold Forward at hf; omega
        have ge : (s.regs 1).toInt≤(s.regs 2).toInt := by unfold Backward at hb; omega
        apply X86Routine.Prefix.step (middle := ⟨s,comparison s,0x2ca34⟩) (by simp) (by rfl) (by
          simp [comparison,X86Routine.execute,cmp32_signed_le,le])
        apply X86Routine.Prefix.step (middle := selection s) (by simp) (by rfl) (by
          simp [comparison,selection,X86Routine.execute,PlayerHeight.cmp_ge_prop,ge,hf,hb])
        exact .nil _
  obtain ⟨n,hn,path⟩ := branch
  exact ⟨n,hn,(path.transfer localProgram [] decoded (by simp)).transfer program [] contains_local (by simp)⟩

def absCall (right : Bool) (s : X86Memory.State) (f : Option Flags) := if right then rightCall s f else leftCall s f
def divideCall (right : Bool) (s : X86Memory.State) (f : Option Flags) := if right then rightDivide s f else leftDivide s f
def tail (right : Bool) (s : X86Memory.State) (f : Option Flags) := if right then rightTail s f else leftTail s f
def divisionInput (right : Bool) (s : X86Memory.State) (f : Option Flags) :=
  let a := OriginalAbs.result (absCall right s f).core
  divideCall right a.core a.flags
def movingResult (right : Bool) (s : X86Memory.State) (f : Option Flags) :=
  let d := OriginalDivMemory.result (divisionInput right s f).core
  tail right d.core d.flags



theorem abs_return (right : Bool) (s : X86Memory.State) (f : Option Flags) :
    (OriginalAbs.result (absCall right s f).core).pc=(if right then 0x2ca1c else 0x2ca40) := by
  cases right <;> simp [absCall,rightCall,rightCall_2,rightCall_m1,rightCall_1,leftCall,leftCall_2,leftCall_m1,leftCall_1,OriginalAbs.result,put,write,load_store]

theorem divide_return (right : Bool) (s : X86Memory.State) (f : Option Flags) :
    (OriginalDivMemory.result (divideCall right s f).core).pc=(if right then 0x2ca32 else 0x2ca4d) := by
  rw [(OriginalDivMemory.restored_registers _).2.2.2.2]
  cases right <;> simp [divideCall,rightDivide,rightDivide_7,rightDivide_m6,rightDivide_6,rightDivide_m5,rightDivide_5,rightDivide_4,rightDivide_3,rightDivide_2,rightDivide_1,leftDivide,leftDivide_4,leftDivide_m3,leftDivide_3,leftDivide_2,leftDivide_1,leftDivide_m0,put,write,load_store]

theorem abs_call_execution (right : Bool) (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 2 ⟨s,f,if right then 0x2ca12 else 0x2ca36⟩ (absCall right s f) := by
  cases right
  · exact (leftCall_execution s f).transfer program [] contains_local (by simp)
  · exact (rightCall_execution s f).transfer program [] contains_local (by simp)

theorem divide_call_execution (right : Bool) (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] (if right then 7 else 4) ⟨s,f,if right then 0x2ca1c else 0x2ca40⟩ (divideCall right s f) := by
  cases right
  · exact (leftDivide_execution s f).transfer program [] contains_local (by simp)
  · exact (rightDivide_execution s f).transfer program [] contains_local (by simp)

theorem tail_execution (right : Bool) (s : X86Memory.State) (f : Option Flags) :
    ∃ n, n≤1 ∧ X86Routine.Prefix program [] n ⟨s,f,if right then 0x2ca32 else 0x2ca4d⟩ (tail right s f) := by
  cases right
  · exact ⟨1,by omega,(leftTail_execution s f).transfer program [] contains_local (by simp)⟩
  · exact ⟨1,by omega,(rightTail_execution s f).transfer program [] contains_local (by simp)⟩

theorem at_pc (s : X86Control.State) (pc : Nat) (h : s.pc=pc) :
    (⟨s.core,s.flags,pc⟩ : X86Control.State)=s := by rw [←h]

theorem moving_execution (right : Bool) (s : X86Memory.State) (f : Option Flags)
    (safe : OriginalDivMemory.Safe (divisionInput right s f).core) :
    ∃ n, n≤39 ∧ X86Routine.Prefix program [] n
      ⟨s,f,if right then 0x2ca12 else 0x2ca36⟩ (movingResult right s f) := by
  have a := abs_call_execution right s f
  obtain ⟨nb,hb,b⟩ := OriginalAbs.execution (absCall right s f).core (absCall right s f).flags
  have b := b.transfer program [] contains_abs (by simp)
  have apc : (absCall right s f).pc=0x418d8 := by cases right <;> rfl
  rw [at_pc _ _ apc] at b
  have c := divide_call_execution right (OriginalAbs.result (absCall right s f).core).core
    (OriginalAbs.result (absCall right s f).core).flags
  rw [at_pc _ _ (abs_return right s f)] at c
  obtain ⟨nd,hd,d⟩ := OriginalDivMemory.execution_path (divisionInput right s f).core
    (divisionInput right s f).flags safe
  have d := d.transfer program [] contains_div (by simp)
  have cpc : (divisionInput right s f).pc=0x1d180 := by cases right <;> rfl
  rw [at_pc _ _ cpc] at d
  obtain ⟨ne,he,e⟩ := tail_execution right (OriginalDivMemory.result (divisionInput right s f).core).core
    (OriginalDivMemory.result (divisionInput right s f).core).flags
  have dpc : (OriginalDivMemory.result (divisionInput right s f).core).pc=(if right then 0x2ca32 else 0x2ca4d) :=
    divide_return right (OriginalAbs.result (absCall right s f).core).core (OriginalAbs.result (absCall right s f).core).flags
  rw [at_pc _ _ dpc] at e
  exact ⟨2+nb+(if right then 7 else 4)+nd+ne,by cases right <;> simp_all <;> omega,OriginalGroupBounds.prefix_join
    (OriginalGroupBounds.prefix_join (OriginalGroupBounds.prefix_join (OriginalGroupBounds.prefix_join a b) c) d) e⟩

def Safe (s : X86Memory.State) : Prop := ¬Still s →
  OriginalDivMemory.Safe (divisionInput (decide (Forward s)) (selection s).core (selection s).flags).core

def result (s : X86Memory.State) : X86Control.State :=
  if Still s then same (selection s).core (selection s).flags
  else movingResult (decide (Forward s)) (selection s).core (selection s).flags

/-- Three direction branches, including real absolute-value and FixedDiv calls,
stack writes, returns and portion adjustment. Faulting division is excluded. -/
theorem execution (s : X86Memory.State) (safe : Safe s) :
    ∃ n, n≤41 ∧ X86Routine.Prefix program [] n ⟨s,comparison s,0x2ca10⟩ (result s) := by
  obtain ⟨n,hn,a⟩ := selection_execution s
  by_cases still : Still s
  · have b := (same_execution (selection s).core (selection s).flags).transfer program [] contains_local (by simp)
    have pc : (selection s).pc=0x2ca4f := by simp [selection,still.1,still.2]
    rw [at_pc _ _ pc] at b
    exact ⟨n+4,by omega,by simpa only [result,if_pos still] using OriginalGroupBounds.prefix_join a b⟩
  · obtain ⟨m,hm,b⟩ := moving_execution (decide (Forward s)) (selection s).core (selection s).flags (safe still)
    have pc : (selection s).pc=(if decide (Forward s) then 0x2ca12 else 0x2ca36) := by
      by_cases forward : Forward s
      · simp [selection,forward]
      · have back : Backward s := by
          by_cases hb : Backward s
          · exact hb
          · exact False.elim (still ⟨forward,hb⟩)
        simp [selection,forward,back]
    rw [at_pc _ _ pc] at b
    exact ⟨n+m,by omega,by simpa only [result,if_neg still] using OriginalGroupBounds.prefix_join a b⟩

theorem result_pc (s : X86Memory.State) : (result s).pc=0x2ca5f := by
  unfold result movingResult tail
  split
  · rfl
  · split <;> rfl




theorem input_observe (right : Bool) (s : X86Memory.State) (f : Option Flags) :
    (divisionInput right s f).core.regs 0=s.regs 5 ∧
    (divisionInput right s f).core.regs 2=OriginalAbs.value (s.regs 0) ∧
    (divisionInput right s f).core.regs 3=(if right then 65536-s.regs 3 else s.regs 3) ∧
    (divisionInput right s f).core.regs 4=s.regs 4-4 ∧
    (divisionInput right s f).core.regs 6=s.regs 6 ∧
    (divisionInput right s f).core.memory=
      store32 (store32 (store32 s.memory (s.regs 4-4) (if right then 0x2ca1c else 0x2ca40))
        (s.regs 4+28) (if right then 1 else 0xffffffff)) (s.regs 4-4) (if right then 0x2ca32 else 0x2ca4d) := by
  cases right <;> by_cases h : (s.regs 0).toInt<0 <;>
    simp [divisionInput,absCall,divideCall,OriginalAbs.result,OriginalAbs.value,rightCall,rightCall_2,rightCall_m1,rightCall_1,leftCall,leftCall_2,leftCall_m1,leftCall_1,rightDivide,rightDivide_7,rightDivide_m6,rightDivide_6,rightDivide_m5,rightDivide_5,rightDivide_4,rightDivide_3,rightDivide_2,rightDivide_1,leftDivide,leftDivide_4,leftDivide_m3,leftDivide_3,leftDivide_2,leftDivide_1,leftDivide_m0,
      put,write,BitVec.sub_add_cancel,h]

@[local simp] theorem slot_28_4294967292 (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(4294967292#32)) v) (sp+(28#32))=load32 m (sp+(28#32)) := by
  exact load_store_apart _ _ _ _ (OriginalPathXStep.apart_translate sp _ _ (by unfold Apart; decide))
@[local simp] theorem slot_28_4294967288 (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(4294967288#32)) v) (sp+(28#32))=load32 m (sp+(28#32)) := by
  exact load_store_apart _ _ _ _ (OriginalPathXStep.apart_translate sp _ _ (by unfold Apart; decide))
@[local simp] theorem slot_28_4294967284 (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(4294967284#32)) v) (sp+(28#32))=load32 m (sp+(28#32)) := by
  exact load_store_apart _ _ _ _ (OriginalPathXStep.apart_translate sp _ _ (by unfold Apart; decide))
@[local simp] theorem slot_28_4294967280 (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(4294967280#32)) v) (sp+(28#32))=load32 m (sp+(28#32)) := by
  exact load_store_apart _ _ _ _ (OriginalPathXStep.apart_translate sp _ _ (by unfold Apart; decide))
theorem moving_observe (right : Bool) (s : X86Memory.State) (f : Option Flags) :
    (movingResult right s f).core.regs 0=OriginalDivMemory.answer (s.regs 5) (OriginalAbs.value (s.regs 0)) ∧
    (movingResult right s f).core.regs 3=(if right then 65536-s.regs 3 else s.regs 3) ∧
    load32 (movingResult right s f).core.memory (s.regs 4+28)=(if right then 1 else 0xffffffff) ∧
    (movingResult right s f).core.regs 4=s.regs 4 ∧
    (movingResult right s f).core.regs 6=s.regs 6 := by
  have input := input_observe right s f
  have rr := OriginalDivMemory.restored_registers (divisionInput right s f).core
  have rv := OriginalDivMemory.result_value (divisionInput right s f).core
  have mem : (OriginalDivMemory.result (divisionInput right s f).core).core.memory=
      (OriginalDivMemory.saved (divisionInput right s f).core).memory := by
    change (OriginalDivMemory.body (divisionInput right s f).core).core.memory=_
    exact OriginalDivMemory.body_memory _
  have direction : load32 (OriginalDivMemory.result (divisionInput right s f).core).core.memory (s.regs 4+28)=
      (if right then 1 else 0xffffffff) := by
    rw [mem]
    simp [OriginalDivMemory.saved_memory,input.2.2.2.1,input.2.2.2.2.2,BitVec.sub_eq_add_neg,
      BitVec.add_assoc,load_store]
  cases right <;> simp only [movingResult,tail,Bool.false_eq_true,↓reduceIte,rightTail,rightTail_1,leftTail,leftTail_1]
  all_goals simp only [rv,rr.1,rr.2.2.1,rr.2.2.2.1,input.1,input.2.1,input.2.2.1,input.2.2.2.1,
    input.2.2.2.2.1,BitVec.sub_add_cancel,Bool.false_eq_true,↓reduceIte,direction,and_self]

theorem division_success (right : Bool) (s : X86Memory.State) (f : Option Flags)
    (numerator denominator quotient : Fixed)
    (hn : s.regs 5=numerator.raw.toBitVec)
    (hd : OriginalAbs.value (s.regs 0)=denominator.raw.toBitVec)
    (ok : Collision.checkedPathDiv numerator denominator=.ok quotient) :
    OriginalDivMemory.Safe (divisionInput right s f).core ∧
    OriginalDivMemory.answer (s.regs 5) (OriginalAbs.value (s.regs 0))=quotient.raw.toBitVec := by
  have input := input_observe right s f
  have num : (⟨Int32.ofBitVec ((divisionInput right s f).core.regs 0)⟩ : Fixed)=numerator := by
    rw [input.1,hn]; cases numerator; rfl
  have den : (⟨Int32.ofBitVec ((divisionInput right s f).core.regs 2)⟩ : Fixed)=denominator := by
    rw [input.2.1,hd]; cases denominator; rfl
  have fixed : Fixed.divChecked numerator denominator=.ok quotient := by
    unfold Collision.checkedPathDiv at ok
    cases he : Fixed.divChecked numerator denominator <;> simp_all [Except.mapError]
  have safe := OriginalDivMemory.safe_of_fixed_success (divisionInput right s f).core (by rw [num,den,fixed]; rfl)
  have value := OriginalDivMemory.result_matches_fixed (divisionInput right s f).core safe
  rw [num,den,fixed] at value
  simp only [Except.toOption,Option.map_some,Option.some.injEq] at value
  rw [OriginalDivMemory.result_value,input.1,input.2.1] at value
  exact ⟨safe,value.symm⟩

structure Inputs (s : X86Memory.State) (p : Collision.PathStart) : Prop where
  deltaX : s.regs 5=(p.x2-p.x1).raw.toBitVec
  deltaY : s.regs 0=(p.y2-p.y1).raw.toBitVec
  startBlock : s.regs 1=p.startBlockY.toBitVec
  endBlock : s.regs 2=p.endBlockY.toBitVec
  fraction : s.regs 3=p.yFraction.raw.toBitVec

def observe (s : X86Memory.State) (t : X86Control.State) : Word × Word × Word :=
  (load32 t.core.memory (s.regs 4+28),t.core.regs 3,t.core.regs 0)
abbrev liveObserve := OriginalPathXStep.liveObserve

theorem forward_iff (s : X86Memory.State) (p : Collision.PathStart) (h : Inputs s p) :
    Forward s ↔ p.startBlockY<p.endBlockY := by
  simp only [Forward,h.startBlock,h.endBlock,Int32.lt_iff_toInt_lt]
  rfl

theorem still_iff (s : X86Memory.State) (p : Collision.PathStart) (h : Inputs s p) :
    Still s ↔ p.endBlockY=p.startBlockY := by
  simp only [Still,Forward,Backward,h.startBlock,h.endBlock]
  change (¬p.startBlockY.toInt<p.endBlockY.toInt ∧ ¬p.endBlockY.toInt<p.startBlockY.toInt) ↔ _
  rw [←Int32.toInt_inj]
  omega

/-- Successful production arithmetic supplies the IDIV safety condition. -/
theorem live (s : X86Memory.State) (p : Collision.PathStart) (out : Int32 × Fixed × Fixed)
    (h : Inputs s p) (ok : p.yStep=.ok out) :
    Safe s ∧ observe s (result s)=liveObserve out := by
  by_cases still : p.endBlockY=p.startBlockY
  · have st : Still s := (still_iff s p h).mpr still
    have output : out=(0,Fixed.ofInt 1,Fixed.ofInt 256) := by
      simpa [Collision.PathStart.yStep,bind,pure,Except.bind,Except.pure,Functor.map,Except.map,still] using ok.symm
    refine ⟨fun moving => False.elim (moving st),?_⟩
    rw [output]
    simp [observe,result,st,same,same_4,same_m3,same_3,same_2,same_1,selection,
      put,write,load_store,liveObserve,OriginalPathXStep.liveObserve,Fixed.ofInt]
  · have st : ¬Still s := fun hs => still ((still_iff s p h).mp hs)
    cases ha : Collision.checkedPathAbs (p.y2-p.y1) with
    | error e => simp [Collision.PathStart.yStep,bind,pure,Except.bind,Except.pure,Functor.map,Except.map,still,ha] at ok
    | ok denominator =>
      cases hd : Collision.checkedPathDiv (p.x2-p.x1) denominator with
      | error e => simp [Collision.PathStart.yStep,bind,pure,Except.bind,Except.pure,Functor.map,Except.map,still,ha,hd] at ok
      | ok quotient =>
        have abs : OriginalAbs.value (s.regs 0)=denominator.raw.toBitVec := by
          rw [h.deltaY]; exact OriginalAbs.checked _ _ ha
        have div := division_success (decide (Forward s)) s (comparison s)
          (p.x2-p.x1) denominator quotient h.deltaX abs hd
        refine ⟨fun _ => div.1,?_⟩
        have output : out=(if p.endBlockY>p.startBlockY then 1 else -1,
            if p.endBlockY>p.startBlockY then Fixed.ofInt 1-p.yFraction else p.yFraction,quotient) := by
          simpa [Collision.PathStart.yStep,bind,pure,Except.bind,Except.pure,Functor.map,Except.map,still,ha,hd] using ok.symm
        have obs := moving_observe (decide (Forward s)) s (comparison s)
        rw [output]
        simp only [observe,result,if_neg st,liveObserve,OriginalPathXStep.liveObserve,selection]
        rw [obs.2.2.1,obs.2.1,obs.1,div.2,h.fraction]
        by_cases forward : Forward s
        · have fwd := (forward_iff s p h).mp forward
          simp only [forward,decide_true,↓reduceIte,fwd]
          rfl
        · have fwd : ¬p.startBlockY<p.endBlockY := fun hf => forward ((forward_iff s p h).mpr hf)
          simp only [forward,decide_false,↓reduceIte,fwd]
          rfl

/-- Reuses the preceding block's proved outputs, including the flag-producing comparison. -/
theorem inputs_from_intercept (s : X86Memory.State) (t : X86Control.State)
    (p : Collision.PathStart) (portion stride : Fixed)
    (h : OriginalPathIntercept.Ready s t p portion stride) :
    Inputs t.core p ∧ t.flags=comparison t.core ∧ t.pc=0x2ca10 := by
  refine ⟨⟨h.deltaX,h.deltaY,h.startBlockY,h.endBlockY,h.fraction⟩,?_,h.pc⟩
  rw [comparison,h.startBlockY,h.endBlockY]
  exact h.comparison


theorem preserved (s : X86Memory.State) :
    (result s).core.regs 4=s.regs 4 ∧ (result s).core.regs 6=s.regs 6 := by
  unfold result
  split
  · simp [same,same_4,same_m3,same_3,same_2,same_1,selection,put,write]
  · exact (moving_observe _ _ _).2.2.2

def writes (s : X86Memory.State) : List Word :=
  [s.regs 4+28,s.regs 4-4,s.regs 4-8,s.regs 4-12,s.regs 4-16]

theorem moving_frame (right : Bool) (s : X86Memory.State) (f : Option Flags) (a : Word)
    (safe : ∀ b, b∈writes s → Apart a b) :
    load32 (movingResult right s f).core.memory a=load32 s.memory a := by
  have tailMem : ∀ (s : X86Memory.State) (f : Option Flags), (tail right s f).core.memory=s.memory := by
    intro s f; cases right <;> rfl
  unfold movingResult
  rw [tailMem,OriginalDivMemory.result_frame]
  · rw [(input_observe right s f).2.2.2.2.2]
    repeat rw [load_store_apart _ _ _ _ (safe _ (by simp [writes]))]
  · intro off h
    rw [(input_observe right s f).2.2.2.1]
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl <;> simp only [BitVec.sub_sub]
    all_goals exact safe _ (by simp [writes])

theorem frame (s : X86Memory.State) (a : Word)
    (safe : ∀ b, b∈writes s → Apart a b) :
    load32 (result s).core.memory a=load32 s.memory a := by
  unfold result
  split
  · simp only [same,same_4,same_m3,same_3,same_2,same_1,selection,put,write,ite_false]
    exact load_store_apart _ _ _ _ (safe _ (by simp [writes]))
  · exact moving_frame _ _ _ a safe

theorem local_preserved (s : X86Memory.State) (off : Word) (h : off∈[12,16,20,24,32,40,44]) :
    load32 (result s).core.memory (s.regs 4+off)=load32 s.memory (s.regs 4+off) := by
  apply frame
  intro b hb
  simp only [writes,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl
  · have finite : ∀ i : Word, i∈[12,16,20,24,32,40,44] → Apart i (28#32) := by
      intro i hi
      simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> unfold Apart <;> decide
    simpa [BitVec.sub_eq_add_neg,BitVec.add_zero] using
      OriginalPathXStep.apart_translate (s.regs 4) off (28#32) (finite off h)
  · have finite : ∀ i : Word, i∈[12,16,20,24,32,40,44] → Apart i (4294967292#32) := by
      intro i hi
      simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> unfold Apart <;> decide
    simpa [BitVec.sub_eq_add_neg,BitVec.add_zero] using
      OriginalPathXStep.apart_translate (s.regs 4) off (4294967292#32) (finite off h)
  · have finite : ∀ i : Word, i∈[12,16,20,24,32,40,44] → Apart i (4294967288#32) := by
      intro i hi
      simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> unfold Apart <;> decide
    simpa [BitVec.sub_eq_add_neg,BitVec.add_zero] using
      OriginalPathXStep.apart_translate (s.regs 4) off (4294967288#32) (finite off h)
  · have finite : ∀ i : Word, i∈[12,16,20,24,32,40,44] → Apart i (4294967284#32) := by
      intro i hi
      simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> unfold Apart <;> decide
    simpa [BitVec.sub_eq_add_neg,BitVec.add_zero] using
      OriginalPathXStep.apart_translate (s.regs 4) off (4294967284#32) (finite off h)
  · have finite : ∀ i : Word, i∈[12,16,20,24,32,40,44] → Apart i (4294967280#32) := by
      intro i hi
      simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> unfold Apart <;> decide
    simpa [BitVec.sub_eq_add_neg,BitVec.add_zero] using
      OriginalPathXStep.apart_translate (s.regs 4) off (4294967280#32) (finite off h)
end Doom.Proofs.OriginalPathYStep
