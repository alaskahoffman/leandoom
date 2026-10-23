import Doom.Proofs.OriginalAbs
import Doom.Proofs.OriginalPathInit
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalPathXStep
open Verification X86 X86Memory X86Control BlockSummary
def code : List UInt8 := [0x89,0xe8,0x8b,0x5c,0x24,0x14,0x29,0xf0,0x3b,0x5c,0x24,0xc,0x7e,0x26,0xe8,0x59,0x4f,0x1,0x0,0xbb,0x1,0x0,0x0,0x0,0x89,0x4,0x24,0x89,0x5c,0x24,0x20,0x89,0xd0,0x8b,0x14,0x24,0xbb,0x0,0x0,0x1,0x0,0xe8,0xe6,0x7,0xff,0xff,0x2b,0x5c,0x24,0x8,0xeb,0x33,0x7d,0x21,0xe8,0x31,0x4f,0x1,0x0,0xbb,0xff,0xff,0xff,0xff,0x89,0x4,0x24,0x89,0x5c,0x24,0x20,0x89,0xd0,0x8b,0x14,0x24,0x8b,0x5c,0x24,0x8,0xe8,0xbf,0x7,0xff,0xff,0xeb,0x10,0xbb,0x0,0x0,0x1,0x0,0x31,0xd2,0xb8,0x0,0x0,0x0,0x1,0x89,0x54,0x24,0x20]
def bytesProgram (bytes : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2c96c≤pc ∧ pc<0x2c9d3 then X86Routine.decodeAt bytes (pc-0x2c96c) else none
def localProgram := bytesProgram code
def listed : X86Routine.Program
  | 0x2c96c => some (.control (.block (.legacy (.mov 0 5))),2)
  | 0x2c96e => some (.control (.block (.load 3 ⟨some 4,none,0,20⟩)),4)
  | 0x2c972 => some (.control (.block (.arithmetic (.sub 0 6))),2)
  | 0x2c974 => some (.control (.cmpMemory 3 ⟨some 4,none,0,12⟩),4)
  | 0x2c978 => some (.jumpSigned 1 38,2)
  | 0x2c97a => some (.call 85849,5)
  | 0x2c97f => some (.immediate 3 0x1,5)
  | 0x2c984 => some (.control (.block (.store ⟨some 4,none,0,0⟩ 0)),3)
  | 0x2c987 => some (.control (.block (.store ⟨some 4,none,0,32⟩ 3)),4)
  | 0x2c98b => some (.control (.block (.legacy (.mov 0 2))),2)
  | 0x2c98d => some (.control (.block (.load 2 ⟨some 4,none,0,0⟩)),3)
  | 0x2c990 => some (.immediate 3 0x10000,5)
  | 0x2c995 => some (.call (-63514),5)
  | 0x2c99a => some (.subMemory 3 ⟨some 4,none,0,8⟩,4)
  | 0x2c99e => some (.jump 51,2)
  | 0x2c9a0 => some (.jumpSigned 0 33,2)
  | 0x2c9a2 => some (.call 85809,5)
  | 0x2c9a7 => some (.immediate 3 0xffffffff,5)
  | 0x2c9ac => some (.control (.block (.store ⟨some 4,none,0,0⟩ 0)),3)
  | 0x2c9af => some (.control (.block (.store ⟨some 4,none,0,32⟩ 3)),4)
  | 0x2c9b3 => some (.control (.block (.legacy (.mov 0 2))),2)
  | 0x2c9b5 => some (.control (.block (.load 2 ⟨some 4,none,0,0⟩)),3)
  | 0x2c9b8 => some (.control (.block (.load 3 ⟨some 4,none,0,8⟩)),4)
  | 0x2c9bc => some (.call (-63553),5)
  | 0x2c9c1 => some (.jump 16,2)
  | 0x2c9c3 => some (.immediate 3 0x10000,5)
  | 0x2c9c8 => some (.xorRegister 2 2,2)
  | 0x2c9ca => some (.immediate 0 0x1000000,5)
  | 0x2c9cf => some (.control (.block (.store ⟨some 4,none,0,32⟩ 2)),4)
  | _ => none
theorem decoded (pc : Nat) (h : listed pc≠none) : localProgram pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def prepare_1 (s : X86Memory.State) : X86Memory.State := put (s) 0 (s.regs 5)
def prepare_v1 (s : X86Memory.State) : Word := load32 (s.memory) ((s.regs 4)+20)
def prepare_2 (s : X86Memory.State) : X86Memory.State := put (prepare_1 s) 3 (prepare_v1 s)
def prepare_3 (s : X86Memory.State) : X86Memory.State := put (prepare_2 s) 0 ((s.regs 5)-(s.regs 6))
def prepare_v3 (s : X86Memory.State) : Word := load32 (s.memory) ((s.regs 4)+12)
def prepare_4 (s : X86Memory.State) : X86Memory.State := prepare_3 s
def prepare (s : X86Memory.State) (f : Option Flags) : X86Control.State := ⟨prepare_4 s,some (compare32 (prepare_v1 s) (prepare_v3 s)),0x2c978⟩
theorem prepare_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix localProgram [] 4 ⟨s,f,0x2c96c⟩ (prepare s f) := by
  have path : X86Routine.Prefix listed [] 4 ⟨s,f,0x2c96c⟩ (prepare s f) := by
    apply X86Routine.Prefix.step (middle := ⟨prepare_1 s,f,0x2c96e⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,prepare_4,prepare_v3,prepare_3,prepare_2,prepare_v1,prepare_1,prepare])
    apply X86Routine.Prefix.step (middle := ⟨prepare_2 s,f,0x2c972⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,prepare_4,prepare_v3,prepare_3,prepare_2,prepare_v1,prepare_1,prepare])
    apply X86Routine.Prefix.step (middle := ⟨prepare_3 s,none,0x2c974⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,prepare_4,prepare_v3,prepare_3,prepare_2,prepare_v1,prepare_1,prepare])
    apply X86Routine.Prefix.step (middle := ⟨prepare_4 s,some (compare32 (prepare_v1 s) (prepare_v3 s)),0x2c978⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,prepare_4,prepare_v3,prepare_3,prepare_2,prepare_v1,prepare_1,prepare])
    exact .nil _
  exact path.transfer localProgram [] decoded (by simp)

def rightCall_m0 (s : X86Memory.State) : Memory := store32 (s.memory) (s.regs 4-4) 0x2c97f
def rightCall_1 (s : X86Memory.State) : X86Memory.State := {regs:=write (s).regs 4 (s.regs 4-4),memory:=rightCall_m0 s}
def rightCall (s : X86Memory.State) (f : Option Flags) : X86Control.State := ⟨rightCall_1 s,f,0x418d8⟩
theorem rightCall_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix localProgram [] 1 ⟨s,f,0x2c97a⟩ (rightCall s f) := by
  have path : X86Routine.Prefix listed [] 1 ⟨s,f,0x2c97a⟩ (rightCall s f) := by
    apply X86Routine.Prefix.step (middle := ⟨rightCall_1 s,f,0x418d8⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,rightCall_1,rightCall_m0,rightCall])
    exact .nil _
  exact path.transfer localProgram [] decoded (by simp)

def leftCall_m0 (s : X86Memory.State) : Memory := store32 (s.memory) (s.regs 4-4) 0x2c9a7
def leftCall_1 (s : X86Memory.State) : X86Memory.State := {regs:=write (s).regs 4 (s.regs 4-4),memory:=leftCall_m0 s}
def leftCall (s : X86Memory.State) (f : Option Flags) : X86Control.State := ⟨leftCall_1 s,f,0x418d8⟩
theorem leftCall_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix localProgram [] 1 ⟨s,f,0x2c9a2⟩ (leftCall s f) := by
  have path : X86Routine.Prefix listed [] 1 ⟨s,f,0x2c9a2⟩ (leftCall s f) := by
    apply X86Routine.Prefix.step (middle := ⟨leftCall_1 s,f,0x418d8⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,leftCall_1,leftCall_m0,leftCall])
    exact .nil _
  exact path.transfer localProgram [] decoded (by simp)

def rightDivide_1 (s : X86Memory.State) : X86Memory.State := put (s) 3 (0x1)
def rightDivide_m1 (s : X86Memory.State) : Memory := store32 (s.memory) ((s.regs 4)+0) (s.regs 0)
def rightDivide_2 (s : X86Memory.State) : X86Memory.State := {regs:=(rightDivide_1 s).regs,memory:=rightDivide_m1 s}
def rightDivide_m2 (s : X86Memory.State) : Memory := store32 (rightDivide_m1 s) ((s.regs 4)+32) (0x1)
def rightDivide_3 (s : X86Memory.State) : X86Memory.State := {regs:=(rightDivide_2 s).regs,memory:=rightDivide_m2 s}
def rightDivide_4 (s : X86Memory.State) : X86Memory.State := put (rightDivide_3 s) 0 (s.regs 2)
def rightDivide_v4 (s : X86Memory.State) : Word := load32 (rightDivide_m2 s) ((s.regs 4)+0)
def rightDivide_5 (s : X86Memory.State) : X86Memory.State := put (rightDivide_4 s) 2 (rightDivide_v4 s)
def rightDivide_6 (s : X86Memory.State) : X86Memory.State := put (rightDivide_5 s) 3 (0x10000)
def rightDivide_m6 (s : X86Memory.State) : Memory := store32 (rightDivide_m2 s) (s.regs 4-4) 0x2c99a
def rightDivide_7 (s : X86Memory.State) : X86Memory.State := {regs:=write (rightDivide_6 s).regs 4 (s.regs 4-4),memory:=rightDivide_m6 s}
def rightDivide (s : X86Memory.State) (f : Option Flags) : X86Control.State := ⟨rightDivide_7 s,f,0x1d180⟩
theorem rightDivide_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix localProgram [] 7 ⟨s,f,0x2c97f⟩ (rightDivide s f) := by
  have path : X86Routine.Prefix listed [] 7 ⟨s,f,0x2c97f⟩ (rightDivide s f) := by
    apply X86Routine.Prefix.step (middle := ⟨rightDivide_1 s,f,0x2c984⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,rightDivide_7,rightDivide_m6,rightDivide_6,rightDivide_5,rightDivide_v4,rightDivide_4,rightDivide_3,rightDivide_m2,rightDivide_2,rightDivide_m1,rightDivide_1,rightDivide])
    apply X86Routine.Prefix.step (middle := ⟨rightDivide_2 s,f,0x2c987⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,rightDivide_7,rightDivide_m6,rightDivide_6,rightDivide_5,rightDivide_v4,rightDivide_4,rightDivide_3,rightDivide_m2,rightDivide_2,rightDivide_m1,rightDivide_1,rightDivide])
    apply X86Routine.Prefix.step (middle := ⟨rightDivide_3 s,f,0x2c98b⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,rightDivide_7,rightDivide_m6,rightDivide_6,rightDivide_5,rightDivide_v4,rightDivide_4,rightDivide_3,rightDivide_m2,rightDivide_2,rightDivide_m1,rightDivide_1,rightDivide])
    apply X86Routine.Prefix.step (middle := ⟨rightDivide_4 s,f,0x2c98d⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,rightDivide_7,rightDivide_m6,rightDivide_6,rightDivide_5,rightDivide_v4,rightDivide_4,rightDivide_3,rightDivide_m2,rightDivide_2,rightDivide_m1,rightDivide_1,rightDivide])
    apply X86Routine.Prefix.step (middle := ⟨rightDivide_5 s,f,0x2c990⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,rightDivide_7,rightDivide_m6,rightDivide_6,rightDivide_5,rightDivide_v4,rightDivide_4,rightDivide_3,rightDivide_m2,rightDivide_2,rightDivide_m1,rightDivide_1,rightDivide])
    apply X86Routine.Prefix.step (middle := ⟨rightDivide_6 s,f,0x2c995⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,rightDivide_7,rightDivide_m6,rightDivide_6,rightDivide_5,rightDivide_v4,rightDivide_4,rightDivide_3,rightDivide_m2,rightDivide_2,rightDivide_m1,rightDivide_1,rightDivide])
    apply X86Routine.Prefix.step (middle := ⟨rightDivide_7 s,f,0x1d180⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,rightDivide_7,rightDivide_m6,rightDivide_6,rightDivide_5,rightDivide_v4,rightDivide_4,rightDivide_3,rightDivide_m2,rightDivide_2,rightDivide_m1,rightDivide_1,rightDivide])
    exact .nil _
  exact path.transfer localProgram [] decoded (by simp)

def leftDivide_1 (s : X86Memory.State) : X86Memory.State := put (s) 3 (0xffffffff)
def leftDivide_m1 (s : X86Memory.State) : Memory := store32 (s.memory) ((s.regs 4)+0) (s.regs 0)
def leftDivide_2 (s : X86Memory.State) : X86Memory.State := {regs:=(leftDivide_1 s).regs,memory:=leftDivide_m1 s}
def leftDivide_m2 (s : X86Memory.State) : Memory := store32 (leftDivide_m1 s) ((s.regs 4)+32) (0xffffffff)
def leftDivide_3 (s : X86Memory.State) : X86Memory.State := {regs:=(leftDivide_2 s).regs,memory:=leftDivide_m2 s}
def leftDivide_4 (s : X86Memory.State) : X86Memory.State := put (leftDivide_3 s) 0 (s.regs 2)
def leftDivide_v4 (s : X86Memory.State) : Word := load32 (leftDivide_m2 s) ((s.regs 4)+0)
def leftDivide_5 (s : X86Memory.State) : X86Memory.State := put (leftDivide_4 s) 2 (leftDivide_v4 s)
def leftDivide_v5 (s : X86Memory.State) : Word := load32 (leftDivide_m2 s) ((s.regs 4)+8)
def leftDivide_6 (s : X86Memory.State) : X86Memory.State := put (leftDivide_5 s) 3 (leftDivide_v5 s)
def leftDivide_m6 (s : X86Memory.State) : Memory := store32 (leftDivide_m2 s) (s.regs 4-4) 0x2c9c1
def leftDivide_7 (s : X86Memory.State) : X86Memory.State := {regs:=write (leftDivide_6 s).regs 4 (s.regs 4-4),memory:=leftDivide_m6 s}
def leftDivide (s : X86Memory.State) (f : Option Flags) : X86Control.State := ⟨leftDivide_7 s,f,0x1d180⟩
theorem leftDivide_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix localProgram [] 7 ⟨s,f,0x2c9a7⟩ (leftDivide s f) := by
  have path : X86Routine.Prefix listed [] 7 ⟨s,f,0x2c9a7⟩ (leftDivide s f) := by
    apply X86Routine.Prefix.step (middle := ⟨leftDivide_1 s,f,0x2c9ac⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,leftDivide_7,leftDivide_m6,leftDivide_6,leftDivide_v5,leftDivide_5,leftDivide_v4,leftDivide_4,leftDivide_3,leftDivide_m2,leftDivide_2,leftDivide_m1,leftDivide_1,leftDivide])
    apply X86Routine.Prefix.step (middle := ⟨leftDivide_2 s,f,0x2c9af⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,leftDivide_7,leftDivide_m6,leftDivide_6,leftDivide_v5,leftDivide_5,leftDivide_v4,leftDivide_4,leftDivide_3,leftDivide_m2,leftDivide_2,leftDivide_m1,leftDivide_1,leftDivide])
    apply X86Routine.Prefix.step (middle := ⟨leftDivide_3 s,f,0x2c9b3⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,leftDivide_7,leftDivide_m6,leftDivide_6,leftDivide_v5,leftDivide_5,leftDivide_v4,leftDivide_4,leftDivide_3,leftDivide_m2,leftDivide_2,leftDivide_m1,leftDivide_1,leftDivide])
    apply X86Routine.Prefix.step (middle := ⟨leftDivide_4 s,f,0x2c9b5⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,leftDivide_7,leftDivide_m6,leftDivide_6,leftDivide_v5,leftDivide_5,leftDivide_v4,leftDivide_4,leftDivide_3,leftDivide_m2,leftDivide_2,leftDivide_m1,leftDivide_1,leftDivide])
    apply X86Routine.Prefix.step (middle := ⟨leftDivide_5 s,f,0x2c9b8⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,leftDivide_7,leftDivide_m6,leftDivide_6,leftDivide_v5,leftDivide_5,leftDivide_v4,leftDivide_4,leftDivide_3,leftDivide_m2,leftDivide_2,leftDivide_m1,leftDivide_1,leftDivide])
    apply X86Routine.Prefix.step (middle := ⟨leftDivide_6 s,f,0x2c9bc⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,leftDivide_7,leftDivide_m6,leftDivide_6,leftDivide_v5,leftDivide_5,leftDivide_v4,leftDivide_4,leftDivide_3,leftDivide_m2,leftDivide_2,leftDivide_m1,leftDivide_1,leftDivide])
    apply X86Routine.Prefix.step (middle := ⟨leftDivide_7 s,f,0x1d180⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,leftDivide_7,leftDivide_m6,leftDivide_6,leftDivide_v5,leftDivide_5,leftDivide_v4,leftDivide_4,leftDivide_3,leftDivide_m2,leftDivide_2,leftDivide_m1,leftDivide_1,leftDivide])
    exact .nil _
  exact path.transfer localProgram [] decoded (by simp)

def same_1 (s : X86Memory.State) : X86Memory.State := put (s) 3 (0x10000)
def same_2 (s : X86Memory.State) : X86Memory.State := put (same_1 s) 2 (0)
def same_3 (s : X86Memory.State) : X86Memory.State := put (same_2 s) 0 (0x1000000)
def same_m3 (s : X86Memory.State) : Memory := store32 (s.memory) ((s.regs 4)+32) (0)
def same_4 (s : X86Memory.State) : X86Memory.State := {regs:=(same_3 s).regs,memory:=same_m3 s}
def same (s : X86Memory.State) (f : Option Flags) : X86Control.State := ⟨same_4 s,some {(logical32 0) with carry:=some false},0x2c9d3⟩
theorem same_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix localProgram [] 4 ⟨s,f,0x2c9c3⟩ (same s f) := by
  have path : X86Routine.Prefix listed [] 4 ⟨s,f,0x2c9c3⟩ (same s f) := by
    apply X86Routine.Prefix.step (middle := ⟨same_1 s,f,0x2c9c8⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,same_4,same_m3,same_3,same_2,same_1,same])
    apply X86Routine.Prefix.step (middle := ⟨same_2 s,some {(logical32 0) with carry:=some false},0x2c9ca⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,same_4,same_m3,same_3,same_2,same_1,same])
    apply X86Routine.Prefix.step (middle := ⟨same_3 s,some {(logical32 0) with carry:=some false},0x2c9cf⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,same_4,same_m3,same_3,same_2,same_1,same])
    apply X86Routine.Prefix.step (middle := ⟨same_4 s,some {(logical32 0) with carry:=some false},0x2c9d3⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,same_4,same_m3,same_3,same_2,same_1,same])
    exact .nil _
  exact path.transfer localProgram [] decoded (by simp)

def rightTail_v0 (s : X86Memory.State) : Word := load32 (s.memory) ((s.regs 4)+8)
def rightTail_1 (s : X86Memory.State) : X86Memory.State := put (s) 3 ((s.regs 3)-(rightTail_v0 s))
def rightTail_2 (s : X86Memory.State) : X86Memory.State := rightTail_1 s
def rightTail (s : X86Memory.State) (f : Option Flags) : X86Control.State := ⟨rightTail_2 s,none,0x2c9d3⟩
theorem rightTail_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix localProgram [] 2 ⟨s,f,0x2c99a⟩ (rightTail s f) := by
  have path : X86Routine.Prefix listed [] 2 ⟨s,f,0x2c99a⟩ (rightTail s f) := by
    apply X86Routine.Prefix.step (middle := ⟨rightTail_1 s,none,0x2c99e⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,rightTail_2,rightTail_1,rightTail_v0,rightTail])
    apply X86Routine.Prefix.step (middle := ⟨rightTail_2 s,none,0x2c9d3⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,rightTail_2,rightTail_1,rightTail_v0,rightTail])
    exact .nil _
  exact path.transfer localProgram [] decoded (by simp)

def leftTail_1 (s : X86Memory.State) : X86Memory.State := s
def leftTail (s : X86Memory.State) (f : Option Flags) : X86Control.State := ⟨leftTail_1 s,f,0x2c9d3⟩
theorem leftTail_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix localProgram [] 1 ⟨s,f,0x2c9c1⟩ (leftTail s f) := by
  have path : X86Routine.Prefix listed [] 1 ⟨s,f,0x2c9c1⟩ (leftTail s f) := by
    apply X86Routine.Prefix.step (middle := ⟨leftTail_1 s,f,0x2c9d3⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,leftTail_1,leftTail])
    exact .nil _
  exact path.transfer localProgram [] decoded (by simp)


def program (pc : Nat) : Option (X86Routine.Op × Nat) :=
  if 0x2c96c≤pc ∧ pc<0x2c9d3 then localProgram pc
  else if 0x418d8≤pc ∧ pc<0x418df then OriginalAbs.program pc
  else OriginalDivMemory.program pc

theorem contains_local (pc : Nat) (h : localProgram pc≠none) : program pc=localProgram pc := by
  by_cases a : 0x2c96c≤pc ∧ pc<0x2c9d3
  · simp [program,a]
  · simp [localProgram,bytesProgram,a] at h

theorem contains_abs (pc : Nat) (h : OriginalAbs.program pc≠none) : program pc=OriginalAbs.program pc := by
  have a : 0x418d8≤pc ∧ pc<0x418df := by
    by_cases a : 0x418d8≤pc ∧ pc<0x418df
    · exact a
    · simp [OriginalAbs.program,OriginalAbs.bytesProgram,a] at h
  simp [program,a,show ¬(0x2c96c≤pc ∧ pc<0x2c9d3) by omega]

theorem contains_div (pc : Nat) (h : OriginalDivMemory.program pc≠none) : program pc=OriginalDivMemory.program pc := by
  have a : 0x1d180≤pc ∧ pc<0x1d1c1 := by
    by_cases a : 0x1d180≤pc ∧ pc<0x1d1c1
    · exact a
    · simp [OriginalDivMemory.program,OriginalDivMemory.bytesProgram,a] at h
  simp [program,show ¬(0x2c96c≤pc ∧ pc<0x2c9d3) by omega,show ¬(0x418d8≤pc ∧ pc<0x418df) by omega]

def Forward (s : X86Memory.State) : Prop := (prepare_v3 s).toInt<(prepare_v1 s).toInt
def Backward (s : X86Memory.State) : Prop := (prepare_v1 s).toInt<(prepare_v3 s).toInt
instance (s : X86Memory.State) : Decidable (Forward s) := inferInstanceAs (Decidable (_<_))
instance (s : X86Memory.State) : Decidable (Backward s) := inferInstanceAs (Decidable (_<_))
def Still (s : X86Memory.State) : Prop := ¬Forward s ∧ ¬Backward s
instance (s : X86Memory.State) : Decidable (Still s) := inferInstanceAs (Decidable (_∧_))
def selection (s : X86Memory.State) : X86Control.State :=
  {prepare s none with pc := if Forward s then 0x2c97a else if Backward s then 0x2c9a2 else 0x2c9c3}

theorem selection_execution (s : X86Memory.State) (f : Option Flags) :
    ∃ n, n≤6 ∧ X86Routine.Prefix program [] n ⟨s,f,0x2c96c⟩ (selection s) := by
  have p := (prepare_execution s f).transfer program [] contains_local (by simp)
  have branch : ∃ n, n≤2 ∧ X86Routine.Prefix listed [] n (prepare s f) (selection s) := by
    by_cases hf : Forward s
    · refine ⟨1,by omega,?_⟩
      have less : ¬(prepare_v1 s).toInt≤(prepare_v3 s).toInt := by unfold Forward at hf; omega
      apply X86Routine.Prefix.step (middle := selection s) (by simp [prepare]) (by rfl) (by
        simp [prepare,selection,X86Routine.execute,cmp32_signed_le,less,hf])
      exact .nil _
    · by_cases hb : Backward s
      · refine ⟨2,by omega,?_⟩
        have le : (prepare_v1 s).toInt≤(prepare_v3 s).toInt := by unfold Backward at hb; omega
        have notge : ¬(prepare_v3 s).toInt≤(prepare_v1 s).toInt := by unfold Backward at hb; omega
        apply X86Routine.Prefix.step (middle := {prepare s f with pc:=0x2c9a0}) (by simp [prepare]) (by rfl) (by
          simp [prepare,X86Routine.execute,cmp32_signed_le,le])
        apply X86Routine.Prefix.step (middle := selection s) (by simp) (by rfl) (by
          simp [prepare,selection,X86Routine.execute,PlayerHeight.cmp_ge_prop,notge,hf,hb])
        exact .nil _
      · refine ⟨2,by omega,?_⟩
        have le : (prepare_v1 s).toInt≤(prepare_v3 s).toInt := by unfold Forward at hf; omega
        have ge : (prepare_v3 s).toInt≤(prepare_v1 s).toInt := by unfold Backward at hb; omega
        apply X86Routine.Prefix.step (middle := {prepare s f with pc:=0x2c9a0}) (by simp [prepare]) (by rfl) (by
          simp [prepare,X86Routine.execute,cmp32_signed_le,le])
        apply X86Routine.Prefix.step (middle := selection s) (by simp) (by rfl) (by
          simp [prepare,selection,X86Routine.execute,PlayerHeight.cmp_ge_prop,ge,hf,hb])
        exact .nil _
  obtain ⟨n,hn,b⟩ := branch
  have b := (b.transfer localProgram [] decoded (by simp)).transfer program [] contains_local (by simp)
  exact ⟨4+n,by omega,OriginalGroupBounds.prefix_join p b⟩

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
    (OriginalAbs.result (absCall right s f).core).pc=(if right then 0x2c97f else 0x2c9a7) := by
  cases right <;> simp [absCall,rightCall,leftCall,rightCall_1,leftCall_1,
    rightCall_m0,leftCall_m0,OriginalAbs.result,write,load_store]

theorem divide_return (right : Bool) (s : X86Memory.State) (f : Option Flags) :
    (OriginalDivMemory.result (divideCall right s f).core).pc=(if right then 0x2c99a else 0x2c9c1) := by
  rw [(OriginalDivMemory.restored_registers _).2.2.2.2]
  cases right <;> simp [divideCall,rightDivide,rightDivide_7,rightDivide_m6,rightDivide_6,
    leftDivide,leftDivide_7,leftDivide_m6,leftDivide_6,write,load_store]

theorem abs_call_execution (right : Bool) (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 1 ⟨s,f,if right then 0x2c97a else 0x2c9a2⟩ (absCall right s f) := by
  cases right
  · exact (leftCall_execution s f).transfer program [] contains_local (by simp)
  · exact (rightCall_execution s f).transfer program [] contains_local (by simp)

theorem divide_call_execution (right : Bool) (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 7 ⟨s,f,if right then 0x2c97f else 0x2c9a7⟩ (divideCall right s f) := by
  cases right
  · exact (leftDivide_execution s f).transfer program [] contains_local (by simp)
  · exact (rightDivide_execution s f).transfer program [] contains_local (by simp)

theorem tail_execution (right : Bool) (s : X86Memory.State) (f : Option Flags) :
    ∃ n, n≤2 ∧ X86Routine.Prefix program [] n ⟨s,f,if right then 0x2c99a else 0x2c9c1⟩ (tail right s f) := by
  cases right
  · exact ⟨1,by omega,(leftTail_execution s f).transfer program [] contains_local (by simp)⟩
  · exact ⟨2,by omega,(rightTail_execution s f).transfer program [] contains_local (by simp)⟩

theorem at_pc (s : X86Control.State) (pc : Nat) (h : s.pc=pc) :
    (⟨s.core,s.flags,pc⟩ : X86Control.State)=s := by rw [←h]

theorem moving_execution (right : Bool) (s : X86Memory.State) (f : Option Flags)
    (safe : OriginalDivMemory.Safe (divisionInput right s f).core) :
    ∃ n, n≤39 ∧ X86Routine.Prefix program [] n
      ⟨s,f,if right then 0x2c97a else 0x2c9a2⟩ (movingResult right s f) := by
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
  have dpc : (OriginalDivMemory.result (divisionInput right s f).core).pc=(if right then 0x2c99a else 0x2c9c1) :=
    divide_return right (OriginalAbs.result (absCall right s f).core).core (OriginalAbs.result (absCall right s f).core).flags
  rw [at_pc _ _ dpc] at e
  exact ⟨1+nb+7+nd+ne,by omega,OriginalGroupBounds.prefix_join
    (OriginalGroupBounds.prefix_join (OriginalGroupBounds.prefix_join (OriginalGroupBounds.prefix_join a b) c) d) e⟩

def Safe (s : X86Memory.State) : Prop := ¬Still s →
  OriginalDivMemory.Safe (divisionInput (decide (Forward s)) (selection s).core (selection s).flags).core

def result (s : X86Memory.State) : X86Control.State :=
  if Still s then same (selection s).core (selection s).flags
  else movingResult (decide (Forward s)) (selection s).core (selection s).flags

/-- Three direction branches, including real absolute-value and FixedDiv calls,
stack writes, returns and portion adjustment. Faulting division is excluded. -/
theorem execution (s : X86Memory.State) (f : Option Flags) (safe : Safe s) :
    ∃ n, n≤45 ∧ X86Routine.Prefix program [] n ⟨s,f,0x2c96c⟩ (result s) := by
  obtain ⟨n,hn,a⟩ := selection_execution s f
  by_cases still : Still s
  · have b := (same_execution (selection s).core (selection s).flags).transfer program [] contains_local (by simp)
    have pc : (selection s).pc=0x2c9c3 := by simp [selection,still.1,still.2]
    rw [at_pc _ _ pc] at b
    exact ⟨n+4,by omega,by simpa only [result,if_pos still] using OriginalGroupBounds.prefix_join a b⟩
  · obtain ⟨m,hm,b⟩ := moving_execution (decide (Forward s)) (selection s).core (selection s).flags (safe still)
    have pc : (selection s).pc=(if decide (Forward s) then 0x2c97a else 0x2c9a2) := by
      by_cases forward : Forward s
      · simp [selection,forward]
      · have back : Backward s := by
          by_cases hb : Backward s
          · exact hb
          · exact False.elim (still ⟨forward,hb⟩)
        simp [selection,forward,back]
    rw [at_pc _ _ pc] at b
    exact ⟨n+m,by omega,by simpa only [result,if_neg still] using OriginalGroupBounds.prefix_join a b⟩

theorem result_pc (s : X86Memory.State) : (result s).pc=0x2c9d3 := by
  unfold result movingResult tail
  split
  · rfl
  · split <;> rfl


/-- Translation preserves byte separation, even across address wraparound. -/
theorem apart_translate (sp a b : Word) (h : Apart a b) : Apart (sp+a) (sp+b) := by
  intro i j eq
  simp only [BitVec.add_assoc] at eq
  exact h i j ((BitVec.add_right_inj sp).mp eq)
@[local simp] theorem slot_0_32 (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(32#32)) v) (sp+(0#32))=load32 m (sp+(0#32)) := by
  exact load_store_apart _ _ _ _ (apart_translate sp _ _ (by unfold Apart; decide))
@[local simp] theorem slot_0_4294967292 (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(4294967292#32)) v) (sp+(0#32))=load32 m (sp+(0#32)) := by
  exact load_store_apart _ _ _ _ (apart_translate sp _ _ (by unfold Apart; decide))
@[local simp] theorem slot_0_4294967288 (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(4294967288#32)) v) (sp+(0#32))=load32 m (sp+(0#32)) := by
  exact load_store_apart _ _ _ _ (apart_translate sp _ _ (by unfold Apart; decide))
@[local simp] theorem slot_0_4294967284 (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(4294967284#32)) v) (sp+(0#32))=load32 m (sp+(0#32)) := by
  exact load_store_apart _ _ _ _ (apart_translate sp _ _ (by unfold Apart; decide))
@[local simp] theorem slot_0_4294967280 (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(4294967280#32)) v) (sp+(0#32))=load32 m (sp+(0#32)) := by
  exact load_store_apart _ _ _ _ (apart_translate sp _ _ (by unfold Apart; decide))
@[local simp] theorem slot_8_0 (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(0#32)) v) (sp+(8#32))=load32 m (sp+(8#32)) := by
  exact load_store_apart _ _ _ _ (apart_translate sp _ _ (by unfold Apart; decide))
@[local simp] theorem slot_8_32 (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(32#32)) v) (sp+(8#32))=load32 m (sp+(8#32)) := by
  exact load_store_apart _ _ _ _ (apart_translate sp _ _ (by unfold Apart; decide))
@[local simp] theorem slot_8_4294967292 (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(4294967292#32)) v) (sp+(8#32))=load32 m (sp+(8#32)) := by
  exact load_store_apart _ _ _ _ (apart_translate sp _ _ (by unfold Apart; decide))
@[local simp] theorem slot_8_4294967288 (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(4294967288#32)) v) (sp+(8#32))=load32 m (sp+(8#32)) := by
  exact load_store_apart _ _ _ _ (apart_translate sp _ _ (by unfold Apart; decide))
@[local simp] theorem slot_8_4294967284 (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(4294967284#32)) v) (sp+(8#32))=load32 m (sp+(8#32)) := by
  exact load_store_apart _ _ _ _ (apart_translate sp _ _ (by unfold Apart; decide))
@[local simp] theorem slot_8_4294967280 (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(4294967280#32)) v) (sp+(8#32))=load32 m (sp+(8#32)) := by
  exact load_store_apart _ _ _ _ (apart_translate sp _ _ (by unfold Apart; decide))
@[local simp] theorem slot_32_0 (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(0#32)) v) (sp+(32#32))=load32 m (sp+(32#32)) := by
  exact load_store_apart _ _ _ _ (apart_translate sp _ _ (by unfold Apart; decide))
@[local simp] theorem slot_32_4294967292 (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(4294967292#32)) v) (sp+(32#32))=load32 m (sp+(32#32)) := by
  exact load_store_apart _ _ _ _ (apart_translate sp _ _ (by unfold Apart; decide))
@[local simp] theorem slot_32_4294967288 (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(4294967288#32)) v) (sp+(32#32))=load32 m (sp+(32#32)) := by
  exact load_store_apart _ _ _ _ (apart_translate sp _ _ (by unfold Apart; decide))
@[local simp] theorem slot_32_4294967284 (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(4294967284#32)) v) (sp+(32#32))=load32 m (sp+(32#32)) := by
  exact load_store_apart _ _ _ _ (apart_translate sp _ _ (by unfold Apart; decide))
@[local simp] theorem slot_32_4294967280 (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(4294967280#32)) v) (sp+(32#32))=load32 m (sp+(32#32)) := by
  exact load_store_apart _ _ _ _ (apart_translate sp _ _ (by unfold Apart; decide))
@[local simp] theorem slot_zero_32 (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(32#32)) v) sp=load32 m sp := by
  simpa using slot_0_32 m sp v
@[local simp] theorem slot_eight_zero (m : Memory) (sp v : Word) :
    load32 (store32 m sp v) (sp+(8#32))=load32 m (sp+(8#32)) := by
  simpa using slot_8_0 m sp v

theorem abs_observe (right : Bool) (s : X86Memory.State) (f : Option Flags) :
    (OriginalAbs.result (absCall right s f).core).core.regs 0=OriginalAbs.value (s.regs 0) ∧
    (OriginalAbs.result (absCall right s f).core).core.regs 2=s.regs 2 ∧
    (OriginalAbs.result (absCall right s f).core).core.regs 4=s.regs 4 ∧
    (OriginalAbs.result (absCall right s f).core).core.memory=
      store32 s.memory (s.regs 4-4) (if right then 0x2c97f else 0x2c9a7) := by
  cases right <;> by_cases h : (s.regs 0).toInt<0 <;> simp [absCall,OriginalAbs.result,OriginalAbs.value,rightCall,leftCall,rightCall_1,leftCall_1,rightCall_m0,leftCall_m0,put,write,BitVec.sub_add_cancel,h]

theorem divide_observe (right : Bool) (s : X86Memory.State) (f : Option Flags) :
    (divideCall right s f).core.regs 0=s.regs 2 ∧
    (divideCall right s f).core.regs 2=s.regs 0 ∧
    (divideCall right s f).core.regs 3=(if right then 0x10000 else load32 s.memory (s.regs 4+8)) ∧
    (divideCall right s f).core.regs 4=s.regs 4-4 ∧
    (divideCall right s f).core.memory=
      store32 (store32 (store32 s.memory (s.regs 4) (s.regs 0)) (s.regs 4+32)
        (if right then 1 else 0xffffffff)) (s.regs 4-4) (if right then 0x2c99a else 0x2c9c1) := by
  cases right <;> simp [divideCall,rightDivide,rightDivide_7,rightDivide_m6,rightDivide_6,rightDivide_5,rightDivide_v4,rightDivide_4,rightDivide_3,rightDivide_m2,rightDivide_2,rightDivide_m1,rightDivide_1,leftDivide,leftDivide_7,leftDivide_m6,leftDivide_6,leftDivide_v5,leftDivide_5,leftDivide_v4,leftDivide_4,leftDivide_3,leftDivide_m2,leftDivide_2,leftDivide_m1,leftDivide_1,put,write,load_store]

theorem input_observe (right : Bool) (s : X86Memory.State) (f : Option Flags) :
    (divisionInput right s f).core.regs 0=s.regs 2 ∧
    (divisionInput right s f).core.regs 2=OriginalAbs.value (s.regs 0) ∧
    (divisionInput right s f).core.regs 3=(if right then 0x10000 else load32 s.memory (s.regs 4+8)) ∧
    (divisionInput right s f).core.regs 4=s.regs 4-4 ∧
    (divisionInput right s f).core.memory=
      store32 (store32 (store32 (store32 s.memory (s.regs 4-4) (if right then 0x2c97f else 0x2c9a7))
        (s.regs 4) (OriginalAbs.value (s.regs 0))) (s.regs 4+32)
        (if right then 1 else 0xffffffff)) (s.regs 4-4) (if right then 0x2c99a else 0x2c9c1) := by
  have a := abs_observe right s f
  have d := divide_observe right (OriginalAbs.result (absCall right s f).core).core
    (OriginalAbs.result (absCall right s f).core).flags
  unfold divisionInput
  dsimp only
  rw [d.1,d.2.1,d.2.2.1,d.2.2.2.1,d.2.2.2.2,a.1,a.2.1,a.2.2.1,a.2.2.2]
  simp [BitVec.sub_eq_add_neg]

/-- The moving branch exposes the division result and preserves the portion slot. -/
theorem moving_observe (right : Bool) (s : X86Memory.State) (f : Option Flags) :
    (movingResult right s f).core.regs 0=OriginalDivMemory.answer (s.regs 2) (OriginalAbs.value (s.regs 0)) ∧
    (movingResult right s f).core.regs 3=(if right then 0x10000-load32 s.memory (s.regs 4+8) else load32 s.memory (s.regs 4+8)) ∧
    load32 (movingResult right s f).core.memory (s.regs 4+32)=(if right then 1 else 0xffffffff) ∧
    (movingResult right s f).core.regs 4=s.regs 4 := by
  have input := input_observe right s f
  have rr := OriginalDivMemory.restored_registers (divisionInput right s f).core
  have rv := OriginalDivMemory.result_value (divisionInput right s f).core
  have mem : (OriginalDivMemory.result (divisionInput right s f).core).core.memory=
      (OriginalDivMemory.saved (divisionInput right s f).core).memory := by
    change (OriginalDivMemory.body (divisionInput right s f).core).core.memory=_
    exact OriginalDivMemory.body_memory _
  have eight : load32 (OriginalDivMemory.result (divisionInput right s f).core).core.memory (s.regs 4+8)=
      load32 s.memory (s.regs 4+8) := by
    rw [mem]
    simp [OriginalDivMemory.saved_memory,input.2.2.2.1,input.2.2.2.2,BitVec.sub_eq_add_neg,
      BitVec.add_assoc]
  have direction : load32 (OriginalDivMemory.result (divisionInput right s f).core).core.memory (s.regs 4+32)=
      (if right then 1 else 0xffffffff) := by
    rw [mem]
    simp [OriginalDivMemory.saved_memory,input.2.2.2.1,input.2.2.2.2,BitVec.sub_eq_add_neg,
      BitVec.add_assoc,load_store]
  cases right <;> simp only [movingResult,tail,Bool.false_eq_true,↓reduceIte,rightTail,rightTail_2,rightTail_1,rightTail_v0,leftTail,leftTail_1,put,write]
  all_goals simp only [rv,rr.2.2.1,rr.2.2.2.1,input.1,input.2.1,input.2.2.1,input.2.2.2.1,
    BitVec.sub_add_cancel,Bool.false_eq_true,↓reduceIte,eight,direction,and_self]
  all_goals simp


/-- Reuse the existing complete FixedDiv proof at this real call site. -/
theorem division_success (right : Bool) (s : X86Memory.State) (f : Option Flags)
    (numerator denominator quotient : Fixed)
    (hn : s.regs 2=numerator.raw.toBitVec)
    (hd : OriginalAbs.value (s.regs 0)=denominator.raw.toBitVec)
    (ok : Collision.checkedPathDiv numerator denominator=.ok quotient) :
    OriginalDivMemory.Safe (divisionInput right s f).core ∧
    OriginalDivMemory.answer (s.regs 2) (OriginalAbs.value (s.regs 0))=quotient.raw.toBitVec := by
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
  startX : s.regs 6=p.x1.raw.toBitVec
  endX : s.regs 5=p.x2.raw.toBitVec
  deltaY : s.regs 2=(p.y2-p.y1).raw.toBitVec
  startBlock : load32 s.memory (s.regs 4+12)=p.startBlockX.toBitVec
  endBlock : load32 s.memory (s.regs 4+20)=p.endBlockX.toBitVec
  fraction : load32 s.memory (s.regs 4+8)=p.xFraction.raw.toBitVec

def observe (s : X86Memory.State) (t : X86Control.State) : Word × Word × Word :=
  (load32 t.core.memory (s.regs 4+32),t.core.regs 3,t.core.regs 0)
def liveObserve (v : Int32 × Fixed × Fixed) : Word × Word × Word :=
  (v.1.toBitVec,v.2.1.raw.toBitVec,v.2.2.raw.toBitVec)

theorem selection_observe (s : X86Memory.State) :
    (selection s).core.regs 0=s.regs 5-s.regs 6 ∧
    (selection s).core.regs 2=s.regs 2 ∧ (selection s).core.regs 4=s.regs 4 ∧
    (selection s).core.memory=s.memory := by
  simp [selection,prepare,prepare_4,prepare_3,prepare_2,prepare_1,put,write]

theorem forward_iff (s : X86Memory.State) (p : Collision.PathStart) (h : Inputs s p) :
    Forward s ↔ p.startBlockX<p.endBlockX := by
  simp only [Forward,prepare_v1,prepare_v3,h.startBlock,h.endBlock,Int32.lt_iff_toInt_lt]
  rfl

theorem still_iff (s : X86Memory.State) (p : Collision.PathStart) (h : Inputs s p) :
    Still s ↔ p.endBlockX=p.startBlockX := by
  simp only [Still,Forward,Backward,prepare_v1,prepare_v3,h.startBlock,h.endBlock]
  change (¬p.startBlockX.toInt<p.endBlockX.toInt ∧ ¬p.endBlockX.toInt<p.startBlockX.toInt) ↔ _
  rw [←Int32.toInt_inj]
  omega

/-- Successful live arithmetic supplies IDIV safety; the theorem does not assume
that the x86 output matches the engine. -/
theorem live (s : X86Memory.State) (p : Collision.PathStart) (out : Int32 × Fixed × Fixed)
    (h : Inputs s p) (ok : p.xStep=.ok out) :
    Safe s ∧ observe s (result s)=liveObserve out := by
  have sel := selection_observe s
  have num : (selection s).core.regs 2=(p.y2-p.y1).raw.toBitVec := sel.2.1.trans h.deltaY
  have delta : (selection s).core.regs 0=(p.x2-p.x1).raw.toBitVec := by
    rw [sel.1,h.endX,h.startX]; rfl
  by_cases still : p.endBlockX=p.startBlockX
  · have st : Still s := (still_iff s p h).mpr still
    have output : out=(0,Fixed.ofInt 1,Fixed.ofInt 256) := by
      simpa [Collision.PathStart.xStep,bind,pure,Except.bind,Except.pure,Functor.map,Except.map,still] using ok.symm
    refine ⟨fun moving => False.elim (moving st),?_⟩
    rw [output]
    simp [observe,result,st,same,same_4,same_m3,same_3,same_2,same_1,
      put,write,sel.2.2.1,load_store,liveObserve,Fixed.ofInt]
  · have st : ¬Still s := fun hs => still ((still_iff s p h).mp hs)
    cases ha : Collision.checkedPathAbs (p.x2-p.x1) with
    | error e => simp [Collision.PathStart.xStep,bind,pure,Except.bind,Except.pure,Functor.map,Except.map,still,ha] at ok
    | ok denominator =>
      cases hd : Collision.checkedPathDiv (p.y2-p.y1) denominator with
      | error e => simp [Collision.PathStart.xStep,bind,pure,Except.bind,Except.pure,Functor.map,Except.map,still,ha,hd] at ok
      | ok quotient =>
        have abs : OriginalAbs.value ((selection s).core.regs 0)=denominator.raw.toBitVec := by
          rw [delta]; exact OriginalAbs.checked _ _ ha
        have div := division_success (decide (Forward s)) (selection s).core (selection s).flags
          (p.y2-p.y1) denominator quotient num abs hd
        refine ⟨fun _ => div.1,?_⟩
        have output : out=(if p.endBlockX>p.startBlockX then 1 else -1,
            if p.endBlockX>p.startBlockX then Fixed.ofInt 1-p.xFraction else p.xFraction,quotient) := by
          simpa [Collision.PathStart.xStep,bind,pure,Except.bind,Except.pure,Functor.map,Except.map,still,ha,hd] using ok.symm
        have obs := moving_observe (decide (Forward s)) (selection s).core (selection s).flags
        rw [output]
        simp only [observe,result,if_neg st,liveObserve]
        rw [←sel.2.2.1,obs.2.2.1,obs.2.1,obs.1,div.2,sel.2.2.1,sel.2.2.2,h.fraction]
        by_cases forward : Forward s
        · have fwd := (forward_iff s p h).mp forward
          simp only [forward,decide_true,↓reduceIte,fwd]
          rfl
        · have fwd : ¬p.startBlockX<p.endBlockX := fun hf => forward ((forward_iff s p h).mpr hf)
          simp only [forward,decide_false,↓reduceIte,fwd]
          rfl

end Doom.Proofs.OriginalPathXStep
