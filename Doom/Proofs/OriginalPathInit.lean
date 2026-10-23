import Doom.Proofs.OriginalAimSetup
import Doom.Path
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalPathInit
open Verification X86 X86Memory X86Control BlockSummary
def code : List UInt8 := [0x56,0x57,0x55,0x83,0xec,0x30,0x89,0xc6,0x89,0xd7,0x89,0xdd,0x8b,0x44,0x24,0x40,0xba,0x20,0xba,0x2,0x0,0x8b,0x1d,0x80,0x35,0x1,0x0,0x83,0xe0,0x4,0x89,0x15,0x28,0xc0,0x2,0x0,0x8b,0x15,0x4,0xc1,0x2,0x0,0xa3,0x24,0xc0,0x2,0x0,0x89,0xf0,0x43,0x29,0xd0,0x89,0x1d,0x80,0x35,0x1,0x0,0xa9,0xff,0xff,0x7f,0x0,0x75,0x6,0x81,0xc6,0x0,0x0,0x1,0x0,0x8b,0x1d,0x8,0xc1,0x2,0x0,0x89,0xf8,0x29,0xd8,0xa9,0xff,0xff,0x7f,0x0,0x75,0x6,0x81,0xc7,0x0,0x0,0x1,0x0,0x89,0xe8,0x8b,0x15,0x8,0xc1,0x2,0x0,0x29,0xf0,0x8b,0x1d,0x4,0xc1,0x2,0x0,0xa3,0x18,0xba,0x2,0x0,0x89,0xc8,0x89,0x35,0x10,0xba,0x2,0x0,0x29,0xf8,0x89,0x3d,0x14,0xba,0x2,0x0,0xa3,0x1c,0xba,0x2,0x0,0xa1,0x4,0xc1,0x2,0x0,0x29,0xdd,0x29,0xc6,0x29,0xd1,0x89,0xf0,0x29,0xd7,0xc1,0xf8,0x17,0x89,0xca,0x89,0x44,0x24,0xc,0x89,0xf8,0x29,0xfa,0xc1,0xf8,0x17,0x89,0xf3,0x89,0x44,0x24,0x10,0x89,0xe8,0xc1,0xfb,0x7,0xc1,0xf8,0x17,0x89,0x44,0x24,0x14,0x89,0xc8,0x81,0xe3,0xff,0xff,0x0,0x0,0xc1,0xf8,0x17,0x89,0x5c,0x24,0x8,0x89,0x44,0x24,0x18]
def bytesProgram (bytes : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2c8a0 ≤ pc ∧ pc < 0x2c96c then X86Routine.decodeAt bytes (pc-0x2c8a0) else none
def program := bytesProgram code
def listed : X86Routine.Program
  | 0x2c8a0 => some (.push 6,1)
  | 0x2c8a1 => some (.push 7,1)
  | 0x2c8a2 => some (.push 5,1)
  | 0x2c8a3 => some (.addImmediate 4 0xffffffd0,3)
  | 0x2c8a6 => some (.control (.block (.legacy (.mov 6 0))),2)
  | 0x2c8a8 => some (.control (.block (.legacy (.mov 7 2))),2)
  | 0x2c8aa => some (.control (.block (.legacy (.mov 5 3))),2)
  | 0x2c8ac => some (.control (.block (.load 0 ⟨some 4,none,0,0x40⟩)),4)
  | 0x2c8b0 => some (.immediate 2 0x2ba20,5)
  | 0x2c8b5 => some (.control (.block (.load 3 ⟨none,none,0,0x13580⟩)),6)
  | 0x2c8bb => some (.andRegister 0 0x4,3)
  | 0x2c8be => some (.control (.block (.store ⟨none,none,0,0x2c028⟩ 2)),6)
  | 0x2c8c4 => some (.control (.block (.load 2 ⟨none,none,0,0x2c104⟩)),6)
  | 0x2c8ca => some (.control (.storeEax 0x2c024),5)
  | 0x2c8cf => some (.control (.block (.legacy (.mov 0 6))),2)
  | 0x2c8d1 => some (.addImmediate 3 1,1)
  | 0x2c8d2 => some (.control (.block (.arithmetic (.sub 0 2))),2)
  | 0x2c8d4 => some (.control (.block (.store ⟨none,none,0,0x13580⟩ 3)),6)
  | 0x2c8da => some (.testRegisterImmediate 0 0x7fffff,5)
  | 0x2c8df => some (.control (.jumpZero false 6),2)
  | 0x2c8e1 => some (.addImmediate 6 0x10000,6)
  | 0x2c8e7 => some (.control (.block (.load 3 ⟨none,none,0,0x2c108⟩)),6)
  | 0x2c8ed => some (.control (.block (.legacy (.mov 0 7))),2)
  | 0x2c8ef => some (.control (.block (.arithmetic (.sub 0 3))),2)
  | 0x2c8f1 => some (.testRegisterImmediate 0 0x7fffff,5)
  | 0x2c8f6 => some (.control (.jumpZero false 6),2)
  | 0x2c8f8 => some (.addImmediate 7 0x10000,6)
  | 0x2c8fe => some (.control (.block (.legacy (.mov 0 5))),2)
  | 0x2c900 => some (.control (.block (.load 2 ⟨none,none,0,0x2c108⟩)),6)
  | 0x2c906 => some (.control (.block (.arithmetic (.sub 0 6))),2)
  | 0x2c908 => some (.control (.block (.load 3 ⟨none,none,0,0x2c104⟩)),6)
  | 0x2c90e => some (.control (.storeEax 0x2ba18),5)
  | 0x2c913 => some (.control (.block (.legacy (.mov 0 1))),2)
  | 0x2c915 => some (.control (.block (.store ⟨none,none,0,0x2ba10⟩ 6)),6)
  | 0x2c91b => some (.control (.block (.arithmetic (.sub 0 7))),2)
  | 0x2c91d => some (.control (.block (.store ⟨none,none,0,0x2ba14⟩ 7)),6)
  | 0x2c923 => some (.control (.storeEax 0x2ba1c),5)
  | 0x2c928 => some (.control (.block (.load 0 ⟨none,none,0,0x2c104⟩)),5)
  | 0x2c92d => some (.control (.block (.arithmetic (.sub 5 3))),2)
  | 0x2c92f => some (.control (.block (.arithmetic (.sub 6 0))),2)
  | 0x2c931 => some (.control (.block (.arithmetic (.sub 1 2))),2)
  | 0x2c933 => some (.control (.block (.legacy (.mov 0 6))),2)
  | 0x2c935 => some (.control (.block (.arithmetic (.sub 7 2))),2)
  | 0x2c937 => some (.sar 0 23,3)
  | 0x2c93a => some (.control (.block (.legacy (.mov 2 1))),2)
  | 0x2c93c => some (.control (.block (.store ⟨some 4,none,0,0xc⟩ 0)),4)
  | 0x2c940 => some (.control (.block (.legacy (.mov 0 7))),2)
  | 0x2c942 => some (.control (.block (.arithmetic (.sub 2 7))),2)
  | 0x2c944 => some (.sar 0 23,3)
  | 0x2c947 => some (.control (.block (.legacy (.mov 3 6))),2)
  | 0x2c949 => some (.control (.block (.store ⟨some 4,none,0,0x10⟩ 0)),4)
  | 0x2c94d => some (.control (.block (.legacy (.mov 0 5))),2)
  | 0x2c94f => some (.sar 3 7,3)
  | 0x2c952 => some (.sar 0 23,3)
  | 0x2c955 => some (.control (.block (.store ⟨some 4,none,0,0x14⟩ 0)),4)
  | 0x2c959 => some (.control (.block (.legacy (.mov 0 1))),2)
  | 0x2c95b => some (.andRegister 3 0xffff,6)
  | 0x2c961 => some (.sar 0 23,3)
  | 0x2c964 => some (.control (.block (.store ⟨some 4,none,0,0x8⟩ 3)),4)
  | 0x2c968 => some (.control (.block (.store ⟨some 4,none,0,0x18⟩ 0)),4)
  | _ => none
theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

-- Reads name the memory at the actual instruction, including stack/global overlap.
def m1 (s : X86Memory.State) : Memory := store32 (s.memory) (s.regs 4-4) (s.regs 6)
def c1 (s : X86Memory.State) : X86Memory.State := {regs:=write (s).regs 4 (s.regs 4-4),memory:=m1 s}
def m2 (s : X86Memory.State) : Memory := store32 (m1 s) (s.regs 4-8) (s.regs 7)
def c2 (s : X86Memory.State) : X86Memory.State := {regs:=write (c1 s).regs 4 (s.regs 4-8),memory:=m2 s}
def m3 (s : X86Memory.State) : Memory := store32 (m2 s) (s.regs 4-12) (s.regs 5)
def c3 (s : X86Memory.State) : X86Memory.State := {regs:=write (c2 s).regs 4 (s.regs 4-12),memory:=m3 s}
def c4 (s : X86Memory.State) : X86Memory.State := put (c3 s) 4 (s.regs 4-60)
def c5 (s : X86Memory.State) : X86Memory.State := put (c4 s) 6 (s.regs 0)
def c6 (s : X86Memory.State) : X86Memory.State := put (c5 s) 7 (s.regs 2)
def c7 (s : X86Memory.State) : X86Memory.State := put (c6 s) 5 (s.regs 3)
def argument (s : X86Memory.State) : Word := load32 (m3 s) (s.regs 4+4)
def c8 (s : X86Memory.State) : X86Memory.State := put (c7 s) 0 (argument s)
def c9 (s : X86Memory.State) : X86Memory.State := put (c8 s) 2 (0x2ba20)
def oldValid (s : X86Memory.State) : Word := load32 (m3 s) (0x13580)
def c10 (s : X86Memory.State) : X86Memory.State := put (c9 s) 3 (oldValid s)
def c11 (s : X86Memory.State) : X86Memory.State := put (c10 s) 0 ((argument s) &&& 0x4)
def m4 (s : X86Memory.State) : Memory := store32 (m3 s) (0x2c028) (0x2ba20)
def c12 (s : X86Memory.State) : X86Memory.State := {regs:=(c11 s).regs,memory:=m4 s}
def orgX0 (s : X86Memory.State) : Word := load32 (m4 s) (0x2c104)
def c13 (s : X86Memory.State) : X86Memory.State := put (c12 s) 2 (orgX0 s)
def m5 (s : X86Memory.State) : Memory := store32 (m4 s) (0x2c024) ((argument s) &&& 0x4)
def c14 (s : X86Memory.State) : X86Memory.State := {regs:=(c13 s).regs,memory:=m5 s}
def c15 (s : X86Memory.State) : X86Memory.State := put (c14 s) 0 (s.regs 0)
def c16 (s : X86Memory.State) : X86Memory.State := put (c15 s) 3 ((oldValid s)+1)
def c17 (s : X86Memory.State) : X86Memory.State := put (c16 s) 0 ((s.regs 0)-(orgX0 s))
def m6 (s : X86Memory.State) : Memory := store32 (m5 s) (0x13580) ((oldValid s)+1)
def c18 (s : X86Memory.State) : X86Memory.State := {regs:=(c17 s).regs,memory:=m6 s}
def boundaryX (s : X86Memory.State) : Prop := ((s.regs 0)-(orgX0 s)) &&& 0x7fffff = 0
instance (s : X86Memory.State) : Decidable (boundaryX s) := inferInstanceAs (Decidable (_ = _))
def c19 (s : X86Memory.State) : X86Memory.State := c18 s
def c20 (s : X86Memory.State) : X86Memory.State := c19 s
def nudgedX (s : X86Memory.State) : Word := if boundaryX s then s.regs 0+0x10000 else s.regs 0
def c21 (s : X86Memory.State) : X86Memory.State := put (c20 s) 6 (nudgedX s)
def orgY0 (s : X86Memory.State) : Word := load32 (m6 s) (0x2c108)
def c22 (s : X86Memory.State) : X86Memory.State := put (c21 s) 3 (orgY0 s)
def c23 (s : X86Memory.State) : X86Memory.State := put (c22 s) 0 (s.regs 2)
def c24 (s : X86Memory.State) : X86Memory.State := put (c23 s) 0 ((s.regs 2)-(orgY0 s))
def boundaryY (s : X86Memory.State) : Prop := ((s.regs 2)-(orgY0 s)) &&& 0x7fffff = 0
instance (s : X86Memory.State) : Decidable (boundaryY s) := inferInstanceAs (Decidable (_ = _))
def c25 (s : X86Memory.State) : X86Memory.State := c24 s
def c26 (s : X86Memory.State) : X86Memory.State := c25 s
def nudgedY (s : X86Memory.State) : Word := if boundaryY s then s.regs 2+0x10000 else s.regs 2
def c27 (s : X86Memory.State) : X86Memory.State := put (c26 s) 7 (nudgedY s)
def c28 (s : X86Memory.State) : X86Memory.State := put (c27 s) 0 (s.regs 3)
def orgY1 (s : X86Memory.State) : Word := load32 (m6 s) (0x2c108)
def c29 (s : X86Memory.State) : X86Memory.State := put (c28 s) 2 (orgY1 s)
def c30 (s : X86Memory.State) : X86Memory.State := put (c29 s) 0 ((s.regs 3)-(nudgedX s))
def orgX1 (s : X86Memory.State) : Word := load32 (m6 s) (0x2c104)
def c31 (s : X86Memory.State) : X86Memory.State := put (c30 s) 3 (orgX1 s)
def m7 (s : X86Memory.State) : Memory := store32 (m6 s) (0x2ba18) ((s.regs 3)-(nudgedX s))
def c32 (s : X86Memory.State) : X86Memory.State := {regs:=(c31 s).regs,memory:=m7 s}
def c33 (s : X86Memory.State) : X86Memory.State := put (c32 s) 0 (s.regs 1)
def m8 (s : X86Memory.State) : Memory := store32 (m7 s) (0x2ba10) (nudgedX s)
def c34 (s : X86Memory.State) : X86Memory.State := {regs:=(c33 s).regs,memory:=m8 s}
def c35 (s : X86Memory.State) : X86Memory.State := put (c34 s) 0 ((s.regs 1)-(nudgedY s))
def m9 (s : X86Memory.State) : Memory := store32 (m8 s) (0x2ba14) (nudgedY s)
def c36 (s : X86Memory.State) : X86Memory.State := {regs:=(c35 s).regs,memory:=m9 s}
def m10 (s : X86Memory.State) : Memory := store32 (m9 s) (0x2ba1c) ((s.regs 1)-(nudgedY s))
def c37 (s : X86Memory.State) : X86Memory.State := {regs:=(c36 s).regs,memory:=m10 s}
def orgX2 (s : X86Memory.State) : Word := load32 (m10 s) (0x2c104)
def c38 (s : X86Memory.State) : X86Memory.State := put (c37 s) 0 (orgX2 s)
def c39 (s : X86Memory.State) : X86Memory.State := put (c38 s) 5 ((s.regs 3)-(orgX1 s))
def c40 (s : X86Memory.State) : X86Memory.State := put (c39 s) 6 ((nudgedX s)-(orgX2 s))
def c41 (s : X86Memory.State) : X86Memory.State := put (c40 s) 1 ((s.regs 1)-(orgY1 s))
def c42 (s : X86Memory.State) : X86Memory.State := put (c41 s) 0 ((nudgedX s)-(orgX2 s))
def c43 (s : X86Memory.State) : X86Memory.State := put (c42 s) 7 ((nudgedY s)-(orgY1 s))
def c44 (s : X86Memory.State) : X86Memory.State := put (c43 s) 0 (((nudgedX s)-(orgX2 s)).sshiftRight 23)
def c45 (s : X86Memory.State) : X86Memory.State := put (c44 s) 2 ((s.regs 1)-(orgY1 s))
def m11 (s : X86Memory.State) : Memory := store32 (m10 s) ((s.regs 4-48)) (((nudgedX s)-(orgX2 s)).sshiftRight 23)
def c46 (s : X86Memory.State) : X86Memory.State := {regs:=(c45 s).regs,memory:=m11 s}
def c47 (s : X86Memory.State) : X86Memory.State := put (c46 s) 0 ((nudgedY s)-(orgY1 s))
def c48 (s : X86Memory.State) : X86Memory.State := put (c47 s) 2 (((s.regs 1)-(orgY1 s))-((nudgedY s)-(orgY1 s)))
def c49 (s : X86Memory.State) : X86Memory.State := put (c48 s) 0 (((nudgedY s)-(orgY1 s)).sshiftRight 23)
def c50 (s : X86Memory.State) : X86Memory.State := put (c49 s) 3 ((nudgedX s)-(orgX2 s))
def m12 (s : X86Memory.State) : Memory := store32 (m11 s) ((s.regs 4-44)) (((nudgedY s)-(orgY1 s)).sshiftRight 23)
def c51 (s : X86Memory.State) : X86Memory.State := {regs:=(c50 s).regs,memory:=m12 s}
def c52 (s : X86Memory.State) : X86Memory.State := put (c51 s) 0 ((s.regs 3)-(orgX1 s))
def c53 (s : X86Memory.State) : X86Memory.State := put (c52 s) 3 (((nudgedX s)-(orgX2 s)).sshiftRight 7)
def c54 (s : X86Memory.State) : X86Memory.State := put (c53 s) 0 (((s.regs 3)-(orgX1 s)).sshiftRight 23)
def m13 (s : X86Memory.State) : Memory := store32 (m12 s) ((s.regs 4-40)) (((s.regs 3)-(orgX1 s)).sshiftRight 23)
def c55 (s : X86Memory.State) : X86Memory.State := {regs:=(c54 s).regs,memory:=m13 s}
def c56 (s : X86Memory.State) : X86Memory.State := put (c55 s) 0 ((s.regs 1)-(orgY1 s))
def c57 (s : X86Memory.State) : X86Memory.State := put (c56 s) 3 ((((nudgedX s)-(orgX2 s)).sshiftRight 7) &&& 0xffff)
def c58 (s : X86Memory.State) : X86Memory.State := put (c57 s) 0 (((s.regs 1)-(orgY1 s)).sshiftRight 23)
def m14 (s : X86Memory.State) : Memory := store32 (m13 s) ((s.regs 4-52)) ((((nudgedX s)-(orgX2 s)).sshiftRight 7) &&& 0xffff)
def c59 (s : X86Memory.State) : X86Memory.State := {regs:=(c58 s).regs,memory:=m14 s}
def m15 (s : X86Memory.State) : Memory := store32 (m14 s) ((s.regs 4-36)) (((s.regs 1)-(orgY1 s)).sshiftRight 23)
def c60 (s : X86Memory.State) : X86Memory.State := {regs:=(c59 s).regs,memory:=m15 s}
def result (s : X86Memory.State) : X86Control.State := ⟨c60 s,none,0x2c96c⟩
@[simp] theorem stack_8 (a : Word) : a-(60#32)+(8#32) = a-(52#32) := by simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl
@[simp] theorem stack_12 (a : Word) : a-(60#32)+(12#32) = a-(48#32) := by simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl
@[simp] theorem stack_16 (a : Word) : a-(60#32)+(16#32) = a-(44#32) := by simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl
@[simp] theorem stack_20 (a : Word) : a-(60#32)+(20#32) = a-(40#32) := by simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl
@[simp] theorem stack_24 (a : Word) : a-(60#32)+(24#32) = a-(36#32) := by simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl
@[simp] theorem stack_64 (a : Word) : a-(60#32)+(64#32) = a+(4#32) := by simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl
@[simp] theorem stack_allocate (a : Word) : a-(12#32)+(0xffffffd0#32)=a-(60#32) := by simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl

theorem entry (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix listed [] 19 ⟨s,f,0x2c8a0⟩ ⟨c19 s,some (logical32 (((s.regs 0)-(orgX0 s)) &&& 0x7fffff)),0x2c8df⟩ := by
  apply X86Routine.Prefix.step (middle := ⟨c1 s,f,0x2c8a1⟩) (by simp) (by rfl) (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,logical32,relative8,result,c60,m15,c59,m14,c58,c57,c56,c55,m13,c54,c53,c52,c51,m12,c50,c49,c48,c47,c46,m11,c45,c44,c43,c42,c41,c40,c39,c38,orgX2,c37,m10,c36,m9,c35,c34,m8,c33,c32,m7,c31,orgX1,c30,c29,orgY1,c28,c27,nudgedY,c26,c25,boundaryY,c24,c23,c22,orgY0,c21,nudgedX,c20,c19,boundaryX,c18,m6,c17,c16,c15,c14,m5,c13,orgX0,c12,m4,c11,c10,oldValid,c9,c8,argument,c7,c6,c5,c4,c3,m3,c2,m2,c1,m1])
  apply X86Routine.Prefix.step (middle := ⟨c2 s,f,0x2c8a2⟩) (by simp) (by rfl) (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,logical32,relative8,result,c60,m15,c59,m14,c58,c57,c56,c55,m13,c54,c53,c52,c51,m12,c50,c49,c48,c47,c46,m11,c45,c44,c43,c42,c41,c40,c39,c38,orgX2,c37,m10,c36,m9,c35,c34,m8,c33,c32,m7,c31,orgX1,c30,c29,orgY1,c28,c27,nudgedY,c26,c25,boundaryY,c24,c23,c22,orgY0,c21,nudgedX,c20,c19,boundaryX,c18,m6,c17,c16,c15,c14,m5,c13,orgX0,c12,m4,c11,c10,oldValid,c9,c8,argument,c7,c6,c5,c4,c3,m3,c2,m2,c1,m1])
  apply X86Routine.Prefix.step (middle := ⟨c3 s,f,0x2c8a3⟩) (by simp) (by rfl) (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,logical32,relative8,result,c60,m15,c59,m14,c58,c57,c56,c55,m13,c54,c53,c52,c51,m12,c50,c49,c48,c47,c46,m11,c45,c44,c43,c42,c41,c40,c39,c38,orgX2,c37,m10,c36,m9,c35,c34,m8,c33,c32,m7,c31,orgX1,c30,c29,orgY1,c28,c27,nudgedY,c26,c25,boundaryY,c24,c23,c22,orgY0,c21,nudgedX,c20,c19,boundaryX,c18,m6,c17,c16,c15,c14,m5,c13,orgX0,c12,m4,c11,c10,oldValid,c9,c8,argument,c7,c6,c5,c4,c3,m3,c2,m2,c1,m1])
  apply X86Routine.Prefix.step (middle := ⟨c4 s,none,0x2c8a6⟩) (by simp) (by rfl) (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,logical32,relative8,result,c60,m15,c59,m14,c58,c57,c56,c55,m13,c54,c53,c52,c51,m12,c50,c49,c48,c47,c46,m11,c45,c44,c43,c42,c41,c40,c39,c38,orgX2,c37,m10,c36,m9,c35,c34,m8,c33,c32,m7,c31,orgX1,c30,c29,orgY1,c28,c27,nudgedY,c26,c25,boundaryY,c24,c23,c22,orgY0,c21,nudgedX,c20,c19,boundaryX,c18,m6,c17,c16,c15,c14,m5,c13,orgX0,c12,m4,c11,c10,oldValid,c9,c8,argument,c7,c6,c5,c4,c3,m3,c2,m2,c1,m1])
  apply X86Routine.Prefix.step (middle := ⟨c5 s,none,0x2c8a8⟩) (by simp) (by rfl) (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,logical32,relative8,result,c60,m15,c59,m14,c58,c57,c56,c55,m13,c54,c53,c52,c51,m12,c50,c49,c48,c47,c46,m11,c45,c44,c43,c42,c41,c40,c39,c38,orgX2,c37,m10,c36,m9,c35,c34,m8,c33,c32,m7,c31,orgX1,c30,c29,orgY1,c28,c27,nudgedY,c26,c25,boundaryY,c24,c23,c22,orgY0,c21,nudgedX,c20,c19,boundaryX,c18,m6,c17,c16,c15,c14,m5,c13,orgX0,c12,m4,c11,c10,oldValid,c9,c8,argument,c7,c6,c5,c4,c3,m3,c2,m2,c1,m1])
  apply X86Routine.Prefix.step (middle := ⟨c6 s,none,0x2c8aa⟩) (by simp) (by rfl) (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,logical32,relative8,result,c60,m15,c59,m14,c58,c57,c56,c55,m13,c54,c53,c52,c51,m12,c50,c49,c48,c47,c46,m11,c45,c44,c43,c42,c41,c40,c39,c38,orgX2,c37,m10,c36,m9,c35,c34,m8,c33,c32,m7,c31,orgX1,c30,c29,orgY1,c28,c27,nudgedY,c26,c25,boundaryY,c24,c23,c22,orgY0,c21,nudgedX,c20,c19,boundaryX,c18,m6,c17,c16,c15,c14,m5,c13,orgX0,c12,m4,c11,c10,oldValid,c9,c8,argument,c7,c6,c5,c4,c3,m3,c2,m2,c1,m1])
  apply X86Routine.Prefix.step (middle := ⟨c7 s,none,0x2c8ac⟩) (by simp) (by rfl) (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,logical32,relative8,result,c60,m15,c59,m14,c58,c57,c56,c55,m13,c54,c53,c52,c51,m12,c50,c49,c48,c47,c46,m11,c45,c44,c43,c42,c41,c40,c39,c38,orgX2,c37,m10,c36,m9,c35,c34,m8,c33,c32,m7,c31,orgX1,c30,c29,orgY1,c28,c27,nudgedY,c26,c25,boundaryY,c24,c23,c22,orgY0,c21,nudgedX,c20,c19,boundaryX,c18,m6,c17,c16,c15,c14,m5,c13,orgX0,c12,m4,c11,c10,oldValid,c9,c8,argument,c7,c6,c5,c4,c3,m3,c2,m2,c1,m1])
  apply X86Routine.Prefix.step (middle := ⟨c8 s,none,0x2c8b0⟩) (by simp) (by rfl) (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,logical32,relative8,result,c60,m15,c59,m14,c58,c57,c56,c55,m13,c54,c53,c52,c51,m12,c50,c49,c48,c47,c46,m11,c45,c44,c43,c42,c41,c40,c39,c38,orgX2,c37,m10,c36,m9,c35,c34,m8,c33,c32,m7,c31,orgX1,c30,c29,orgY1,c28,c27,nudgedY,c26,c25,boundaryY,c24,c23,c22,orgY0,c21,nudgedX,c20,c19,boundaryX,c18,m6,c17,c16,c15,c14,m5,c13,orgX0,c12,m4,c11,c10,oldValid,c9,c8,argument,c7,c6,c5,c4,c3,m3,c2,m2,c1,m1])
  apply X86Routine.Prefix.step (middle := ⟨c9 s,none,0x2c8b5⟩) (by simp) (by rfl) (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,logical32,relative8,result,c60,m15,c59,m14,c58,c57,c56,c55,m13,c54,c53,c52,c51,m12,c50,c49,c48,c47,c46,m11,c45,c44,c43,c42,c41,c40,c39,c38,orgX2,c37,m10,c36,m9,c35,c34,m8,c33,c32,m7,c31,orgX1,c30,c29,orgY1,c28,c27,nudgedY,c26,c25,boundaryY,c24,c23,c22,orgY0,c21,nudgedX,c20,c19,boundaryX,c18,m6,c17,c16,c15,c14,m5,c13,orgX0,c12,m4,c11,c10,oldValid,c9,c8,argument,c7,c6,c5,c4,c3,m3,c2,m2,c1,m1])
  apply X86Routine.Prefix.step (middle := ⟨c10 s,none,0x2c8bb⟩) (by simp) (by rfl) (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,logical32,relative8,result,c60,m15,c59,m14,c58,c57,c56,c55,m13,c54,c53,c52,c51,m12,c50,c49,c48,c47,c46,m11,c45,c44,c43,c42,c41,c40,c39,c38,orgX2,c37,m10,c36,m9,c35,c34,m8,c33,c32,m7,c31,orgX1,c30,c29,orgY1,c28,c27,nudgedY,c26,c25,boundaryY,c24,c23,c22,orgY0,c21,nudgedX,c20,c19,boundaryX,c18,m6,c17,c16,c15,c14,m5,c13,orgX0,c12,m4,c11,c10,oldValid,c9,c8,argument,c7,c6,c5,c4,c3,m3,c2,m2,c1,m1])
  apply X86Routine.Prefix.step (middle := ⟨c11 s,some {(logical32 ((argument s) &&& 0x4)) with carry:=some false},0x2c8be⟩) (by simp) (by rfl) (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,logical32,relative8,result,c60,m15,c59,m14,c58,c57,c56,c55,m13,c54,c53,c52,c51,m12,c50,c49,c48,c47,c46,m11,c45,c44,c43,c42,c41,c40,c39,c38,orgX2,c37,m10,c36,m9,c35,c34,m8,c33,c32,m7,c31,orgX1,c30,c29,orgY1,c28,c27,nudgedY,c26,c25,boundaryY,c24,c23,c22,orgY0,c21,nudgedX,c20,c19,boundaryX,c18,m6,c17,c16,c15,c14,m5,c13,orgX0,c12,m4,c11,c10,oldValid,c9,c8,argument,c7,c6,c5,c4,c3,m3,c2,m2,c1,m1])
  apply X86Routine.Prefix.step (middle := ⟨c12 s,some {(logical32 ((argument s) &&& 0x4)) with carry:=some false},0x2c8c4⟩) (by simp) (by rfl) (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,logical32,relative8,result,c60,m15,c59,m14,c58,c57,c56,c55,m13,c54,c53,c52,c51,m12,c50,c49,c48,c47,c46,m11,c45,c44,c43,c42,c41,c40,c39,c38,orgX2,c37,m10,c36,m9,c35,c34,m8,c33,c32,m7,c31,orgX1,c30,c29,orgY1,c28,c27,nudgedY,c26,c25,boundaryY,c24,c23,c22,orgY0,c21,nudgedX,c20,c19,boundaryX,c18,m6,c17,c16,c15,c14,m5,c13,orgX0,c12,m4,c11,c10,oldValid,c9,c8,argument,c7,c6,c5,c4,c3,m3,c2,m2,c1,m1])
  apply X86Routine.Prefix.step (middle := ⟨c13 s,some {(logical32 ((argument s) &&& 0x4)) with carry:=some false},0x2c8ca⟩) (by simp) (by rfl) (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,logical32,relative8,result,c60,m15,c59,m14,c58,c57,c56,c55,m13,c54,c53,c52,c51,m12,c50,c49,c48,c47,c46,m11,c45,c44,c43,c42,c41,c40,c39,c38,orgX2,c37,m10,c36,m9,c35,c34,m8,c33,c32,m7,c31,orgX1,c30,c29,orgY1,c28,c27,nudgedY,c26,c25,boundaryY,c24,c23,c22,orgY0,c21,nudgedX,c20,c19,boundaryX,c18,m6,c17,c16,c15,c14,m5,c13,orgX0,c12,m4,c11,c10,oldValid,c9,c8,argument,c7,c6,c5,c4,c3,m3,c2,m2,c1,m1])
  apply X86Routine.Prefix.step (middle := ⟨c14 s,some {(logical32 ((argument s) &&& 0x4)) with carry:=some false},0x2c8cf⟩) (by simp) (by rfl) (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,logical32,relative8,result,c60,m15,c59,m14,c58,c57,c56,c55,m13,c54,c53,c52,c51,m12,c50,c49,c48,c47,c46,m11,c45,c44,c43,c42,c41,c40,c39,c38,orgX2,c37,m10,c36,m9,c35,c34,m8,c33,c32,m7,c31,orgX1,c30,c29,orgY1,c28,c27,nudgedY,c26,c25,boundaryY,c24,c23,c22,orgY0,c21,nudgedX,c20,c19,boundaryX,c18,m6,c17,c16,c15,c14,m5,c13,orgX0,c12,m4,c11,c10,oldValid,c9,c8,argument,c7,c6,c5,c4,c3,m3,c2,m2,c1,m1])
  apply X86Routine.Prefix.step (middle := ⟨c15 s,some {(logical32 ((argument s) &&& 0x4)) with carry:=some false},0x2c8d1⟩) (by simp) (by rfl) (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,logical32,relative8,result,c60,m15,c59,m14,c58,c57,c56,c55,m13,c54,c53,c52,c51,m12,c50,c49,c48,c47,c46,m11,c45,c44,c43,c42,c41,c40,c39,c38,orgX2,c37,m10,c36,m9,c35,c34,m8,c33,c32,m7,c31,orgX1,c30,c29,orgY1,c28,c27,nudgedY,c26,c25,boundaryY,c24,c23,c22,orgY0,c21,nudgedX,c20,c19,boundaryX,c18,m6,c17,c16,c15,c14,m5,c13,orgX0,c12,m4,c11,c10,oldValid,c9,c8,argument,c7,c6,c5,c4,c3,m3,c2,m2,c1,m1])
  apply X86Routine.Prefix.step (middle := ⟨c16 s,none,0x2c8d2⟩) (by simp) (by rfl) (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,logical32,relative8,result,c60,m15,c59,m14,c58,c57,c56,c55,m13,c54,c53,c52,c51,m12,c50,c49,c48,c47,c46,m11,c45,c44,c43,c42,c41,c40,c39,c38,orgX2,c37,m10,c36,m9,c35,c34,m8,c33,c32,m7,c31,orgX1,c30,c29,orgY1,c28,c27,nudgedY,c26,c25,boundaryY,c24,c23,c22,orgY0,c21,nudgedX,c20,c19,boundaryX,c18,m6,c17,c16,c15,c14,m5,c13,orgX0,c12,m4,c11,c10,oldValid,c9,c8,argument,c7,c6,c5,c4,c3,m3,c2,m2,c1,m1])
  apply X86Routine.Prefix.step (middle := ⟨c17 s,none,0x2c8d4⟩) (by simp) (by rfl) (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,logical32,relative8,result,c60,m15,c59,m14,c58,c57,c56,c55,m13,c54,c53,c52,c51,m12,c50,c49,c48,c47,c46,m11,c45,c44,c43,c42,c41,c40,c39,c38,orgX2,c37,m10,c36,m9,c35,c34,m8,c33,c32,m7,c31,orgX1,c30,c29,orgY1,c28,c27,nudgedY,c26,c25,boundaryY,c24,c23,c22,orgY0,c21,nudgedX,c20,c19,boundaryX,c18,m6,c17,c16,c15,c14,m5,c13,orgX0,c12,m4,c11,c10,oldValid,c9,c8,argument,c7,c6,c5,c4,c3,m3,c2,m2,c1,m1])
  apply X86Routine.Prefix.step (middle := ⟨c18 s,none,0x2c8da⟩) (by simp) (by rfl) (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,logical32,relative8,result,c60,m15,c59,m14,c58,c57,c56,c55,m13,c54,c53,c52,c51,m12,c50,c49,c48,c47,c46,m11,c45,c44,c43,c42,c41,c40,c39,c38,orgX2,c37,m10,c36,m9,c35,c34,m8,c33,c32,m7,c31,orgX1,c30,c29,orgY1,c28,c27,nudgedY,c26,c25,boundaryY,c24,c23,c22,orgY0,c21,nudgedX,c20,c19,boundaryX,c18,m6,c17,c16,c15,c14,m5,c13,orgX0,c12,m4,c11,c10,oldValid,c9,c8,argument,c7,c6,c5,c4,c3,m3,c2,m2,c1,m1])
  apply X86Routine.Prefix.step (middle := ⟨c19 s,some (logical32 (((s.regs 0)-(orgX0 s)) &&& 0x7fffff)),0x2c8df⟩) (by simp) (by rfl) (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,logical32,relative8,result,c60,m15,c59,m14,c58,c57,c56,c55,m13,c54,c53,c52,c51,m12,c50,c49,c48,c47,c46,m11,c45,c44,c43,c42,c41,c40,c39,c38,orgX2,c37,m10,c36,m9,c35,c34,m8,c33,c32,m7,c31,orgX1,c30,c29,orgY1,c28,c27,nudgedY,c26,c25,boundaryY,c24,c23,c22,orgY0,c21,nudgedX,c20,c19,boundaryX,c18,m6,c17,c16,c15,c14,m5,c13,orgX0,c12,m4,c11,c10,oldValid,c9,c8,argument,c7,c6,c5,c4,c3,m3,c2,m2,c1,m1])
  exact X86Routine.Prefix.nil _

theorem middle (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix listed [] 4 ⟨c21 s,(if boundaryX s then none else some (logical32 (((s.regs 0)-(orgX0 s)) &&& 0x7fffff))),0x2c8e7⟩ ⟨c25 s,some (logical32 (((s.regs 2)-(orgY0 s)) &&& 0x7fffff)),0x2c8f6⟩ := by
  apply X86Routine.Prefix.step (middle := ⟨c22 s,(if boundaryX s then none else some (logical32 (((s.regs 0)-(orgX0 s)) &&& 0x7fffff))),0x2c8ed⟩) (by simp) (by rfl) (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,logical32,relative8,result,c60,m15,c59,m14,c58,c57,c56,c55,m13,c54,c53,c52,c51,m12,c50,c49,c48,c47,c46,m11,c45,c44,c43,c42,c41,c40,c39,c38,orgX2,c37,m10,c36,m9,c35,c34,m8,c33,c32,m7,c31,orgX1,c30,c29,orgY1,c28,c27,nudgedY,c26,c25,boundaryY,c24,c23,c22,orgY0,c21,nudgedX,c20,c19,boundaryX,c18,m6,c17,c16,c15,c14,m5,c13,orgX0,c12,m4,c11,c10,oldValid,c9,c8,argument,c7,c6,c5,c4,c3,m3,c2,m2,c1,m1])
  apply X86Routine.Prefix.step (middle := ⟨c23 s,(if boundaryX s then none else some (logical32 (((s.regs 0)-(orgX0 s)) &&& 0x7fffff))),0x2c8ef⟩) (by simp) (by rfl) (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,logical32,relative8,result,c60,m15,c59,m14,c58,c57,c56,c55,m13,c54,c53,c52,c51,m12,c50,c49,c48,c47,c46,m11,c45,c44,c43,c42,c41,c40,c39,c38,orgX2,c37,m10,c36,m9,c35,c34,m8,c33,c32,m7,c31,orgX1,c30,c29,orgY1,c28,c27,nudgedY,c26,c25,boundaryY,c24,c23,c22,orgY0,c21,nudgedX,c20,c19,boundaryX,c18,m6,c17,c16,c15,c14,m5,c13,orgX0,c12,m4,c11,c10,oldValid,c9,c8,argument,c7,c6,c5,c4,c3,m3,c2,m2,c1,m1])
  apply X86Routine.Prefix.step (middle := ⟨c24 s,none,0x2c8f1⟩) (by simp) (by rfl) (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,logical32,relative8,result,c60,m15,c59,m14,c58,c57,c56,c55,m13,c54,c53,c52,c51,m12,c50,c49,c48,c47,c46,m11,c45,c44,c43,c42,c41,c40,c39,c38,orgX2,c37,m10,c36,m9,c35,c34,m8,c33,c32,m7,c31,orgX1,c30,c29,orgY1,c28,c27,nudgedY,c26,c25,boundaryY,c24,c23,c22,orgY0,c21,nudgedX,c20,c19,boundaryX,c18,m6,c17,c16,c15,c14,m5,c13,orgX0,c12,m4,c11,c10,oldValid,c9,c8,argument,c7,c6,c5,c4,c3,m3,c2,m2,c1,m1])
  apply X86Routine.Prefix.step (middle := ⟨c25 s,some (logical32 (((s.regs 2)-(orgY0 s)) &&& 0x7fffff)),0x2c8f6⟩) (by simp) (by rfl) (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,logical32,relative8,result,c60,m15,c59,m14,c58,c57,c56,c55,m13,c54,c53,c52,c51,m12,c50,c49,c48,c47,c46,m11,c45,c44,c43,c42,c41,c40,c39,c38,orgX2,c37,m10,c36,m9,c35,c34,m8,c33,c32,m7,c31,orgX1,c30,c29,orgY1,c28,c27,nudgedY,c26,c25,boundaryY,c24,c23,c22,orgY0,c21,nudgedX,c20,c19,boundaryX,c18,m6,c17,c16,c15,c14,m5,c13,orgX0,c12,m4,c11,c10,oldValid,c9,c8,argument,c7,c6,c5,c4,c3,m3,c2,m2,c1,m1])
  exact X86Routine.Prefix.nil _

theorem finish (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix listed [] 33 ⟨c27 s,(if boundaryY s then none else some (logical32 (((s.regs 2)-(orgY0 s)) &&& 0x7fffff))),0x2c8fe⟩ (result s) := by
  apply X86Routine.Prefix.step (middle := ⟨c28 s,(if boundaryY s then none else some (logical32 (((s.regs 2)-(orgY0 s)) &&& 0x7fffff))),0x2c900⟩) (by simp) (by rfl) (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,logical32,relative8,result,c60,m15,c59,m14,c58,c57,c56,c55,m13,c54,c53,c52,c51,m12,c50,c49,c48,c47,c46,m11,c45,c44,c43,c42,c41,c40,c39,c38,orgX2,c37,m10,c36,m9,c35,c34,m8,c33,c32,m7,c31,orgX1,c30,c29,orgY1,c28,c27,nudgedY,c26,c25,boundaryY,c24,c23,c22,orgY0,c21,nudgedX,c20,c19,boundaryX,c18,m6,c17,c16,c15,c14,m5,c13,orgX0,c12,m4,c11,c10,oldValid,c9,c8,argument,c7,c6,c5,c4,c3,m3,c2,m2,c1,m1])
  apply X86Routine.Prefix.step (middle := ⟨c29 s,(if boundaryY s then none else some (logical32 (((s.regs 2)-(orgY0 s)) &&& 0x7fffff))),0x2c906⟩) (by simp) (by rfl) (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,logical32,relative8,result,c60,m15,c59,m14,c58,c57,c56,c55,m13,c54,c53,c52,c51,m12,c50,c49,c48,c47,c46,m11,c45,c44,c43,c42,c41,c40,c39,c38,orgX2,c37,m10,c36,m9,c35,c34,m8,c33,c32,m7,c31,orgX1,c30,c29,orgY1,c28,c27,nudgedY,c26,c25,boundaryY,c24,c23,c22,orgY0,c21,nudgedX,c20,c19,boundaryX,c18,m6,c17,c16,c15,c14,m5,c13,orgX0,c12,m4,c11,c10,oldValid,c9,c8,argument,c7,c6,c5,c4,c3,m3,c2,m2,c1,m1])
  apply X86Routine.Prefix.step (middle := ⟨c30 s,none,0x2c908⟩) (by simp) (by rfl) (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,logical32,relative8,result,c60,m15,c59,m14,c58,c57,c56,c55,m13,c54,c53,c52,c51,m12,c50,c49,c48,c47,c46,m11,c45,c44,c43,c42,c41,c40,c39,c38,orgX2,c37,m10,c36,m9,c35,c34,m8,c33,c32,m7,c31,orgX1,c30,c29,orgY1,c28,c27,nudgedY,c26,c25,boundaryY,c24,c23,c22,orgY0,c21,nudgedX,c20,c19,boundaryX,c18,m6,c17,c16,c15,c14,m5,c13,orgX0,c12,m4,c11,c10,oldValid,c9,c8,argument,c7,c6,c5,c4,c3,m3,c2,m2,c1,m1])
  apply X86Routine.Prefix.step (middle := ⟨c31 s,none,0x2c90e⟩) (by simp) (by rfl) (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,logical32,relative8,result,c60,m15,c59,m14,c58,c57,c56,c55,m13,c54,c53,c52,c51,m12,c50,c49,c48,c47,c46,m11,c45,c44,c43,c42,c41,c40,c39,c38,orgX2,c37,m10,c36,m9,c35,c34,m8,c33,c32,m7,c31,orgX1,c30,c29,orgY1,c28,c27,nudgedY,c26,c25,boundaryY,c24,c23,c22,orgY0,c21,nudgedX,c20,c19,boundaryX,c18,m6,c17,c16,c15,c14,m5,c13,orgX0,c12,m4,c11,c10,oldValid,c9,c8,argument,c7,c6,c5,c4,c3,m3,c2,m2,c1,m1])
  apply X86Routine.Prefix.step (middle := ⟨c32 s,none,0x2c913⟩) (by simp) (by rfl) (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,logical32,relative8,result,c60,m15,c59,m14,c58,c57,c56,c55,m13,c54,c53,c52,c51,m12,c50,c49,c48,c47,c46,m11,c45,c44,c43,c42,c41,c40,c39,c38,orgX2,c37,m10,c36,m9,c35,c34,m8,c33,c32,m7,c31,orgX1,c30,c29,orgY1,c28,c27,nudgedY,c26,c25,boundaryY,c24,c23,c22,orgY0,c21,nudgedX,c20,c19,boundaryX,c18,m6,c17,c16,c15,c14,m5,c13,orgX0,c12,m4,c11,c10,oldValid,c9,c8,argument,c7,c6,c5,c4,c3,m3,c2,m2,c1,m1])
  apply X86Routine.Prefix.step (middle := ⟨c33 s,none,0x2c915⟩) (by simp) (by rfl) (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,logical32,relative8,result,c60,m15,c59,m14,c58,c57,c56,c55,m13,c54,c53,c52,c51,m12,c50,c49,c48,c47,c46,m11,c45,c44,c43,c42,c41,c40,c39,c38,orgX2,c37,m10,c36,m9,c35,c34,m8,c33,c32,m7,c31,orgX1,c30,c29,orgY1,c28,c27,nudgedY,c26,c25,boundaryY,c24,c23,c22,orgY0,c21,nudgedX,c20,c19,boundaryX,c18,m6,c17,c16,c15,c14,m5,c13,orgX0,c12,m4,c11,c10,oldValid,c9,c8,argument,c7,c6,c5,c4,c3,m3,c2,m2,c1,m1])
  apply X86Routine.Prefix.step (middle := ⟨c34 s,none,0x2c91b⟩) (by simp) (by rfl) (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,logical32,relative8,result,c60,m15,c59,m14,c58,c57,c56,c55,m13,c54,c53,c52,c51,m12,c50,c49,c48,c47,c46,m11,c45,c44,c43,c42,c41,c40,c39,c38,orgX2,c37,m10,c36,m9,c35,c34,m8,c33,c32,m7,c31,orgX1,c30,c29,orgY1,c28,c27,nudgedY,c26,c25,boundaryY,c24,c23,c22,orgY0,c21,nudgedX,c20,c19,boundaryX,c18,m6,c17,c16,c15,c14,m5,c13,orgX0,c12,m4,c11,c10,oldValid,c9,c8,argument,c7,c6,c5,c4,c3,m3,c2,m2,c1,m1])
  apply X86Routine.Prefix.step (middle := ⟨c35 s,none,0x2c91d⟩) (by simp) (by rfl) (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,logical32,relative8,result,c60,m15,c59,m14,c58,c57,c56,c55,m13,c54,c53,c52,c51,m12,c50,c49,c48,c47,c46,m11,c45,c44,c43,c42,c41,c40,c39,c38,orgX2,c37,m10,c36,m9,c35,c34,m8,c33,c32,m7,c31,orgX1,c30,c29,orgY1,c28,c27,nudgedY,c26,c25,boundaryY,c24,c23,c22,orgY0,c21,nudgedX,c20,c19,boundaryX,c18,m6,c17,c16,c15,c14,m5,c13,orgX0,c12,m4,c11,c10,oldValid,c9,c8,argument,c7,c6,c5,c4,c3,m3,c2,m2,c1,m1])
  apply X86Routine.Prefix.step (middle := ⟨c36 s,none,0x2c923⟩) (by simp) (by rfl) (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,logical32,relative8,result,c60,m15,c59,m14,c58,c57,c56,c55,m13,c54,c53,c52,c51,m12,c50,c49,c48,c47,c46,m11,c45,c44,c43,c42,c41,c40,c39,c38,orgX2,c37,m10,c36,m9,c35,c34,m8,c33,c32,m7,c31,orgX1,c30,c29,orgY1,c28,c27,nudgedY,c26,c25,boundaryY,c24,c23,c22,orgY0,c21,nudgedX,c20,c19,boundaryX,c18,m6,c17,c16,c15,c14,m5,c13,orgX0,c12,m4,c11,c10,oldValid,c9,c8,argument,c7,c6,c5,c4,c3,m3,c2,m2,c1,m1])
  apply X86Routine.Prefix.step (middle := ⟨c37 s,none,0x2c928⟩) (by simp) (by rfl) (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,logical32,relative8,result,c60,m15,c59,m14,c58,c57,c56,c55,m13,c54,c53,c52,c51,m12,c50,c49,c48,c47,c46,m11,c45,c44,c43,c42,c41,c40,c39,c38,orgX2,c37,m10,c36,m9,c35,c34,m8,c33,c32,m7,c31,orgX1,c30,c29,orgY1,c28,c27,nudgedY,c26,c25,boundaryY,c24,c23,c22,orgY0,c21,nudgedX,c20,c19,boundaryX,c18,m6,c17,c16,c15,c14,m5,c13,orgX0,c12,m4,c11,c10,oldValid,c9,c8,argument,c7,c6,c5,c4,c3,m3,c2,m2,c1,m1])
  apply X86Routine.Prefix.step (middle := ⟨c38 s,none,0x2c92d⟩) (by simp) (by rfl) (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,logical32,relative8,result,c60,m15,c59,m14,c58,c57,c56,c55,m13,c54,c53,c52,c51,m12,c50,c49,c48,c47,c46,m11,c45,c44,c43,c42,c41,c40,c39,c38,orgX2,c37,m10,c36,m9,c35,c34,m8,c33,c32,m7,c31,orgX1,c30,c29,orgY1,c28,c27,nudgedY,c26,c25,boundaryY,c24,c23,c22,orgY0,c21,nudgedX,c20,c19,boundaryX,c18,m6,c17,c16,c15,c14,m5,c13,orgX0,c12,m4,c11,c10,oldValid,c9,c8,argument,c7,c6,c5,c4,c3,m3,c2,m2,c1,m1])
  apply X86Routine.Prefix.step (middle := ⟨c39 s,none,0x2c92f⟩) (by simp) (by rfl) (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,logical32,relative8,result,c60,m15,c59,m14,c58,c57,c56,c55,m13,c54,c53,c52,c51,m12,c50,c49,c48,c47,c46,m11,c45,c44,c43,c42,c41,c40,c39,c38,orgX2,c37,m10,c36,m9,c35,c34,m8,c33,c32,m7,c31,orgX1,c30,c29,orgY1,c28,c27,nudgedY,c26,c25,boundaryY,c24,c23,c22,orgY0,c21,nudgedX,c20,c19,boundaryX,c18,m6,c17,c16,c15,c14,m5,c13,orgX0,c12,m4,c11,c10,oldValid,c9,c8,argument,c7,c6,c5,c4,c3,m3,c2,m2,c1,m1])
  apply X86Routine.Prefix.step (middle := ⟨c40 s,none,0x2c931⟩) (by simp) (by rfl) (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,logical32,relative8,result,c60,m15,c59,m14,c58,c57,c56,c55,m13,c54,c53,c52,c51,m12,c50,c49,c48,c47,c46,m11,c45,c44,c43,c42,c41,c40,c39,c38,orgX2,c37,m10,c36,m9,c35,c34,m8,c33,c32,m7,c31,orgX1,c30,c29,orgY1,c28,c27,nudgedY,c26,c25,boundaryY,c24,c23,c22,orgY0,c21,nudgedX,c20,c19,boundaryX,c18,m6,c17,c16,c15,c14,m5,c13,orgX0,c12,m4,c11,c10,oldValid,c9,c8,argument,c7,c6,c5,c4,c3,m3,c2,m2,c1,m1])
  apply X86Routine.Prefix.step (middle := ⟨c41 s,none,0x2c933⟩) (by simp) (by rfl) (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,logical32,relative8,result,c60,m15,c59,m14,c58,c57,c56,c55,m13,c54,c53,c52,c51,m12,c50,c49,c48,c47,c46,m11,c45,c44,c43,c42,c41,c40,c39,c38,orgX2,c37,m10,c36,m9,c35,c34,m8,c33,c32,m7,c31,orgX1,c30,c29,orgY1,c28,c27,nudgedY,c26,c25,boundaryY,c24,c23,c22,orgY0,c21,nudgedX,c20,c19,boundaryX,c18,m6,c17,c16,c15,c14,m5,c13,orgX0,c12,m4,c11,c10,oldValid,c9,c8,argument,c7,c6,c5,c4,c3,m3,c2,m2,c1,m1])
  apply X86Routine.Prefix.step (middle := ⟨c42 s,none,0x2c935⟩) (by simp) (by rfl) (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,logical32,relative8,result,c60,m15,c59,m14,c58,c57,c56,c55,m13,c54,c53,c52,c51,m12,c50,c49,c48,c47,c46,m11,c45,c44,c43,c42,c41,c40,c39,c38,orgX2,c37,m10,c36,m9,c35,c34,m8,c33,c32,m7,c31,orgX1,c30,c29,orgY1,c28,c27,nudgedY,c26,c25,boundaryY,c24,c23,c22,orgY0,c21,nudgedX,c20,c19,boundaryX,c18,m6,c17,c16,c15,c14,m5,c13,orgX0,c12,m4,c11,c10,oldValid,c9,c8,argument,c7,c6,c5,c4,c3,m3,c2,m2,c1,m1])
  apply X86Routine.Prefix.step (middle := ⟨c43 s,none,0x2c937⟩) (by simp) (by rfl) (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,logical32,relative8,result,c60,m15,c59,m14,c58,c57,c56,c55,m13,c54,c53,c52,c51,m12,c50,c49,c48,c47,c46,m11,c45,c44,c43,c42,c41,c40,c39,c38,orgX2,c37,m10,c36,m9,c35,c34,m8,c33,c32,m7,c31,orgX1,c30,c29,orgY1,c28,c27,nudgedY,c26,c25,boundaryY,c24,c23,c22,orgY0,c21,nudgedX,c20,c19,boundaryX,c18,m6,c17,c16,c15,c14,m5,c13,orgX0,c12,m4,c11,c10,oldValid,c9,c8,argument,c7,c6,c5,c4,c3,m3,c2,m2,c1,m1])
  apply X86Routine.Prefix.step (middle := ⟨c44 s,none,0x2c93a⟩) (by simp) (by rfl) (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,logical32,relative8,result,c60,m15,c59,m14,c58,c57,c56,c55,m13,c54,c53,c52,c51,m12,c50,c49,c48,c47,c46,m11,c45,c44,c43,c42,c41,c40,c39,c38,orgX2,c37,m10,c36,m9,c35,c34,m8,c33,c32,m7,c31,orgX1,c30,c29,orgY1,c28,c27,nudgedY,c26,c25,boundaryY,c24,c23,c22,orgY0,c21,nudgedX,c20,c19,boundaryX,c18,m6,c17,c16,c15,c14,m5,c13,orgX0,c12,m4,c11,c10,oldValid,c9,c8,argument,c7,c6,c5,c4,c3,m3,c2,m2,c1,m1])
  apply X86Routine.Prefix.step (middle := ⟨c45 s,none,0x2c93c⟩) (by simp) (by rfl) (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,logical32,relative8,result,c60,m15,c59,m14,c58,c57,c56,c55,m13,c54,c53,c52,c51,m12,c50,c49,c48,c47,c46,m11,c45,c44,c43,c42,c41,c40,c39,c38,orgX2,c37,m10,c36,m9,c35,c34,m8,c33,c32,m7,c31,orgX1,c30,c29,orgY1,c28,c27,nudgedY,c26,c25,boundaryY,c24,c23,c22,orgY0,c21,nudgedX,c20,c19,boundaryX,c18,m6,c17,c16,c15,c14,m5,c13,orgX0,c12,m4,c11,c10,oldValid,c9,c8,argument,c7,c6,c5,c4,c3,m3,c2,m2,c1,m1])
  apply X86Routine.Prefix.step (middle := ⟨c46 s,none,0x2c940⟩) (by simp) (by rfl) (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,logical32,relative8,result,c60,m15,c59,m14,c58,c57,c56,c55,m13,c54,c53,c52,c51,m12,c50,c49,c48,c47,c46,m11,c45,c44,c43,c42,c41,c40,c39,c38,orgX2,c37,m10,c36,m9,c35,c34,m8,c33,c32,m7,c31,orgX1,c30,c29,orgY1,c28,c27,nudgedY,c26,c25,boundaryY,c24,c23,c22,orgY0,c21,nudgedX,c20,c19,boundaryX,c18,m6,c17,c16,c15,c14,m5,c13,orgX0,c12,m4,c11,c10,oldValid,c9,c8,argument,c7,c6,c5,c4,c3,m3,c2,m2,c1,m1])
  apply X86Routine.Prefix.step (middle := ⟨c47 s,none,0x2c942⟩) (by simp) (by rfl) (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,logical32,relative8,result,c60,m15,c59,m14,c58,c57,c56,c55,m13,c54,c53,c52,c51,m12,c50,c49,c48,c47,c46,m11,c45,c44,c43,c42,c41,c40,c39,c38,orgX2,c37,m10,c36,m9,c35,c34,m8,c33,c32,m7,c31,orgX1,c30,c29,orgY1,c28,c27,nudgedY,c26,c25,boundaryY,c24,c23,c22,orgY0,c21,nudgedX,c20,c19,boundaryX,c18,m6,c17,c16,c15,c14,m5,c13,orgX0,c12,m4,c11,c10,oldValid,c9,c8,argument,c7,c6,c5,c4,c3,m3,c2,m2,c1,m1])
  apply X86Routine.Prefix.step (middle := ⟨c48 s,none,0x2c944⟩) (by simp) (by rfl) (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,logical32,relative8,result,c60,m15,c59,m14,c58,c57,c56,c55,m13,c54,c53,c52,c51,m12,c50,c49,c48,c47,c46,m11,c45,c44,c43,c42,c41,c40,c39,c38,orgX2,c37,m10,c36,m9,c35,c34,m8,c33,c32,m7,c31,orgX1,c30,c29,orgY1,c28,c27,nudgedY,c26,c25,boundaryY,c24,c23,c22,orgY0,c21,nudgedX,c20,c19,boundaryX,c18,m6,c17,c16,c15,c14,m5,c13,orgX0,c12,m4,c11,c10,oldValid,c9,c8,argument,c7,c6,c5,c4,c3,m3,c2,m2,c1,m1])
  apply X86Routine.Prefix.step (middle := ⟨c49 s,none,0x2c947⟩) (by simp) (by rfl) (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,logical32,relative8,result,c60,m15,c59,m14,c58,c57,c56,c55,m13,c54,c53,c52,c51,m12,c50,c49,c48,c47,c46,m11,c45,c44,c43,c42,c41,c40,c39,c38,orgX2,c37,m10,c36,m9,c35,c34,m8,c33,c32,m7,c31,orgX1,c30,c29,orgY1,c28,c27,nudgedY,c26,c25,boundaryY,c24,c23,c22,orgY0,c21,nudgedX,c20,c19,boundaryX,c18,m6,c17,c16,c15,c14,m5,c13,orgX0,c12,m4,c11,c10,oldValid,c9,c8,argument,c7,c6,c5,c4,c3,m3,c2,m2,c1,m1])
  apply X86Routine.Prefix.step (middle := ⟨c50 s,none,0x2c949⟩) (by simp) (by rfl) (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,logical32,relative8,result,c60,m15,c59,m14,c58,c57,c56,c55,m13,c54,c53,c52,c51,m12,c50,c49,c48,c47,c46,m11,c45,c44,c43,c42,c41,c40,c39,c38,orgX2,c37,m10,c36,m9,c35,c34,m8,c33,c32,m7,c31,orgX1,c30,c29,orgY1,c28,c27,nudgedY,c26,c25,boundaryY,c24,c23,c22,orgY0,c21,nudgedX,c20,c19,boundaryX,c18,m6,c17,c16,c15,c14,m5,c13,orgX0,c12,m4,c11,c10,oldValid,c9,c8,argument,c7,c6,c5,c4,c3,m3,c2,m2,c1,m1])
  apply X86Routine.Prefix.step (middle := ⟨c51 s,none,0x2c94d⟩) (by simp) (by rfl) (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,logical32,relative8,result,c60,m15,c59,m14,c58,c57,c56,c55,m13,c54,c53,c52,c51,m12,c50,c49,c48,c47,c46,m11,c45,c44,c43,c42,c41,c40,c39,c38,orgX2,c37,m10,c36,m9,c35,c34,m8,c33,c32,m7,c31,orgX1,c30,c29,orgY1,c28,c27,nudgedY,c26,c25,boundaryY,c24,c23,c22,orgY0,c21,nudgedX,c20,c19,boundaryX,c18,m6,c17,c16,c15,c14,m5,c13,orgX0,c12,m4,c11,c10,oldValid,c9,c8,argument,c7,c6,c5,c4,c3,m3,c2,m2,c1,m1])
  apply X86Routine.Prefix.step (middle := ⟨c52 s,none,0x2c94f⟩) (by simp) (by rfl) (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,logical32,relative8,result,c60,m15,c59,m14,c58,c57,c56,c55,m13,c54,c53,c52,c51,m12,c50,c49,c48,c47,c46,m11,c45,c44,c43,c42,c41,c40,c39,c38,orgX2,c37,m10,c36,m9,c35,c34,m8,c33,c32,m7,c31,orgX1,c30,c29,orgY1,c28,c27,nudgedY,c26,c25,boundaryY,c24,c23,c22,orgY0,c21,nudgedX,c20,c19,boundaryX,c18,m6,c17,c16,c15,c14,m5,c13,orgX0,c12,m4,c11,c10,oldValid,c9,c8,argument,c7,c6,c5,c4,c3,m3,c2,m2,c1,m1])
  apply X86Routine.Prefix.step (middle := ⟨c53 s,none,0x2c952⟩) (by simp) (by rfl) (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,logical32,relative8,result,c60,m15,c59,m14,c58,c57,c56,c55,m13,c54,c53,c52,c51,m12,c50,c49,c48,c47,c46,m11,c45,c44,c43,c42,c41,c40,c39,c38,orgX2,c37,m10,c36,m9,c35,c34,m8,c33,c32,m7,c31,orgX1,c30,c29,orgY1,c28,c27,nudgedY,c26,c25,boundaryY,c24,c23,c22,orgY0,c21,nudgedX,c20,c19,boundaryX,c18,m6,c17,c16,c15,c14,m5,c13,orgX0,c12,m4,c11,c10,oldValid,c9,c8,argument,c7,c6,c5,c4,c3,m3,c2,m2,c1,m1])
  apply X86Routine.Prefix.step (middle := ⟨c54 s,none,0x2c955⟩) (by simp) (by rfl) (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,logical32,relative8,result,c60,m15,c59,m14,c58,c57,c56,c55,m13,c54,c53,c52,c51,m12,c50,c49,c48,c47,c46,m11,c45,c44,c43,c42,c41,c40,c39,c38,orgX2,c37,m10,c36,m9,c35,c34,m8,c33,c32,m7,c31,orgX1,c30,c29,orgY1,c28,c27,nudgedY,c26,c25,boundaryY,c24,c23,c22,orgY0,c21,nudgedX,c20,c19,boundaryX,c18,m6,c17,c16,c15,c14,m5,c13,orgX0,c12,m4,c11,c10,oldValid,c9,c8,argument,c7,c6,c5,c4,c3,m3,c2,m2,c1,m1])
  apply X86Routine.Prefix.step (middle := ⟨c55 s,none,0x2c959⟩) (by simp) (by rfl) (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,logical32,relative8,result,c60,m15,c59,m14,c58,c57,c56,c55,m13,c54,c53,c52,c51,m12,c50,c49,c48,c47,c46,m11,c45,c44,c43,c42,c41,c40,c39,c38,orgX2,c37,m10,c36,m9,c35,c34,m8,c33,c32,m7,c31,orgX1,c30,c29,orgY1,c28,c27,nudgedY,c26,c25,boundaryY,c24,c23,c22,orgY0,c21,nudgedX,c20,c19,boundaryX,c18,m6,c17,c16,c15,c14,m5,c13,orgX0,c12,m4,c11,c10,oldValid,c9,c8,argument,c7,c6,c5,c4,c3,m3,c2,m2,c1,m1])
  apply X86Routine.Prefix.step (middle := ⟨c56 s,none,0x2c95b⟩) (by simp) (by rfl) (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,logical32,relative8,result,c60,m15,c59,m14,c58,c57,c56,c55,m13,c54,c53,c52,c51,m12,c50,c49,c48,c47,c46,m11,c45,c44,c43,c42,c41,c40,c39,c38,orgX2,c37,m10,c36,m9,c35,c34,m8,c33,c32,m7,c31,orgX1,c30,c29,orgY1,c28,c27,nudgedY,c26,c25,boundaryY,c24,c23,c22,orgY0,c21,nudgedX,c20,c19,boundaryX,c18,m6,c17,c16,c15,c14,m5,c13,orgX0,c12,m4,c11,c10,oldValid,c9,c8,argument,c7,c6,c5,c4,c3,m3,c2,m2,c1,m1])
  apply X86Routine.Prefix.step (middle := ⟨c57 s,some {(logical32 ((((nudgedX s)-(orgX2 s)).sshiftRight 7) &&& 0xffff)) with carry:=some false},0x2c961⟩) (by simp) (by rfl) (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,logical32,relative8,result,c60,m15,c59,m14,c58,c57,c56,c55,m13,c54,c53,c52,c51,m12,c50,c49,c48,c47,c46,m11,c45,c44,c43,c42,c41,c40,c39,c38,orgX2,c37,m10,c36,m9,c35,c34,m8,c33,c32,m7,c31,orgX1,c30,c29,orgY1,c28,c27,nudgedY,c26,c25,boundaryY,c24,c23,c22,orgY0,c21,nudgedX,c20,c19,boundaryX,c18,m6,c17,c16,c15,c14,m5,c13,orgX0,c12,m4,c11,c10,oldValid,c9,c8,argument,c7,c6,c5,c4,c3,m3,c2,m2,c1,m1])
  apply X86Routine.Prefix.step (middle := ⟨c58 s,none,0x2c964⟩) (by simp) (by rfl) (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,logical32,relative8,result,c60,m15,c59,m14,c58,c57,c56,c55,m13,c54,c53,c52,c51,m12,c50,c49,c48,c47,c46,m11,c45,c44,c43,c42,c41,c40,c39,c38,orgX2,c37,m10,c36,m9,c35,c34,m8,c33,c32,m7,c31,orgX1,c30,c29,orgY1,c28,c27,nudgedY,c26,c25,boundaryY,c24,c23,c22,orgY0,c21,nudgedX,c20,c19,boundaryX,c18,m6,c17,c16,c15,c14,m5,c13,orgX0,c12,m4,c11,c10,oldValid,c9,c8,argument,c7,c6,c5,c4,c3,m3,c2,m2,c1,m1])
  apply X86Routine.Prefix.step (middle := ⟨c59 s,none,0x2c968⟩) (by simp) (by rfl) (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,logical32,relative8,result,c60,m15,c59,m14,c58,c57,c56,c55,m13,c54,c53,c52,c51,m12,c50,c49,c48,c47,c46,m11,c45,c44,c43,c42,c41,c40,c39,c38,orgX2,c37,m10,c36,m9,c35,c34,m8,c33,c32,m7,c31,orgX1,c30,c29,orgY1,c28,c27,nudgedY,c26,c25,boundaryY,c24,c23,c22,orgY0,c21,nudgedX,c20,c19,boundaryX,c18,m6,c17,c16,c15,c14,m5,c13,orgX0,c12,m4,c11,c10,oldValid,c9,c8,argument,c7,c6,c5,c4,c3,m3,c2,m2,c1,m1])
  apply X86Routine.Prefix.step (middle := (result s)) (by simp) (by rfl) (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,logical32,relative8,result,c60,m15,c59,m14,c58,c57,c56,c55,m13,c54,c53,c52,c51,m12,c50,c49,c48,c47,c46,m11,c45,c44,c43,c42,c41,c40,c39,c38,orgX2,c37,m10,c36,m9,c35,c34,m8,c33,c32,m7,c31,orgX1,c30,c29,orgY1,c28,c27,nudgedY,c26,c25,boundaryY,c24,c23,c22,orgY0,c21,nudgedX,c20,c19,boundaryX,c18,m6,c17,c16,c15,c14,m5,c13,orgX0,c12,m4,c11,c10,oldValid,c9,c8,argument,c7,c6,c5,c4,c3,m3,c2,m2,c1,m1])
  exact X86Routine.Prefix.nil _

theorem xbranch (s : X86Memory.State) :
    ∃ n, n≤2 ∧ X86Routine.Prefix listed [] n ⟨c19 s,some (logical32 (((s.regs 0)-(orgX0 s)) &&& 0x7fffff)),0x2c8df⟩ ⟨c21 s,(if boundaryX s then none else some (logical32 (((s.regs 0)-(orgX0 s)) &&& 0x7fffff))),0x2c8e7⟩ := by
  by_cases h : boundaryX s
  · refine ⟨2,by omega,?_⟩
    apply X86Routine.Prefix.step (middle := ⟨c20 s,some (logical32 (((s.regs 0)-(orgX0 s)) &&& 0x7fffff)),0x2c8e1⟩) (by simp) (by rfl) (by
      simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,logical32,relative8,result,c60,m15,c59,m14,c58,c57,c56,c55,m13,c54,c53,c52,c51,m12,c50,c49,c48,c47,c46,m11,c45,c44,c43,c42,c41,c40,c39,c38,orgX2,c37,m10,c36,m9,c35,c34,m8,c33,c32,m7,c31,orgX1,c30,c29,orgY1,c28,c27,nudgedY,c26,c25,boundaryY,c24,c23,c22,orgY0,c21,nudgedX,c20,c19,boundaryX,c18,m6,c17,c16,c15,c14,m5,c13,orgX0,c12,m4,c11,c10,oldValid,c9,c8,argument,c7,c6,c5,c4,c3,m3,c2,m2,c1,m1] <;> try (funext r; by_cases hr : r=6 <;> simp_all [write]))
    apply X86Routine.Prefix.step (middle := ⟨c21 s,(if boundaryX s then none else some (logical32 (((s.regs 0)-(orgX0 s)) &&& 0x7fffff))),0x2c8e7⟩) (by simp) (by rfl) (by
      simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,logical32,relative8,result,c60,m15,c59,m14,c58,c57,c56,c55,m13,c54,c53,c52,c51,m12,c50,c49,c48,c47,c46,m11,c45,c44,c43,c42,c41,c40,c39,c38,orgX2,c37,m10,c36,m9,c35,c34,m8,c33,c32,m7,c31,orgX1,c30,c29,orgY1,c28,c27,nudgedY,c26,c25,boundaryY,c24,c23,c22,orgY0,c21,nudgedX,c20,c19,boundaryX,c18,m6,c17,c16,c15,c14,m5,c13,orgX0,c12,m4,c11,c10,oldValid,c9,c8,argument,c7,c6,c5,c4,c3,m3,c2,m2,c1,m1] <;> try (funext r; by_cases hr : r=6 <;> simp_all [write]))
    exact X86Routine.Prefix.nil _
  · refine ⟨1,by omega,?_⟩
    apply X86Routine.Prefix.step (middle := ⟨c21 s,(if boundaryX s then none else some (logical32 (((s.regs 0)-(orgX0 s)) &&& 0x7fffff))),0x2c8e7⟩) (by simp) (by rfl) (by
      simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,logical32,relative8,result,c60,m15,c59,m14,c58,c57,c56,c55,m13,c54,c53,c52,c51,m12,c50,c49,c48,c47,c46,m11,c45,c44,c43,c42,c41,c40,c39,c38,orgX2,c37,m10,c36,m9,c35,c34,m8,c33,c32,m7,c31,orgX1,c30,c29,orgY1,c28,c27,nudgedY,c26,c25,boundaryY,c24,c23,c22,orgY0,c21,nudgedX,c20,c19,boundaryX,c18,m6,c17,c16,c15,c14,m5,c13,orgX0,c12,m4,c11,c10,oldValid,c9,c8,argument,c7,c6,c5,c4,c3,m3,c2,m2,c1,m1] <;> try (funext r; by_cases hr : r=6 <;> simp_all [write]))
    exact X86Routine.Prefix.nil _

theorem ybranch (s : X86Memory.State) :
    ∃ n, n≤2 ∧ X86Routine.Prefix listed [] n ⟨c25 s,some (logical32 (((s.regs 2)-(orgY0 s)) &&& 0x7fffff)),0x2c8f6⟩ ⟨c27 s,(if boundaryY s then none else some (logical32 (((s.regs 2)-(orgY0 s)) &&& 0x7fffff))),0x2c8fe⟩ := by
  by_cases h : boundaryY s
  · refine ⟨2,by omega,?_⟩
    apply X86Routine.Prefix.step (middle := ⟨c26 s,some (logical32 (((s.regs 2)-(orgY0 s)) &&& 0x7fffff)),0x2c8f8⟩) (by simp) (by rfl) (by
      simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,logical32,relative8,result,c60,m15,c59,m14,c58,c57,c56,c55,m13,c54,c53,c52,c51,m12,c50,c49,c48,c47,c46,m11,c45,c44,c43,c42,c41,c40,c39,c38,orgX2,c37,m10,c36,m9,c35,c34,m8,c33,c32,m7,c31,orgX1,c30,c29,orgY1,c28,c27,nudgedY,c26,c25,boundaryY,c24,c23,c22,orgY0,c21,nudgedX,c20,c19,boundaryX,c18,m6,c17,c16,c15,c14,m5,c13,orgX0,c12,m4,c11,c10,oldValid,c9,c8,argument,c7,c6,c5,c4,c3,m3,c2,m2,c1,m1] <;> try (funext r; by_cases hr : r=7 <;> simp_all [write]))
    apply X86Routine.Prefix.step (middle := ⟨c27 s,(if boundaryY s then none else some (logical32 (((s.regs 2)-(orgY0 s)) &&& 0x7fffff))),0x2c8fe⟩) (by simp) (by rfl) (by
      simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,logical32,relative8,result,c60,m15,c59,m14,c58,c57,c56,c55,m13,c54,c53,c52,c51,m12,c50,c49,c48,c47,c46,m11,c45,c44,c43,c42,c41,c40,c39,c38,orgX2,c37,m10,c36,m9,c35,c34,m8,c33,c32,m7,c31,orgX1,c30,c29,orgY1,c28,c27,nudgedY,c26,c25,boundaryY,c24,c23,c22,orgY0,c21,nudgedX,c20,c19,boundaryX,c18,m6,c17,c16,c15,c14,m5,c13,orgX0,c12,m4,c11,c10,oldValid,c9,c8,argument,c7,c6,c5,c4,c3,m3,c2,m2,c1,m1] <;> try (funext r; by_cases hr : r=7 <;> simp_all [write]))
    exact X86Routine.Prefix.nil _
  · refine ⟨1,by omega,?_⟩
    apply X86Routine.Prefix.step (middle := ⟨c27 s,(if boundaryY s then none else some (logical32 (((s.regs 2)-(orgY0 s)) &&& 0x7fffff))),0x2c8fe⟩) (by simp) (by rfl) (by
      simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,logical32,relative8,result,c60,m15,c59,m14,c58,c57,c56,c55,m13,c54,c53,c52,c51,m12,c50,c49,c48,c47,c46,m11,c45,c44,c43,c42,c41,c40,c39,c38,orgX2,c37,m10,c36,m9,c35,c34,m8,c33,c32,m7,c31,orgX1,c30,c29,orgY1,c28,c27,nudgedY,c26,c25,boundaryY,c24,c23,c22,orgY0,c21,nudgedX,c20,c19,boundaryX,c18,m6,c17,c16,c15,c14,m5,c13,orgX0,c12,m4,c11,c10,oldValid,c9,c8,argument,c7,c6,c5,c4,c3,m3,c2,m2,c1,m1] <;> try (funext r; by_cases hr : r=7 <;> simp_all [write]))
    exact X86Routine.Prefix.nil _

theorem prefix_trans {p exits n m a b c}
    (x : X86Routine.Prefix p exits n a b) (y : X86Routine.Prefix p exits m b c) :
    X86Routine.Prefix p exits (n+m) a c := by
  induction x with
  | nil => simpa using y
  | step he hd hx _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using X86Routine.Prefix.step he hd hx (ih y)

/-- All instructions up to the first X stepping comparison, for arbitrary byte memory. -/
theorem execution (s : X86Memory.State) (f : Option Flags) :
    ∃ n, n≤60 ∧ X86Routine.Prefix program [] n ⟨s,f,0x2c8a0⟩ (result s) := by
  obtain ⟨nx,hx,px⟩ := xbranch s
  obtain ⟨ny,hy,py⟩ := ybranch s
  have p := prefix_trans (prefix_trans (prefix_trans (prefix_trans (entry s f) px) (middle s f)) py) (finish s f)
  exact ⟨_,by omega,p.transfer program [] decoded (by simp)⟩

/-- Every destination, in actual instruction order. -/
def writes (s : X86Memory.State) : Vector Word 15 := #v[s.regs 4-4,s.regs 4-8,s.regs 4-12,0x2c028,0x2c024,0x13580,0x2ba18,0x2ba10,0x2ba14,0x2ba1c,(s.regs 4-48),(s.regs 4-44),(s.regs 4-40),(s.regs 4-52),(s.regs 4-36)]
def Separated (s : X86Memory.State) : Prop :=
  ∀ i j : Fin 15, i≠j → Apart ((writes s).get i) ((writes s).get j)
theorem frame3 (s : X86Memory.State) (a : Word)
    (safe : ∀ b, b ∈ (writes s).toList → Apart a b) :
    load32 (m3 s) a=load32 s.memory a := by
  simp only [m3,m2,m1]
  repeat rw [load_store_apart _ _ _ _ (safe _ (by simp [writes]))]

theorem frame4 (s : X86Memory.State) (a : Word)
    (safe : ∀ b, b ∈ (writes s).toList → Apart a b) :
    load32 (m4 s) a=load32 s.memory a := by
  simp only [m4,m3,m2,m1]
  repeat rw [load_store_apart _ _ _ _ (safe _ (by simp [writes]))]

theorem frame6 (s : X86Memory.State) (a : Word)
    (safe : ∀ b, b ∈ (writes s).toList → Apart a b) :
    load32 (m6 s) a=load32 s.memory a := by
  simp only [m6,m5,m4,m3,m2,m1]
  repeat rw [load_store_apart _ _ _ _ (safe _ (by simp [writes]))]

theorem frame10 (s : X86Memory.State) (a : Word)
    (safe : ∀ b, b ∈ (writes s).toList → Apart a b) :
    load32 (m10 s) a=load32 s.memory a := by
  simp only [m10,m9,m8,m7,m6,m5,m4,m3,m2,m1]
  repeat rw [load_store_apart _ _ _ _ (safe _ (by simp [writes]))]

theorem frame15 (s : X86Memory.State) (a : Word)
    (safe : ∀ b, b ∈ (writes s).toList → Apart a b) :
    load32 (m15 s) a=load32 s.memory a := by
  simp only [m15,m14,m13,m12,m11,m10,m9,m8,m7,m6,m5,m4,m3,m2,m1]
  repeat rw [load_store_apart _ _ _ _ (safe _ (by simp [writes]))]

theorem memory (s : X86Memory.State) : (result s).core.memory=m15 s := rfl
theorem stored_1 (s : X86Memory.State) (h : Separated s) :
    load32 (result s).core.memory (s.regs 4-4)=s.regs 6 := by
  rw [memory]
  simp only [m15,m14,m13,m12,m11,m10,m9,m8,m7,m6,m5,m4,m3,m2,m1]
  rw [load_store_apart _ _ _ _ (show Apart (s.regs 4-4) ((s.regs 4-36)) from h 0 14 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (s.regs 4-4) ((s.regs 4-52)) from h 0 13 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (s.regs 4-4) ((s.regs 4-40)) from h 0 12 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (s.regs 4-4) ((s.regs 4-44)) from h 0 11 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (s.regs 4-4) ((s.regs 4-48)) from h 0 10 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (s.regs 4-4) (0x2ba1c) from h 0 9 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (s.regs 4-4) (0x2ba14) from h 0 8 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (s.regs 4-4) (0x2ba10) from h 0 7 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (s.regs 4-4) (0x2ba18) from h 0 6 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (s.regs 4-4) (0x13580) from h 0 5 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (s.regs 4-4) (0x2c024) from h 0 4 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (s.regs 4-4) (0x2c028) from h 0 3 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (s.regs 4-4) (s.regs 4-12) from h 0 2 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (s.regs 4-4) (s.regs 4-8) from h 0 1 (by decide))]
  exact load_store _ _ _

theorem stored_2 (s : X86Memory.State) (h : Separated s) :
    load32 (result s).core.memory (s.regs 4-8)=s.regs 7 := by
  rw [memory]
  simp only [m15,m14,m13,m12,m11,m10,m9,m8,m7,m6,m5,m4,m3,m2]
  rw [load_store_apart _ _ _ _ (show Apart (s.regs 4-8) ((s.regs 4-36)) from h 1 14 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (s.regs 4-8) ((s.regs 4-52)) from h 1 13 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (s.regs 4-8) ((s.regs 4-40)) from h 1 12 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (s.regs 4-8) ((s.regs 4-44)) from h 1 11 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (s.regs 4-8) ((s.regs 4-48)) from h 1 10 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (s.regs 4-8) (0x2ba1c) from h 1 9 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (s.regs 4-8) (0x2ba14) from h 1 8 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (s.regs 4-8) (0x2ba10) from h 1 7 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (s.regs 4-8) (0x2ba18) from h 1 6 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (s.regs 4-8) (0x13580) from h 1 5 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (s.regs 4-8) (0x2c024) from h 1 4 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (s.regs 4-8) (0x2c028) from h 1 3 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (s.regs 4-8) (s.regs 4-12) from h 1 2 (by decide))]
  exact load_store _ _ _

theorem stored_3 (s : X86Memory.State) (h : Separated s) :
    load32 (result s).core.memory (s.regs 4-12)=s.regs 5 := by
  rw [memory]
  simp only [m15,m14,m13,m12,m11,m10,m9,m8,m7,m6,m5,m4,m3]
  rw [load_store_apart _ _ _ _ (show Apart (s.regs 4-12) ((s.regs 4-36)) from h 2 14 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (s.regs 4-12) ((s.regs 4-52)) from h 2 13 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (s.regs 4-12) ((s.regs 4-40)) from h 2 12 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (s.regs 4-12) ((s.regs 4-44)) from h 2 11 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (s.regs 4-12) ((s.regs 4-48)) from h 2 10 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (s.regs 4-12) (0x2ba1c) from h 2 9 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (s.regs 4-12) (0x2ba14) from h 2 8 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (s.regs 4-12) (0x2ba10) from h 2 7 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (s.regs 4-12) (0x2ba18) from h 2 6 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (s.regs 4-12) (0x13580) from h 2 5 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (s.regs 4-12) (0x2c024) from h 2 4 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (s.regs 4-12) (0x2c028) from h 2 3 (by decide))]
  exact load_store _ _ _

theorem stored_4 (s : X86Memory.State) (h : Separated s) :
    load32 (result s).core.memory (0x2c028)=0x2ba20 := by
  rw [memory]
  simp only [m15,m14,m13,m12,m11,m10,m9,m8,m7,m6,m5,m4]
  rw [load_store_apart _ _ _ _ (show Apart (0x2c028) ((s.regs 4-36)) from h 3 14 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (0x2c028) ((s.regs 4-52)) from h 3 13 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (0x2c028) ((s.regs 4-40)) from h 3 12 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (0x2c028) ((s.regs 4-44)) from h 3 11 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (0x2c028) ((s.regs 4-48)) from h 3 10 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (0x2c028) (0x2ba1c) from h 3 9 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (0x2c028) (0x2ba14) from h 3 8 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (0x2c028) (0x2ba10) from h 3 7 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (0x2c028) (0x2ba18) from h 3 6 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (0x2c028) (0x13580) from h 3 5 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (0x2c028) (0x2c024) from h 3 4 (by decide))]
  exact load_store _ _ _

theorem stored_5 (s : X86Memory.State) (h : Separated s) :
    load32 (result s).core.memory (0x2c024)=(argument s) &&& 0x4 := by
  rw [memory]
  simp only [m15,m14,m13,m12,m11,m10,m9,m8,m7,m6,m5]
  rw [load_store_apart _ _ _ _ (show Apart (0x2c024) ((s.regs 4-36)) from h 4 14 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (0x2c024) ((s.regs 4-52)) from h 4 13 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (0x2c024) ((s.regs 4-40)) from h 4 12 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (0x2c024) ((s.regs 4-44)) from h 4 11 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (0x2c024) ((s.regs 4-48)) from h 4 10 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (0x2c024) (0x2ba1c) from h 4 9 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (0x2c024) (0x2ba14) from h 4 8 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (0x2c024) (0x2ba10) from h 4 7 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (0x2c024) (0x2ba18) from h 4 6 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (0x2c024) (0x13580) from h 4 5 (by decide))]
  exact load_store _ _ _

theorem stored_6 (s : X86Memory.State) (h : Separated s) :
    load32 (result s).core.memory (0x13580)=(oldValid s)+1 := by
  rw [memory]
  simp only [m15,m14,m13,m12,m11,m10,m9,m8,m7,m6]
  rw [load_store_apart _ _ _ _ (show Apart (0x13580) ((s.regs 4-36)) from h 5 14 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (0x13580) ((s.regs 4-52)) from h 5 13 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (0x13580) ((s.regs 4-40)) from h 5 12 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (0x13580) ((s.regs 4-44)) from h 5 11 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (0x13580) ((s.regs 4-48)) from h 5 10 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (0x13580) (0x2ba1c) from h 5 9 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (0x13580) (0x2ba14) from h 5 8 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (0x13580) (0x2ba10) from h 5 7 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (0x13580) (0x2ba18) from h 5 6 (by decide))]
  exact load_store _ _ _

theorem stored_7 (s : X86Memory.State) (h : Separated s) :
    load32 (result s).core.memory (0x2ba18)=(s.regs 3)-(nudgedX s) := by
  rw [memory]
  simp only [m15,m14,m13,m12,m11,m10,m9,m8,m7]
  rw [load_store_apart _ _ _ _ (show Apart (0x2ba18) ((s.regs 4-36)) from h 6 14 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (0x2ba18) ((s.regs 4-52)) from h 6 13 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (0x2ba18) ((s.regs 4-40)) from h 6 12 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (0x2ba18) ((s.regs 4-44)) from h 6 11 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (0x2ba18) ((s.regs 4-48)) from h 6 10 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (0x2ba18) (0x2ba1c) from h 6 9 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (0x2ba18) (0x2ba14) from h 6 8 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (0x2ba18) (0x2ba10) from h 6 7 (by decide))]
  exact load_store _ _ _

theorem stored_8 (s : X86Memory.State) (h : Separated s) :
    load32 (result s).core.memory (0x2ba10)=nudgedX s := by
  rw [memory]
  simp only [m15,m14,m13,m12,m11,m10,m9,m8]
  rw [load_store_apart _ _ _ _ (show Apart (0x2ba10) ((s.regs 4-36)) from h 7 14 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (0x2ba10) ((s.regs 4-52)) from h 7 13 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (0x2ba10) ((s.regs 4-40)) from h 7 12 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (0x2ba10) ((s.regs 4-44)) from h 7 11 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (0x2ba10) ((s.regs 4-48)) from h 7 10 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (0x2ba10) (0x2ba1c) from h 7 9 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (0x2ba10) (0x2ba14) from h 7 8 (by decide))]
  exact load_store _ _ _

theorem stored_9 (s : X86Memory.State) (h : Separated s) :
    load32 (result s).core.memory (0x2ba14)=nudgedY s := by
  rw [memory]
  simp only [m15,m14,m13,m12,m11,m10,m9]
  rw [load_store_apart _ _ _ _ (show Apart (0x2ba14) ((s.regs 4-36)) from h 8 14 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (0x2ba14) ((s.regs 4-52)) from h 8 13 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (0x2ba14) ((s.regs 4-40)) from h 8 12 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (0x2ba14) ((s.regs 4-44)) from h 8 11 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (0x2ba14) ((s.regs 4-48)) from h 8 10 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (0x2ba14) (0x2ba1c) from h 8 9 (by decide))]
  exact load_store _ _ _

theorem stored_10 (s : X86Memory.State) (h : Separated s) :
    load32 (result s).core.memory (0x2ba1c)=(s.regs 1)-(nudgedY s) := by
  rw [memory]
  simp only [m15,m14,m13,m12,m11,m10]
  rw [load_store_apart _ _ _ _ (show Apart (0x2ba1c) ((s.regs 4-36)) from h 9 14 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (0x2ba1c) ((s.regs 4-52)) from h 9 13 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (0x2ba1c) ((s.regs 4-40)) from h 9 12 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (0x2ba1c) ((s.regs 4-44)) from h 9 11 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (0x2ba1c) ((s.regs 4-48)) from h 9 10 (by decide))]
  exact load_store _ _ _

theorem stored_11 (s : X86Memory.State) (h : Separated s) :
    load32 (result s).core.memory ((s.regs 4-48))=((nudgedX s)-(orgX2 s)).sshiftRight 23 := by
  rw [memory]
  simp only [m15,m14,m13,m12,m11]
  rw [load_store_apart _ _ _ _ (show Apart ((s.regs 4-48)) ((s.regs 4-36)) from h 10 14 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart ((s.regs 4-48)) ((s.regs 4-52)) from h 10 13 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart ((s.regs 4-48)) ((s.regs 4-40)) from h 10 12 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart ((s.regs 4-48)) ((s.regs 4-44)) from h 10 11 (by decide))]
  exact load_store _ _ _

theorem stored_12 (s : X86Memory.State) (h : Separated s) :
    load32 (result s).core.memory ((s.regs 4-44))=((nudgedY s)-(orgY1 s)).sshiftRight 23 := by
  rw [memory]
  simp only [m15,m14,m13,m12]
  rw [load_store_apart _ _ _ _ (show Apart ((s.regs 4-44)) ((s.regs 4-36)) from h 11 14 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart ((s.regs 4-44)) ((s.regs 4-52)) from h 11 13 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart ((s.regs 4-44)) ((s.regs 4-40)) from h 11 12 (by decide))]
  exact load_store _ _ _

theorem stored_13 (s : X86Memory.State) (h : Separated s) :
    load32 (result s).core.memory ((s.regs 4-40))=((s.regs 3)-(orgX1 s)).sshiftRight 23 := by
  rw [memory]
  simp only [m15,m14,m13]
  rw [load_store_apart _ _ _ _ (show Apart ((s.regs 4-40)) ((s.regs 4-36)) from h 12 14 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart ((s.regs 4-40)) ((s.regs 4-52)) from h 12 13 (by decide))]
  exact load_store _ _ _

theorem stored_14 (s : X86Memory.State) (h : Separated s) :
    load32 (result s).core.memory ((s.regs 4-52))=(((nudgedX s)-(orgX2 s)).sshiftRight 7) &&& 0xffff := by
  rw [memory]
  simp only [m15,m14]
  rw [load_store_apart _ _ _ _ (show Apart ((s.regs 4-52)) ((s.regs 4-36)) from h 13 14 (by decide))]
  exact load_store _ _ _

theorem stored_15 (s : X86Memory.State) (h : Separated s) :
    load32 (result s).core.memory ((s.regs 4-36))=((s.regs 1)-(orgY1 s)).sshiftRight 23 := by
  rw [memory]
  simp only [m15]
  exact load_store _ _ _


def reads (s : X86Memory.State) : List Word := [0x2c104,0x2c108,s.regs 4+4]
/-- Encoding and byte separation, not the result of the traversal. -/
structure Inputs (s : X86Memory.State) (ox oy sx sy ex ey : Fixed) : Prop where
  startX : s.regs 0=sx.raw.toBitVec
  startY : s.regs 2=sy.raw.toBitVec
  endX : s.regs 3=ex.raw.toBitVec
  endY : s.regs 1=ey.raw.toBitVec
  originX : load32 s.memory 0x2c104=ox.raw.toBitVec
  originY : load32 s.memory 0x2c108=oy.raw.toBitVec
  safeReads : ∀ a, a ∈ reads s → ∀ b, b ∈ (writes s).toList → Apart a b
  separated : Separated s

theorem loaded_origins (s : X86Memory.State) (ox oy sx sy ex ey : Fixed)
    (h : Inputs s ox oy sx sy ex ey) :
    orgX0 s=ox.raw.toBitVec ∧ orgX1 s=ox.raw.toBitVec ∧ orgX2 s=ox.raw.toBitVec ∧
    orgY0 s=oy.raw.toBitVec ∧ orgY1 s=oy.raw.toBitVec := by
  have x := h.safeReads 0x2c104 (by simp [reads])
  have y := h.safeReads 0x2c108 (by simp [reads])
  simp only [orgX0,orgX1,orgX2,orgY0,orgY1,frame4 s _ x,frame6 s _ x,
    frame10 s _ x,frame6 s _ y,h.originX,h.originY,and_self]

def nudge (x origin : Word) : Word := if (x-origin) &&& 0x7fffff=0 then x+0x10000 else x

theorem live_nudge (x origin : Fixed) :
    (if (x-origin).raw &&& 8388607 == 0 then x+Fixed.ofInt 1 else x).raw.toBitVec =
    nudge x.raw.toBitVec origin.raw.toBitVec := by
  simp only [beq_iff_eq,←Int32.toBitVec_inj]
  change (if (x.raw.toBitVec-origin.raw.toBitVec) &&& 0x7fffff=0 then x+Fixed.ofInt 1 else x).raw.toBitVec = _
  split <;> simp_all [nudge]
  rfl

theorem nudges (s : X86Memory.State) (ox oy sx sy ex ey : Fixed)
    (h : Inputs s ox oy sx sy ex ey) :
    nudgedX s=(Collision.pathStart ox oy sx sy ex ey).trace.x.raw.toBitVec ∧
    nudgedY s=(Collision.pathStart ox oy sx sy ex ey).trace.y.raw.toBitVec := by
  obtain ⟨hx,_,_,hy,_⟩ := loaded_origins s ox oy sx sy ex ey h
  simp only [Collision.pathStart,live_nudge,nudgedX,nudgedY,boundaryX,boundaryY,
    h.startX,h.startY,hx,hy,nudge,and_self]

/-- The observable geometry and control locals at the first stepping comparison. -/
structure Ready (s : X86Memory.State) (t : X86Control.State) (p : Collision.PathStart) : Prop where
  trace : (load32 t.core.memory 0x2ba10,load32 t.core.memory 0x2ba14,
    load32 t.core.memory 0x2ba18,load32 t.core.memory 0x2ba1c)=
    (p.trace.x.raw.toBitVec,p.trace.y.raw.toBitVec,p.trace.dx.raw.toBitVec,p.trace.dy.raw.toBitVec)
  relative : (t.core.regs 6,t.core.regs 7,t.core.regs 5,t.core.regs 1)=
    (p.x1.raw.toBitVec,p.y1.raw.toBitVec,p.x2.raw.toBitVec,p.y2.raw.toBitVec)
  blocks : (load32 t.core.memory (s.regs 4-48),load32 t.core.memory (s.regs 4-44),
    load32 t.core.memory (s.regs 4-40),load32 t.core.memory (s.regs 4-36))=
    (p.startBlockX.toBitVec,p.startBlockY.toBitVec,p.endBlockX.toBitVec,p.endBlockY.toBitVec)
  fraction : load32 t.core.memory (s.regs 4-52)=p.xFraction.raw.toBitVec
  globals : (load32 t.core.memory 0x2c028,load32 t.core.memory 0x2c024,load32 t.core.memory 0x13580)=
    (0x2ba20,load32 s.memory (s.regs 4+4) &&& 4,load32 s.memory 0x13580+1)
  stack : t.core.regs 4=s.regs 4-60
  pc : t.pc=0x2c96c

theorem old_valid (s : X86Memory.State) (h : Separated s) :
    oldValid s=load32 s.memory 0x13580 := by
  simp only [oldValid,m3,m2,m1]
  rw [load_store_apart _ _ _ _ (show Apart (0x13580) (s.regs 4-12) from h 5 2 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (0x13580) (s.regs 4-8) from h 5 1 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (0x13580) (s.regs 4-4) from h 5 0 (by decide))]

theorem ready (s : X86Memory.State) (ox oy sx sy ex ey : Fixed)
    (h : Inputs s ox oy sx sy ex ey) :
    Ready s (result s) (Collision.pathStart ox oy sx sy ex ey) := by
  obtain ⟨hx0,hx1,hx2,hy0,hy1⟩ := loaded_origins s ox oy sx sy ex ey h
  obtain ⟨nx,ny⟩ := nudges s ox oy sx sy ex ey h
  have arg : argument s=load32 s.memory (s.regs 4+4) :=
    frame3 s _ (h.safeReads _ (by simp [reads]))
  have rel : (nudgedX s-orgX2 s,nudgedY s-orgY1 s,s.regs 3-orgX1 s,s.regs 1-orgY1 s)=
      ((Collision.pathStart ox oy sx sy ex ey).x1.raw.toBitVec,
       (Collision.pathStart ox oy sx sy ex ey).y1.raw.toBitVec,
       (Collision.pathStart ox oy sx sy ex ey).x2.raw.toBitVec,
       (Collision.pathStart ox oy sx sy ex ey).y2.raw.toBitVec) := by
    rw [nx,ny,hx1,hx2,hy1,h.endX,h.endY]
    rfl
  have rx := congrArg (fun v => v.1) rel
  have ry := congrArg (fun v => v.2.1) rel
  have ex := congrArg (fun v => v.2.2.1) rel
  have ey := congrArg (fun v => v.2.2.2) rel
  simp only [Prod.fst,Prod.snd] at rx ry ex ey
  constructor
  · rw [stored_8 s h.separated,stored_9 s h.separated,stored_7 s h.separated,stored_10 s h.separated,
      nx,ny,h.endX,h.endY]
    rfl
  · simpa [result,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,put,write] using rel
  · rw [stored_11 s h.separated,stored_12 s h.separated,stored_13 s h.separated,stored_15 s h.separated,
      rx,ry,ex,ey]
    rfl
  · rw [stored_14 s h.separated,rx]
    rfl
  · rw [stored_4 s h.separated,stored_5 s h.separated,stored_6 s h.separated,arg,old_valid s h.separated]
  · simp [result,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,put,write]
  · rfl

end Doom.Proofs.OriginalPathInit
