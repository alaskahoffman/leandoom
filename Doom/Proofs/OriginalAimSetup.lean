import Doom.Proofs.OriginalAimQuery
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalAimSetup
open Verification X86 X86Memory X86Control BlockSummary
def code : List UInt8 := [0x68,0x60,0xb7,0x2,0x0,0xa3,0xac,0xb9,0x2,0x0,0x89,0x1d,0xb8,0xb9,0x2,0x0,0x8b,0x78,0xc,0x6a,0x3,0x31,0xdb,0x8b,0x50,0x10,0x1,0xf9,0x1,0xd6,0x8b,0x50,0x44,0x8b,0x78,0x14,0xd1,0xfa,0x89,0x1d,0xf8,0xb9,0x2,0x0,0x1,0xfa,0x89,0xcb,0x81,0xc2,0x0,0x0,0x8,0x0,0xbd,0x0,0xa0,0x0,0x0,0x89,0x15,0xa8,0xb9,0x2,0x0,0xba,0x0,0x60,0xff,0xff,0x89,0xf1,0x89,0x15,0xe4,0xc1,0x2,0x0,0x8b,0x50,0x10,0x8b,0x40,0xc,0x89,0x2d,0xe8,0xc1,0x2,0x0,0xe8,0xa1,0xc,0x0,0x0]
def bytesProgram (bytes : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2bba0 ≤ pc ∧ pc < 0x2bbff then X86Routine.decodeAt bytes (pc-0x2bba0) else none
def program := bytesProgram code

def listed : X86Routine.Program
  | 0x2bba0 => some (.pushImmediate 0x2b760,5)
  | 0x2bba5 => some (.control (.storeEax 0x2b9ac),5)
  | 0x2bbaa => some (.control (.block (.store ⟨none,none,0,0x2b9b8⟩ 3)),6)
  | 0x2bbb0 => some (.control (.block (.legacy (.load 7 0 12))),3)
  | 0x2bbb3 => some (.pushImmediate 3,2)
  | 0x2bbb5 => some (.xorRegister 3 3,2)
  | 0x2bbb7 => some (.control (.block (.legacy (.load 2 0 16))),3)
  | 0x2bbba => some (.control (.block (.arithmetic (.add 1 7))),2)
  | 0x2bbbc => some (.control (.block (.arithmetic (.add 6 2))),2)
  | 0x2bbbe => some (.control (.block (.legacy (.load 2 0 68))),3)
  | 0x2bbc1 => some (.control (.block (.legacy (.load 7 0 20))),3)
  | 0x2bbc4 => some (.sar 2 1,2)
  | 0x2bbc6 => some (.control (.block (.store ⟨none,none,0,0x2b9f8⟩ 3)),6)
  | 0x2bbcc => some (.control (.block (.arithmetic (.add 2 7))),2)
  | 0x2bbce => some (.control (.block (.legacy (.mov 3 1))),2)
  | 0x2bbd0 => some (.addImmediate 2 0x80000,6)
  | 0x2bbd6 => some (.immediate 5 0xa000,5)
  | 0x2bbdb => some (.control (.block (.store ⟨none,none,0,0x2b9a8⟩ 2)),6)
  | 0x2bbe1 => some (.immediate 2 0xffff6000,5)
  | 0x2bbe6 => some (.control (.block (.legacy (.mov 1 6))),2)
  | 0x2bbe8 => some (.control (.block (.store ⟨none,none,0,0x2c1e4⟩ 2)),6)
  | 0x2bbee => some (.control (.block (.legacy (.load 2 0 16))),3)
  | 0x2bbf1 => some (.control (.block (.legacy (.load 0 0 12))),3)
  | 0x2bbf4 => some (.control (.block (.store ⟨none,none,0,0x2c1e8⟩ 5)),6)
  | 0x2bbfa => some (.call 0xca1,5)
  | _ => none

theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

-- Each read retains the actual memory at that instruction. In particular,
-- actor coordinates are reloaded after the global stores; aliasing is not erased.
def m1 (s : X86Memory.State) := store32 s.memory (s.regs 4-4) 0x2b760
def m2 (s : X86Memory.State) := store32 (m1 s) 0x2b9ac (s.regs 0)
def m3 (s : X86Memory.State) := store32 (m2 s) 0x2b9b8 (s.regs 3)
def m4 (s : X86Memory.State) := store32 (m3 s) (s.regs 4-8) 3
def x0 (s : X86Memory.State) := load32 (m3 s) (s.regs 0+12)
def y0 (s : X86Memory.State) := load32 (m4 s) (s.regs 0+16)
def height (s : X86Memory.State) := load32 (m4 s) (s.regs 0+68)
def z0 (s : X86Memory.State) := load32 (m4 s) (s.regs 0+20)
def endX (s : X86Memory.State) := s.regs 1+x0 s
def endY (s : X86Memory.State) := s.regs 6+y0 s
def shootZ (s : X86Memory.State) := (height s).sshiftRight 1+z0 s+0x80000
def m5 (s : X86Memory.State) := store32 (m4 s) 0x2b9f8 0
def m6 (s : X86Memory.State) := store32 (m5 s) 0x2b9a8 (shootZ s)
def m7 (s : X86Memory.State) := store32 (m6 s) 0x2c1e4 0xffff6000
def m8 (s : X86Memory.State) := store32 (m7 s) 0x2c1e8 0xa000
def m9 (s : X86Memory.State) := store32 (m8 s) (s.regs 4-12) 0x2bbff
def x1 (s : X86Memory.State) := load32 (m7 s) (s.regs 0+12)
def y1 (s : X86Memory.State) := load32 (m7 s) (s.regs 0+16)
def c1 (s : X86Memory.State) : X86Memory.State := {regs:=write s.regs 4 (s.regs 4-4),memory:=m1 s}
def c2 (s : X86Memory.State) : X86Memory.State := {c1 s with memory:=m2 s}
def c3 (s : X86Memory.State) : X86Memory.State := {c2 s with memory:=m3 s}
def c4 (s : X86Memory.State) : X86Memory.State := put (c3 s) 7 (x0 s)
def c5 (s : X86Memory.State) : X86Memory.State := {regs:=write (c4 s).regs 4 (s.regs 4-8),memory:=m4 s}
def c6 (s : X86Memory.State) : X86Memory.State := put (c5 s) 3 0
def c7 (s : X86Memory.State) : X86Memory.State := put (c6 s) 2 (y0 s)
def c8 (s : X86Memory.State) : X86Memory.State := put (c7 s) 1 (endX s)
def c9 (s : X86Memory.State) : X86Memory.State := put (c8 s) 6 (endY s)
def c10 (s : X86Memory.State) : X86Memory.State := put (c9 s) 2 (height s)
def c11 (s : X86Memory.State) : X86Memory.State := put (c10 s) 7 (z0 s)
def c12 (s : X86Memory.State) : X86Memory.State := put (c11 s) 2 ((height s).sshiftRight 1)
def c13 (s : X86Memory.State) : X86Memory.State := {c12 s with memory:=m5 s}
def c14 (s : X86Memory.State) : X86Memory.State := put (c13 s) 2 ((height s).sshiftRight 1+z0 s)
def c15 (s : X86Memory.State) : X86Memory.State := put (c14 s) 3 (endX s)
def c16 (s : X86Memory.State) : X86Memory.State := put (c15 s) 2 (shootZ s)
def c17 (s : X86Memory.State) : X86Memory.State := put (c16 s) 5 0xa000
def c18 (s : X86Memory.State) : X86Memory.State := {c17 s with memory:=m6 s}
def c19 (s : X86Memory.State) : X86Memory.State := put (c18 s) 2 0xffff6000
def c20 (s : X86Memory.State) : X86Memory.State := put (c19 s) 1 (endY s)
def c21 (s : X86Memory.State) : X86Memory.State := {c20 s with memory:=m7 s}
def c22 (s : X86Memory.State) : X86Memory.State := put (c21 s) 2 (y1 s)
def c23 (s : X86Memory.State) : X86Memory.State := put (c22 s) 0 (x1 s)
def c24 (s : X86Memory.State) : X86Memory.State := {c23 s with memory:=m8 s}
def c25 (s : X86Memory.State) : X86Memory.State := {regs:=write (c24 s).regs 4 (s.regs 4-12),memory:=m9 s}
def traversal (s : X86Memory.State) : X86Control.State := ⟨c25 s,none,0x2c8a0⟩

/-- Executes every remaining setup instruction, including the actual CALL. -/
theorem execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 25 ⟨s,f,0x2bba0⟩ (traversal s) := by
  have path : X86Routine.Prefix listed [] 25 ⟨s,f,0x2bba0⟩ (traversal s) := by
    apply X86Routine.Prefix.step (middle := ⟨c1 s,f,0x2bba5⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,c1,endX,endY,shootZ,x0,y0,height,z0,x1,y1,m9,m8,m7,m6,m5,m4,m3,m2,m1])
    apply X86Routine.Prefix.step (middle := ⟨c2 s,f,0x2bbaa⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,c2,c1,endX,endY,shootZ,x0,y0,height,z0,x1,y1,m9,m8,m7,m6,m5,m4,m3,m2,m1])
    apply X86Routine.Prefix.step (middle := ⟨c3 s,f,0x2bbb0⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,c3,c2,c1,endX,endY,shootZ,x0,y0,height,z0,x1,y1,m9,m8,m7,m6,m5,m4,m3,m2,m1])
    apply X86Routine.Prefix.step (middle := ⟨c4 s,f,0x2bbb3⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,c4,c3,c2,c1,endX,endY,shootZ,x0,y0,height,z0,x1,y1,m9,m8,m7,m6,m5,m4,m3,m2,m1])
    apply X86Routine.Prefix.step (middle := ⟨c5 s,f,0x2bbb5⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,c5,c4,c3,c2,c1,endX,endY,shootZ,x0,y0,height,z0,x1,y1,m9,m8,m7,m6,m5,m4,m3,m2,m1])
    apply X86Routine.Prefix.step (middle := ⟨c6 s,some {(logical32 0) with carry:=some false},0x2bbb7⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,c6,c5,c4,c3,c2,c1,endX,endY,shootZ,x0,y0,height,z0,x1,y1,m9,m8,m7,m6,m5,m4,m3,m2,m1])
    apply X86Routine.Prefix.step (middle := ⟨c7 s,some {(logical32 0) with carry:=some false},0x2bbba⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,c7,c6,c5,c4,c3,c2,c1,endX,endY,shootZ,x0,y0,height,z0,x1,y1,m9,m8,m7,m6,m5,m4,m3,m2,m1])
    apply X86Routine.Prefix.step (middle := ⟨c8 s,none,0x2bbbc⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,c8,c7,c6,c5,c4,c3,c2,c1,endX,endY,shootZ,x0,y0,height,z0,x1,y1,m9,m8,m7,m6,m5,m4,m3,m2,m1])
    apply X86Routine.Prefix.step (middle := ⟨c9 s,none,0x2bbbe⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,c9,c8,c7,c6,c5,c4,c3,c2,c1,endX,endY,shootZ,x0,y0,height,z0,x1,y1,m9,m8,m7,m6,m5,m4,m3,m2,m1])
    apply X86Routine.Prefix.step (middle := ⟨c10 s,none,0x2bbc1⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,endX,endY,shootZ,x0,y0,height,z0,x1,y1,m9,m8,m7,m6,m5,m4,m3,m2,m1])
    apply X86Routine.Prefix.step (middle := ⟨c11 s,none,0x2bbc4⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,endX,endY,shootZ,x0,y0,height,z0,x1,y1,m9,m8,m7,m6,m5,m4,m3,m2,m1])
    apply X86Routine.Prefix.step (middle := ⟨c12 s,none,0x2bbc6⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,endX,endY,shootZ,x0,y0,height,z0,x1,y1,m9,m8,m7,m6,m5,m4,m3,m2,m1])
    apply X86Routine.Prefix.step (middle := ⟨c13 s,none,0x2bbcc⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,endX,endY,shootZ,x0,y0,height,z0,x1,y1,m9,m8,m7,m6,m5,m4,m3,m2,m1])
    apply X86Routine.Prefix.step (middle := ⟨c14 s,none,0x2bbce⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,endX,endY,shootZ,x0,y0,height,z0,x1,y1,m9,m8,m7,m6,m5,m4,m3,m2,m1])
    apply X86Routine.Prefix.step (middle := ⟨c15 s,none,0x2bbd0⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,endX,endY,shootZ,x0,y0,height,z0,x1,y1,m9,m8,m7,m6,m5,m4,m3,m2,m1])
    apply X86Routine.Prefix.step (middle := ⟨c16 s,none,0x2bbd6⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,endX,endY,shootZ,x0,y0,height,z0,x1,y1,m9,m8,m7,m6,m5,m4,m3,m2,m1])
    apply X86Routine.Prefix.step (middle := ⟨c17 s,none,0x2bbdb⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,endX,endY,shootZ,x0,y0,height,z0,x1,y1,m9,m8,m7,m6,m5,m4,m3,m2,m1])
    apply X86Routine.Prefix.step (middle := ⟨c18 s,none,0x2bbe1⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,endX,endY,shootZ,x0,y0,height,z0,x1,y1,m9,m8,m7,m6,m5,m4,m3,m2,m1])
    apply X86Routine.Prefix.step (middle := ⟨c19 s,none,0x2bbe6⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,endX,endY,shootZ,x0,y0,height,z0,x1,y1,m9,m8,m7,m6,m5,m4,m3,m2,m1])
    apply X86Routine.Prefix.step (middle := ⟨c20 s,none,0x2bbe8⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,endX,endY,shootZ,x0,y0,height,z0,x1,y1,m9,m8,m7,m6,m5,m4,m3,m2,m1])
    apply X86Routine.Prefix.step (middle := ⟨c21 s,none,0x2bbee⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,endX,endY,shootZ,x0,y0,height,z0,x1,y1,m9,m8,m7,m6,m5,m4,m3,m2,m1])
    apply X86Routine.Prefix.step (middle := ⟨c22 s,none,0x2bbf1⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,endX,endY,shootZ,x0,y0,height,z0,x1,y1,m9,m8,m7,m6,m5,m4,m3,m2,m1])
    apply X86Routine.Prefix.step (middle := ⟨c23 s,none,0x2bbf4⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,endX,endY,shootZ,x0,y0,height,z0,x1,y1,m9,m8,m7,m6,m5,m4,m3,m2,m1])
    apply X86Routine.Prefix.step (middle := ⟨c24 s,none,0x2bbfa⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,endX,endY,shootZ,x0,y0,height,z0,x1,y1,m9,m8,m7,m6,m5,m4,m3,m2,m1])
    apply X86Routine.Prefix.step (middle := ⟨c25 s,none,0x2c8a0⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,eax,ebx,edx,BitVec.sub_sub,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,endX,endY,shootZ,x0,y0,height,z0,x1,y1,m9,m8,m7,m6,m5,m4,m3,m2,m1])
    exact X86Routine.Prefix.nil _
  exact path.transfer program [] decoded (by simp)

theorem registers (s : X86Memory.State) :
    ((traversal s).core.regs 0,(traversal s).core.regs 2,(traversal s).core.regs 3,
     (traversal s).core.regs 1,(traversal s).core.regs 4)=
    (x1 s,y1 s,endX s,endY s,s.regs 4-12) := by
  simp [traversal,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,put,write]

theorem memory (s : X86Memory.State) : (traversal s).core.memory=m9 s := rfl


/-- Exact store destinations in execution order, including argument/return slots. -/
def writes (s : X86Memory.State) : Vector Word 9 :=
  #v[s.regs 4-4,0x2b9ac,0x2b9b8,s.regs 4-8,0x2b9f8,0x2b9a8,0x2c1e4,0x2c1e8,s.regs 4-12]
def Separated (s : X86Memory.State) : Prop :=
  ∀ i j : Fin 9, i≠j → Apart ((writes s).get i) ((writes s).get j)
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

theorem frame7 (s : X86Memory.State) (a : Word)
    (safe : ∀ b, b ∈ (writes s).toList → Apart a b) :
    load32 (m7 s) a=load32 s.memory a := by
  simp only [m7,m6,m5,m4,m3,m2,m1]
  repeat rw [load_store_apart _ _ _ _ (safe _ (by simp [writes]))]

theorem frame9 (s : X86Memory.State) (a : Word)
    (safe : ∀ b, b ∈ (writes s).toList → Apart a b) :
    load32 (m9 s) a=load32 s.memory a := by
  simp only [m9,m8,m7,m6,m5,m4,m3,m2,m1]
  repeat rw [load_store_apart _ _ _ _ (safe _ (by simp [writes]))]

theorem stored_callback (s : X86Memory.State) (h : Separated s) :
    load32 (traversal s).core.memory (s.regs 4-4)=0x2b760 := by
  rw [memory]
  simp only [m9,m8,m7,m6,m5,m4,m3,m2,m1]
  rw [load_store_apart _ _ _ _ (show Apart (s.regs 4-4) (s.regs 4-12) from h 0 8 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (s.regs 4-4) (0x2c1e8) from h 0 7 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (s.regs 4-4) (0x2c1e4) from h 0 6 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (s.regs 4-4) (0x2b9a8) from h 0 5 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (s.regs 4-4) (0x2b9f8) from h 0 4 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (s.regs 4-4) (s.regs 4-8) from h 0 3 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (s.regs 4-4) (0x2b9b8) from h 0 2 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (s.regs 4-4) (0x2b9ac) from h 0 1 (by decide))]
  exact load_store _ _ _

theorem stored_shooter (s : X86Memory.State) (h : Separated s) :
    load32 (traversal s).core.memory (0x2b9ac)=s.regs 0 := by
  rw [memory]
  simp only [m9,m8,m7,m6,m5,m4,m3,m2]
  rw [load_store_apart _ _ _ _ (show Apart (0x2b9ac) (s.regs 4-12) from h 1 8 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (0x2b9ac) (0x2c1e8) from h 1 7 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (0x2b9ac) (0x2c1e4) from h 1 6 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (0x2b9ac) (0x2b9a8) from h 1 5 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (0x2b9ac) (0x2b9f8) from h 1 4 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (0x2b9ac) (s.regs 4-8) from h 1 3 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (0x2b9ac) (0x2b9b8) from h 1 2 (by decide))]
  exact load_store _ _ _

theorem stored_range (s : X86Memory.State) (h : Separated s) :
    load32 (traversal s).core.memory (0x2b9b8)=s.regs 3 := by
  rw [memory]
  simp only [m9,m8,m7,m6,m5,m4,m3]
  rw [load_store_apart _ _ _ _ (show Apart (0x2b9b8) (s.regs 4-12) from h 2 8 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (0x2b9b8) (0x2c1e8) from h 2 7 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (0x2b9b8) (0x2c1e4) from h 2 6 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (0x2b9b8) (0x2b9a8) from h 2 5 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (0x2b9b8) (0x2b9f8) from h 2 4 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (0x2b9b8) (s.regs 4-8) from h 2 3 (by decide))]
  exact load_store _ _ _

theorem stored_flags (s : X86Memory.State) (h : Separated s) :
    load32 (traversal s).core.memory (s.regs 4-8)=3 := by
  rw [memory]
  simp only [m9,m8,m7,m6,m5,m4]
  rw [load_store_apart _ _ _ _ (show Apart (s.regs 4-8) (s.regs 4-12) from h 3 8 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (s.regs 4-8) (0x2c1e8) from h 3 7 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (s.regs 4-8) (0x2c1e4) from h 3 6 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (s.regs 4-8) (0x2b9a8) from h 3 5 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (s.regs 4-8) (0x2b9f8) from h 3 4 (by decide))]
  exact load_store _ _ _

theorem stored_target (s : X86Memory.State) (h : Separated s) :
    load32 (traversal s).core.memory (0x2b9f8)=0 := by
  rw [memory]
  simp only [m9,m8,m7,m6,m5]
  rw [load_store_apart _ _ _ _ (show Apart (0x2b9f8) (s.regs 4-12) from h 4 8 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (0x2b9f8) (0x2c1e8) from h 4 7 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (0x2b9f8) (0x2c1e4) from h 4 6 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (0x2b9f8) (0x2b9a8) from h 4 5 (by decide))]
  exact load_store _ _ _

theorem stored_shootz (s : X86Memory.State) (h : Separated s) :
    load32 (traversal s).core.memory (0x2b9a8)=shootZ s := by
  rw [memory]
  simp only [m9,m8,m7,m6]
  rw [load_store_apart _ _ _ _ (show Apart (0x2b9a8) (s.regs 4-12) from h 5 8 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (0x2b9a8) (0x2c1e8) from h 5 7 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (0x2b9a8) (0x2c1e4) from h 5 6 (by decide))]
  exact load_store _ _ _

theorem stored_bottom (s : X86Memory.State) (h : Separated s) :
    load32 (traversal s).core.memory (0x2c1e4)=0xffff6000 := by
  rw [memory]
  simp only [m9,m8,m7]
  rw [load_store_apart _ _ _ _ (show Apart (0x2c1e4) (s.regs 4-12) from h 6 8 (by decide))]
  rw [load_store_apart _ _ _ _ (show Apart (0x2c1e4) (0x2c1e8) from h 6 7 (by decide))]
  exact load_store _ _ _

theorem stored_top (s : X86Memory.State) (h : Separated s) :
    load32 (traversal s).core.memory (0x2c1e8)=0xa000 := by
  rw [memory]
  simp only [m9,m8]
  rw [load_store_apart _ _ _ _ (show Apart (0x2c1e8) (s.regs 4-12) from h 7 8 (by decide))]
  exact load_store _ _ _

theorem stored_return (s : X86Memory.State) :
    load32 (traversal s).core.memory (s.regs 4-12)=0x2bbff := by
  rw [memory]
  simp only [m9]
  exact load_store _ _ _

def actorReads (s : X86Memory.State) : List Word :=
  [s.regs 0+12,s.regs 0+16,s.regs 0+20,s.regs 0+68]

/-- A representation of the shooter and displacement at setup entry. Read and
write separation are explicit; no geometry result is assumed. -/
structure Inputs (s : X86Memory.State) (thing : Collision.SolidThing)
    (angle : Angle) (distance : Fixed) : Prop where
  x : load32 s.memory (s.regs 0+12)=thing.x.raw.toBitVec
  y : load32 s.memory (s.regs 0+16)=thing.y.raw.toBitVec
  z : load32 s.memory (s.regs 0+20)=thing.z.raw.toBitVec
  height : load32 s.memory (s.regs 0+68)=thing.height.raw.toBitVec
  range : s.regs 3=distance.raw.toBitVec
  offsets : (thing.x.raw.toBitVec+s.regs 1,thing.y.raw.toBitVec+s.regs 6)=
    ((thing.attackEndpoint angle distance).1.raw.toBitVec,
     (thing.attackEndpoint angle distance).2.raw.toBitVec)
  reads : ∀ a, a ∈ actorReads s → ∀ b, b ∈ (writes s).toList → Apart a b
  separated : Separated s

theorem shooter_reads (s : X86Memory.State) (thing : Collision.SolidThing)
    (angle : Angle) (distance : Fixed) (h : Inputs s thing angle distance) :
    x0 s=thing.x.raw.toBitVec ∧ y0 s=thing.y.raw.toBitVec ∧
    z0 s=thing.z.raw.toBitVec ∧ height s=thing.height.raw.toBitVec ∧
    x1 s=thing.x.raw.toBitVec ∧ y1 s=thing.y.raw.toBitVec := by
  simp only [x0,y0,z0,height,x1,y1]
  rw [frame3 s _ (h.reads _ (by simp [actorReads])),
      frame4 s _ (h.reads _ (by simp [actorReads])),
      frame4 s _ (h.reads _ (by simp [actorReads])),
      frame4 s _ (h.reads _ (by simp [actorReads])),
      frame7 s _ (h.reads _ (by simp [actorReads])),
      frame7 s _ (h.reads _ (by simp [actorReads]))]
  exact ⟨h.x,h.y,h.z,h.height,h.x,h.y⟩

theorem live_coordinates (s : X86Memory.State) (thing : Collision.SolidThing)
    (angle : Angle) (distance : Fixed) (h : Inputs s thing angle distance) :
    ((traversal s).core.regs 0,(traversal s).core.regs 2,
     (traversal s).core.regs 3,(traversal s).core.regs 1,(traversal s).core.regs 4)=
    (thing.x.raw.toBitVec,thing.y.raw.toBitVec,
     (thing.attackEndpoint angle distance).1.raw.toBitVec,
     (thing.attackEndpoint angle distance).2.raw.toBitVec,s.regs 4-12) := by
  rw [registers]
  obtain ⟨hx,hy,hz,hh,hx1,hy1⟩ := shooter_reads s thing angle distance h
  have ends : (endX s,endY s)=
      ((thing.attackEndpoint angle distance).1.raw.toBitVec,
       (thing.attackEndpoint angle distance).2.raw.toBitVec) := by
    simpa only [endX,endY,hx,hy,BitVec.add_comm] using h.offsets
  have ex := congrArg Prod.fst ends
  have ey := congrArg Prod.snd ends
  simp only [Prod.fst,Prod.snd] at ex ey
  rw [hx1,hy1,ex,ey]

theorem live_height (s : X86Memory.State) (thing : Collision.SolidThing)
    (angle : Angle) (distance : Fixed) (h : Inputs s thing angle distance) :
    load32 (traversal s).core.memory 0x2b9a8=thing.shootHeight.raw.toBitVec := by
  rw [stored_shootz s h.separated]
  obtain ⟨_,_,hz,hh,_,_⟩ := shooter_reads s thing angle distance h
  simp only [shootZ,hh,hz,Collision.SolidThing.shootHeight,Fixed.add,Fixed.ofInt]
  change thing.height.raw.toBitVec.sshiftRight 1+thing.z.raw.toBitVec+_ =
    thing.z.raw.toBitVec+thing.height.raw.toBitVec.sshiftRight 1+_
  rw [BitVec.add_comm (thing.height.raw.toBitVec.sshiftRight 1)]
  rfl

theorem live_globals (s : X86Memory.State) (thing : Collision.SolidThing)
    (angle : Angle) (distance : Fixed) (h : Inputs s thing angle distance) :
    (load32 (traversal s).core.memory 0x2b9ac,load32 (traversal s).core.memory 0x2b9b8,
     load32 (traversal s).core.memory 0x2b9f8,load32 (traversal s).core.memory 0x2c1e4,
     load32 (traversal s).core.memory 0x2c1e8)=
    (s.regs 0,distance.raw.toBitVec,0,Collision.aimBottomSlope.raw.toBitVec,
      Collision.aimTopSlope.raw.toBitVec) := by
  rw [stored_shooter s h.separated,stored_range s h.separated,stored_target s h.separated,
    stored_bottom s h.separated,stored_top s h.separated,h.range]
  rfl

theorem call_frame (s : X86Memory.State) (h : Separated s) :
    (load32 (traversal s).core.memory ((traversal s).core.regs 4),
     load32 (traversal s).core.memory ((traversal s).core.regs 4+4),
     load32 (traversal s).core.memory ((traversal s).core.regs 4+8))=(0x2bbff,3,0x2b760) := by
  have sp : (traversal s).core.regs 4=s.regs 4-12 := congrArg (fun t => t.2.2.2.2) (registers s)
  have a : s.regs 4-12+4=s.regs 4-8 := by bv_decide
  have b : s.regs 4-12+8=s.regs 4-4 := by bv_decide
  rw [sp,a,b,stored_return s,stored_flags s h,stored_callback s h]
/-- Trace parameters and aiming globals supplied to the traversal/callback interface. -/
structure Ready (initial : X86Memory.State) (out : X86Control.State)
    (thing : Collision.SolidThing) (angle : Angle) (distance : Fixed) : Prop where
  coordinates : (out.core.regs 0,out.core.regs 2,out.core.regs 3,out.core.regs 1,out.core.regs 4)=
    (thing.x.raw.toBitVec,thing.y.raw.toBitVec,
     (thing.attackEndpoint angle distance).1.raw.toBitVec,
     (thing.attackEndpoint angle distance).2.raw.toBitVec,initial.regs 4-12)
  shootHeight : load32 out.core.memory 0x2b9a8=thing.shootHeight.raw.toBitVec
  globals : (load32 out.core.memory 0x2b9ac,load32 out.core.memory 0x2b9b8,
     load32 out.core.memory 0x2b9f8,load32 out.core.memory 0x2c1e4,load32 out.core.memory 0x2c1e8)=
    (initial.regs 0,distance.raw.toBitVec,0,Collision.aimBottomSlope.raw.toBitVec,Collision.aimTopSlope.raw.toBitVec)
  frame : (load32 out.core.memory (out.core.regs 4),load32 out.core.memory (out.core.regs 4+4),
    load32 out.core.memory (out.core.regs 4+8))=(0x2bbff,3,0x2b760)
  pc : out.pc=0x2c8a0

theorem ready (s : X86Memory.State) (thing : Collision.SolidThing)
    (angle : Angle) (distance : Fixed) (h : Inputs s thing angle distance) :
    Ready s (traversal s) thing angle distance :=
  ⟨live_coordinates s thing angle distance h,live_height s thing angle distance h,
   live_globals s thing angle distance h,call_frame s h.separated,rfl⟩
end Doom.Proofs.OriginalAimSetup
