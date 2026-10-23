import Doom.Proofs.E1M1AimLineCycle
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalAimActorGuard
open Verification X86 X86Memory X86Control BlockSummary
open OriginalAimWindow (v0 v1 v2 v3 v4 v5 v6 returned)
attribute [local irreducible] load32 store32
def code : List UInt8 := [0x8b,0x35,0xac,0xb9,0x2,0x0,0x8b,0x48,0x8,0x39,0xf1,0x75,0xa,0xb8,0x1,0x0,0x0,0x0,0xe9,0xa3,0x0,0x0,0x0,0xf6,0x41,0x68,0x4,0x75,0xc,0xb8,0x1,0x0,0x0,0x0,0x5d,0x5f,0x5e,0x5a,0x59,0x5b,0xc3]
def bytesProgram (bytes : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2b81a≤pc ∧ pc<0x2b843 then X86Routine.decodeAt bytes (pc-0x2b81a) else OriginalAimGuard.program pc
def program := bytesProgram code
def listed : X86Routine.Program
  | 0x2b81a => some (.control (.block (.load 6 ⟨none,none,0,0x2b9ac⟩)),6)
  | 0x2b820 => some (.control (.block (.legacy (.load 1 0 8))),3)
  | 0x2b823 => some (.compareRegisters 1 6,2)
  | 0x2b825 => some (.control (.jumpZero false 10),2)
  | 0x2b827 => some (.immediate 0 1,5)
  | 0x2b82c => some (.jump 163,5)
  | 0x2b831 => some (.testMemoryByte ⟨some 1,none,0,104⟩ 4,4)
  | 0x2b835 => some (.control (.jumpZero false 12),2)
  | 0x2b837 => some (.immediate 0 1,5)
  | 0x2b83c => some (.pop 5,1)
  | 0x2b83d => some (.pop 7,1)
  | 0x2b83e => some (.pop 6,1)
  | 0x2b83f => some (.pop 2,1)
  | 0x2b840 => some (.pop 1,1)
  | 0x2b841 => some (.pop 3,1)
  | 0x2b842 => some (.ret,1)
  | 0x2b8d4 => some (.pop 5,1)
  | 0x2b8d5 => some (.pop 7,1)
  | 0x2b8d6 => some (.pop 6,1)
  | 0x2b8d7 => some (.pop 2,1)
  | 0x2b8d8 => some (.pop 1,1)
  | 0x2b8d9 => some (.pop 3,1)
  | 0x2b8da => some (.ret,1)
  | _ => none

theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

theorem contains_guard (pc : Nat) (h : OriginalAimGuard.program pc≠none) :
    program pc=OriginalAimGuard.program pc := by
  have outside : ¬(0x2b81a≤pc ∧ pc<0x2b843) := by
    intro inside
    have left : ¬(0x2b760≤pc ∧ pc<0x2b77f) := by omega
    have right : ¬(0x2b8d2≤pc ∧ pc<0x2b8db) := by omega
    simp [OriginalAimGuard.program,OriginalAimGuard.bytesProgram,left,right] at h
  simp only [program,bytesProgram,if_neg outside]

def shooter (s : X86Memory.State) := load32 s.memory (0x2b9ac#32)
def actor (s : X86Memory.State) := load32 s.memory (s.regs 0+8)
def first (s : X86Memory.State) := put s 6 (shooter s)
def loaded (s : X86Memory.State) := put (first s) 1 (actor s)
def gate (s : X86Memory.State) : X86Control.State :=
  ⟨loaded s,some (compare32 (actor s) (shooter s)),if actor s=shooter s then 0x2b827 else 0x2b831⟩
def bits (s : X86Memory.State) := s.memory (s.regs 1+104) &&& (4#8)
def flagGate (s : X86Memory.State) : X86Control.State :=
  ⟨s,some (logical8 (bits s)),if bits s=0 then 0x2b837 else 0x2b843⟩

theorem head_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 4 ⟨s,f,0x2b81a⟩ (gate s) := by
  have run : X86Routine.Prefix listed [] 4 ⟨s,f,0x2b81a⟩ (gate s) := by
    apply X86Routine.Prefix.step (middle := ⟨first s,f,0x2b820⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,shooter,actor,first,loaded,gate,bits,flagGate,cmp32_zero,logical8,OriginalAimWindow.v0,OriginalAimWindow.v1,OriginalAimWindow.v2,OriginalAimWindow.v3,OriginalAimWindow.v4,OriginalAimWindow.v5,OriginalAimWindow.v6,OriginalAimWindow.returned,OriginalAimGuard.pop,BitVec.add_assoc]
      all_goals split <;> simp_all)
    apply X86Routine.Prefix.step (middle := ⟨loaded s,f,0x2b823⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,shooter,actor,first,loaded,gate,bits,flagGate,cmp32_zero,logical8,OriginalAimWindow.v0,OriginalAimWindow.v1,OriginalAimWindow.v2,OriginalAimWindow.v3,OriginalAimWindow.v4,OriginalAimWindow.v5,OriginalAimWindow.v6,OriginalAimWindow.returned,OriginalAimGuard.pop,BitVec.add_assoc]
      all_goals split <;> simp_all)
    apply X86Routine.Prefix.step (middle := ⟨loaded s,some (compare32 (actor s) (shooter s)),0x2b825⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,shooter,actor,first,loaded,gate,bits,flagGate,cmp32_zero,logical8,OriginalAimWindow.v0,OriginalAimWindow.v1,OriginalAimWindow.v2,OriginalAimWindow.v3,OriginalAimWindow.v4,OriginalAimWindow.v5,OriginalAimWindow.v6,OriginalAimWindow.returned,OriginalAimGuard.pop,BitVec.add_assoc]
      all_goals split <;> simp_all)
    apply X86Routine.Prefix.step (middle := gate s) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,shooter,actor,first,loaded,gate,bits,flagGate,cmp32_zero,logical8,OriginalAimWindow.v0,OriginalAimWindow.v1,OriginalAimWindow.v2,OriginalAimWindow.v3,OriginalAimWindow.v4,OriginalAimWindow.v5,OriginalAimWindow.v6,OriginalAimWindow.returned,OriginalAimGuard.pop,BitVec.add_assoc]
      all_goals split <;> simp_all)
    exact .nil _
  exact run.transfer program [] decoded (by simp)

theorem flags_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 2 ⟨s,f,0x2b831⟩ (flagGate s) := by
  have run : X86Routine.Prefix listed [] 2 ⟨s,f,0x2b831⟩ (flagGate s) := by
    apply X86Routine.Prefix.step (middle := ⟨s,some (logical8 (bits s)),0x2b835⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,shooter,actor,first,loaded,gate,bits,flagGate,cmp32_zero,logical8,OriginalAimWindow.v0,OriginalAimWindow.v1,OriginalAimWindow.v2,OriginalAimWindow.v3,OriginalAimWindow.v4,OriginalAimWindow.v5,OriginalAimWindow.v6,OriginalAimWindow.returned,OriginalAimGuard.pop,BitVec.add_assoc]
      all_goals split <;> simp_all)
    apply X86Routine.Prefix.step (middle := flagGate s) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,shooter,actor,first,loaded,gate,bits,flagGate,cmp32_zero,logical8,OriginalAimWindow.v0,OriginalAimWindow.v1,OriginalAimWindow.v2,OriginalAimWindow.v3,OriginalAimWindow.v4,OriginalAimWindow.v5,OriginalAimWindow.v6,OriginalAimWindow.returned,OriginalAimGuard.pop,BitVec.add_assoc]
      all_goals split <;> simp_all)
    exact .nil _
  exact run.transfer program [] decoded (by simp)

theorem self_return_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 9 ⟨s,f,0x2b827⟩ (returned s 1 f) := by
  have run : X86Routine.Prefix listed [] 9 ⟨s,f,0x2b827⟩ (returned s 1 f) := by
    apply X86Routine.Prefix.step (middle := ⟨v0 s 1,f,0x2b82c⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,shooter,actor,first,loaded,gate,bits,flagGate,cmp32_zero,logical8,OriginalAimWindow.v0,OriginalAimWindow.v1,OriginalAimWindow.v2,OriginalAimWindow.v3,OriginalAimWindow.v4,OriginalAimWindow.v5,OriginalAimWindow.v6,OriginalAimWindow.returned,OriginalAimGuard.pop,BitVec.add_assoc]
      all_goals split <;> simp_all)
    apply X86Routine.Prefix.step (middle := ⟨v0 s 1,f,0x2b8d4⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,shooter,actor,first,loaded,gate,bits,flagGate,cmp32_zero,logical8,OriginalAimWindow.v0,OriginalAimWindow.v1,OriginalAimWindow.v2,OriginalAimWindow.v3,OriginalAimWindow.v4,OriginalAimWindow.v5,OriginalAimWindow.v6,OriginalAimWindow.returned,OriginalAimGuard.pop,BitVec.add_assoc]
      all_goals split <;> simp_all)
    apply X86Routine.Prefix.step (middle := ⟨v1 s 1,f,0x2b8d5⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,shooter,actor,first,loaded,gate,bits,flagGate,cmp32_zero,logical8,OriginalAimWindow.v0,OriginalAimWindow.v1,OriginalAimWindow.v2,OriginalAimWindow.v3,OriginalAimWindow.v4,OriginalAimWindow.v5,OriginalAimWindow.v6,OriginalAimWindow.returned,OriginalAimGuard.pop,BitVec.add_assoc]
      all_goals split <;> simp_all)
    apply X86Routine.Prefix.step (middle := ⟨v2 s 1,f,0x2b8d6⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,shooter,actor,first,loaded,gate,bits,flagGate,cmp32_zero,logical8,OriginalAimWindow.v0,OriginalAimWindow.v1,OriginalAimWindow.v2,OriginalAimWindow.v3,OriginalAimWindow.v4,OriginalAimWindow.v5,OriginalAimWindow.v6,OriginalAimWindow.returned,OriginalAimGuard.pop,BitVec.add_assoc]
      all_goals split <;> simp_all)
    apply X86Routine.Prefix.step (middle := ⟨v3 s 1,f,0x2b8d7⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,shooter,actor,first,loaded,gate,bits,flagGate,cmp32_zero,logical8,OriginalAimWindow.v0,OriginalAimWindow.v1,OriginalAimWindow.v2,OriginalAimWindow.v3,OriginalAimWindow.v4,OriginalAimWindow.v5,OriginalAimWindow.v6,OriginalAimWindow.returned,OriginalAimGuard.pop,BitVec.add_assoc]
      all_goals split <;> simp_all)
    apply X86Routine.Prefix.step (middle := ⟨v4 s 1,f,0x2b8d8⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,shooter,actor,first,loaded,gate,bits,flagGate,cmp32_zero,logical8,OriginalAimWindow.v0,OriginalAimWindow.v1,OriginalAimWindow.v2,OriginalAimWindow.v3,OriginalAimWindow.v4,OriginalAimWindow.v5,OriginalAimWindow.v6,OriginalAimWindow.returned,OriginalAimGuard.pop,BitVec.add_assoc]
      all_goals split <;> simp_all)
    apply X86Routine.Prefix.step (middle := ⟨v5 s 1,f,0x2b8d9⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,shooter,actor,first,loaded,gate,bits,flagGate,cmp32_zero,logical8,OriginalAimWindow.v0,OriginalAimWindow.v1,OriginalAimWindow.v2,OriginalAimWindow.v3,OriginalAimWindow.v4,OriginalAimWindow.v5,OriginalAimWindow.v6,OriginalAimWindow.returned,OriginalAimGuard.pop,BitVec.add_assoc]
      all_goals split <;> simp_all)
    apply X86Routine.Prefix.step (middle := ⟨v6 s 1,f,0x2b8da⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,shooter,actor,first,loaded,gate,bits,flagGate,cmp32_zero,logical8,OriginalAimWindow.v0,OriginalAimWindow.v1,OriginalAimWindow.v2,OriginalAimWindow.v3,OriginalAimWindow.v4,OriginalAimWindow.v5,OriginalAimWindow.v6,OriginalAimWindow.returned,OriginalAimGuard.pop,BitVec.add_assoc]
      all_goals split <;> simp_all)
    apply X86Routine.Prefix.step (middle := returned s 1 f) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,shooter,actor,first,loaded,gate,bits,flagGate,cmp32_zero,logical8,OriginalAimWindow.v0,OriginalAimWindow.v1,OriginalAimWindow.v2,OriginalAimWindow.v3,OriginalAimWindow.v4,OriginalAimWindow.v5,OriginalAimWindow.v6,OriginalAimWindow.returned,OriginalAimGuard.pop,BitVec.add_assoc]
      all_goals split <;> simp_all)
    exact .nil _
  exact run.transfer program [] decoded (by simp)

theorem skip_return_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 8 ⟨s,f,0x2b837⟩ (returned s 1 f) := by
  have run : X86Routine.Prefix listed [] 8 ⟨s,f,0x2b837⟩ (returned s 1 f) := by
    apply X86Routine.Prefix.step (middle := ⟨v0 s 1,f,0x2b83c⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,shooter,actor,first,loaded,gate,bits,flagGate,cmp32_zero,logical8,OriginalAimWindow.v0,OriginalAimWindow.v1,OriginalAimWindow.v2,OriginalAimWindow.v3,OriginalAimWindow.v4,OriginalAimWindow.v5,OriginalAimWindow.v6,OriginalAimWindow.returned,OriginalAimGuard.pop,BitVec.add_assoc]
      all_goals split <;> simp_all)
    apply X86Routine.Prefix.step (middle := ⟨v1 s 1,f,0x2b83d⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,shooter,actor,first,loaded,gate,bits,flagGate,cmp32_zero,logical8,OriginalAimWindow.v0,OriginalAimWindow.v1,OriginalAimWindow.v2,OriginalAimWindow.v3,OriginalAimWindow.v4,OriginalAimWindow.v5,OriginalAimWindow.v6,OriginalAimWindow.returned,OriginalAimGuard.pop,BitVec.add_assoc]
      all_goals split <;> simp_all)
    apply X86Routine.Prefix.step (middle := ⟨v2 s 1,f,0x2b83e⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,shooter,actor,first,loaded,gate,bits,flagGate,cmp32_zero,logical8,OriginalAimWindow.v0,OriginalAimWindow.v1,OriginalAimWindow.v2,OriginalAimWindow.v3,OriginalAimWindow.v4,OriginalAimWindow.v5,OriginalAimWindow.v6,OriginalAimWindow.returned,OriginalAimGuard.pop,BitVec.add_assoc]
      all_goals split <;> simp_all)
    apply X86Routine.Prefix.step (middle := ⟨v3 s 1,f,0x2b83f⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,shooter,actor,first,loaded,gate,bits,flagGate,cmp32_zero,logical8,OriginalAimWindow.v0,OriginalAimWindow.v1,OriginalAimWindow.v2,OriginalAimWindow.v3,OriginalAimWindow.v4,OriginalAimWindow.v5,OriginalAimWindow.v6,OriginalAimWindow.returned,OriginalAimGuard.pop,BitVec.add_assoc]
      all_goals split <;> simp_all)
    apply X86Routine.Prefix.step (middle := ⟨v4 s 1,f,0x2b840⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,shooter,actor,first,loaded,gate,bits,flagGate,cmp32_zero,logical8,OriginalAimWindow.v0,OriginalAimWindow.v1,OriginalAimWindow.v2,OriginalAimWindow.v3,OriginalAimWindow.v4,OriginalAimWindow.v5,OriginalAimWindow.v6,OriginalAimWindow.returned,OriginalAimGuard.pop,BitVec.add_assoc]
      all_goals split <;> simp_all)
    apply X86Routine.Prefix.step (middle := ⟨v5 s 1,f,0x2b841⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,shooter,actor,first,loaded,gate,bits,flagGate,cmp32_zero,logical8,OriginalAimWindow.v0,OriginalAimWindow.v1,OriginalAimWindow.v2,OriginalAimWindow.v3,OriginalAimWindow.v4,OriginalAimWindow.v5,OriginalAimWindow.v6,OriginalAimWindow.returned,OriginalAimGuard.pop,BitVec.add_assoc]
      all_goals split <;> simp_all)
    apply X86Routine.Prefix.step (middle := ⟨v6 s 1,f,0x2b842⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,shooter,actor,first,loaded,gate,bits,flagGate,cmp32_zero,logical8,OriginalAimWindow.v0,OriginalAimWindow.v1,OriginalAimWindow.v2,OriginalAimWindow.v3,OriginalAimWindow.v4,OriginalAimWindow.v5,OriginalAimWindow.v6,OriginalAimWindow.returned,OriginalAimGuard.pop,BitVec.add_assoc]
      all_goals split <;> simp_all)
    apply X86Routine.Prefix.step (middle := returned s 1 f) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,shooter,actor,first,loaded,gate,bits,flagGate,cmp32_zero,logical8,OriginalAimWindow.v0,OriginalAimWindow.v1,OriginalAimWindow.v2,OriginalAimWindow.v3,OriginalAimWindow.v4,OriginalAimWindow.v5,OriginalAimWindow.v6,OriginalAimWindow.returned,OriginalAimGuard.pop,BitVec.add_assoc]
      all_goals split <;> simp_all)
    exact .nil _
  exact run.transfer program [] decoded (by simp)

end Doom.Proofs.OriginalAimActorGuard
