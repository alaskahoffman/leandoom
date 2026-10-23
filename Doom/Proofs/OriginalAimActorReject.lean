import Doom.Proofs.E1M1AimActorTopEntry
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalAimActorReject
open Verification X86 X86Memory X86Control BlockSummary
open OriginalAimWindow (v0 v1 v2 v3 v4 v5 v6 returned)
open OriginalAimActorGuard (shooter actor first loaded gate bits flagGate)
attribute [local irreducible] load32 store32
def code : List UInt8 := [0xb8,0x1,0x0,0x0,0x0,0x5d,0x5f,0x5e,0x5a,0x59,0x5b,0xc3]
def bytesProgram (bytes : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2b875≤pc ∧ pc<0x2b881 then X86Routine.decodeAt bytes (pc-0x2b875) else none
def program := bytesProgram code
def listed : X86Routine.Program
  | 0x2b875 => some (.immediate 0 1,5)
  | 0x2b87a => some (.pop 5,1)
  | 0x2b87b => some (.pop 7,1)
  | 0x2b87c => some (.pop 6,1)
  | 0x2b87d => some (.pop 2,1)
  | 0x2b87e => some (.pop 1,1)
  | 0x2b87f => some (.pop 3,1)
  | 0x2b880 => some (.ret,1)
  | _ => none

theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

/-- The original actor top rejection restores six registers and returns true. -/
theorem execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 8 ⟨s,f,0x2b875⟩ (returned s 1 f) := by
  have run : X86Routine.Prefix listed [] 8 ⟨s,f,0x2b875⟩ (returned s 1 f) := by
    apply X86Routine.Prefix.step (middle := ⟨v0 s 1,f,0x2b87a⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,shooter,actor,first,loaded,gate,bits,flagGate,cmp32_zero,logical8,OriginalAimWindow.v0,OriginalAimWindow.v1,OriginalAimWindow.v2,OriginalAimWindow.v3,OriginalAimWindow.v4,OriginalAimWindow.v5,OriginalAimWindow.v6,OriginalAimWindow.returned,OriginalAimGuard.pop,BitVec.add_assoc]
      all_goals split <;> simp_all)
    apply X86Routine.Prefix.step (middle := ⟨v1 s 1,f,0x2b87b⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,shooter,actor,first,loaded,gate,bits,flagGate,cmp32_zero,logical8,OriginalAimWindow.v0,OriginalAimWindow.v1,OriginalAimWindow.v2,OriginalAimWindow.v3,OriginalAimWindow.v4,OriginalAimWindow.v5,OriginalAimWindow.v6,OriginalAimWindow.returned,OriginalAimGuard.pop,BitVec.add_assoc]
      all_goals split <;> simp_all)
    apply X86Routine.Prefix.step (middle := ⟨v2 s 1,f,0x2b87c⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,shooter,actor,first,loaded,gate,bits,flagGate,cmp32_zero,logical8,OriginalAimWindow.v0,OriginalAimWindow.v1,OriginalAimWindow.v2,OriginalAimWindow.v3,OriginalAimWindow.v4,OriginalAimWindow.v5,OriginalAimWindow.v6,OriginalAimWindow.returned,OriginalAimGuard.pop,BitVec.add_assoc]
      all_goals split <;> simp_all)
    apply X86Routine.Prefix.step (middle := ⟨v3 s 1,f,0x2b87d⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,shooter,actor,first,loaded,gate,bits,flagGate,cmp32_zero,logical8,OriginalAimWindow.v0,OriginalAimWindow.v1,OriginalAimWindow.v2,OriginalAimWindow.v3,OriginalAimWindow.v4,OriginalAimWindow.v5,OriginalAimWindow.v6,OriginalAimWindow.returned,OriginalAimGuard.pop,BitVec.add_assoc]
      all_goals split <;> simp_all)
    apply X86Routine.Prefix.step (middle := ⟨v4 s 1,f,0x2b87e⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,shooter,actor,first,loaded,gate,bits,flagGate,cmp32_zero,logical8,OriginalAimWindow.v0,OriginalAimWindow.v1,OriginalAimWindow.v2,OriginalAimWindow.v3,OriginalAimWindow.v4,OriginalAimWindow.v5,OriginalAimWindow.v6,OriginalAimWindow.returned,OriginalAimGuard.pop,BitVec.add_assoc]
      all_goals split <;> simp_all)
    apply X86Routine.Prefix.step (middle := ⟨v5 s 1,f,0x2b87f⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,shooter,actor,first,loaded,gate,bits,flagGate,cmp32_zero,logical8,OriginalAimWindow.v0,OriginalAimWindow.v1,OriginalAimWindow.v2,OriginalAimWindow.v3,OriginalAimWindow.v4,OriginalAimWindow.v5,OriginalAimWindow.v6,OriginalAimWindow.returned,OriginalAimGuard.pop,BitVec.add_assoc]
      all_goals split <;> simp_all)
    apply X86Routine.Prefix.step (middle := ⟨v6 s 1,f,0x2b880⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,shooter,actor,first,loaded,gate,bits,flagGate,cmp32_zero,logical8,OriginalAimWindow.v0,OriginalAimWindow.v1,OriginalAimWindow.v2,OriginalAimWindow.v3,OriginalAimWindow.v4,OriginalAimWindow.v5,OriginalAimWindow.v6,OriginalAimWindow.returned,OriginalAimGuard.pop,BitVec.add_assoc]
      all_goals split <;> simp_all)
    apply X86Routine.Prefix.step (middle := returned s 1 f) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,shooter,actor,first,loaded,gate,bits,flagGate,cmp32_zero,logical8,OriginalAimWindow.v0,OriginalAimWindow.v1,OriginalAimWindow.v2,OriginalAimWindow.v3,OriginalAimWindow.v4,OriginalAimWindow.v5,OriginalAimWindow.v6,OriginalAimWindow.returned,OriginalAimGuard.pop,BitVec.add_assoc]
      all_goals split <;> simp_all)
    exact .nil _
  exact run.transfer program [] decoded (by simp)

end Doom.Proofs.OriginalAimActorReject
