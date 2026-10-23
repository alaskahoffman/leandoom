import Doom.Proofs.OriginalGroupBounds
import Doom.Proofs.OriginalDiv
import Doom.Proofs.DeathStack
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalDivMemory
open Verification X86 X86Memory X86Control BlockSummary

def bytesProgram (code : List UInt8) : X86Routine.Program := fun pc =>
  if 0x1d180≤pc ∧ pc<0x1d1c1 then X86Routine.decodeAt code (pc-0x1d180) else none
def program := bytesProgram Doom19.fixedDivBytes
def listed : X86Routine.Program
  | 0x1d180 => some (.push 3,1)
  | 0x1d181 => some (.push 1,1)
  | 0x1d182 => some (.push 6,1)
  | 0x1d183 => some (.control (.block (.legacy (.mov 1 0))),2)
  | 0x1d185 => some (.control (.block (.legacy (.mov 3 2))),2)
  | 0x1d187 => some (.cdq,1)
  | 0x1d188 => some (.xorRegister 0 2,2)
  | 0x1d18a => some (.control (.block (.arithmetic (.sub 0 2))),2)
  | 0x1d18c => some (.control (.block (.legacy (.mov 6 0))),2)
  | 0x1d18e => some (.control (.block (.legacy (.mov 0 3))),2)
  | 0x1d190 => some (.sar 6 14,3)
  | 0x1d193 => some (.cdq,1)
  | 0x1d194 => some (.xorRegister 0 2,2)
  | 0x1d196 => some (.control (.block (.arithmetic (.sub 0 2))),2)
  | 0x1d198 => some (.compareRegisters 6 0,2)
  | 0x1d19a => some (.jumpSigned 3 21,2)
  | 0x1d19c => some (.xorRegister 3 1,2)
  | 0x1d19e => some (.control (.testWord 3 3),2)
  | 0x1d1a0 => some (.setLess 0,3)
  | 0x1d1a3 => some (.control (.andEax 255),5)
  | 0x1d1a8 => some (.addImmediate 0 2147483647,5)
  | 0x1d1ad => some (.pop 6,1)
  | 0x1d1ae => some (.pop 1,1)
  | 0x1d1af => some (.pop 3,1)
  | 0x1d1b0 => some (.ret,1)
  | 0x1d1b1 => some (.control (.block (.legacy (.mov 0 1))),2)
  | 0x1d1b3 => some (.cdq,1)
  | 0x1d1b4 => some (.shld 2 0 16,4)
  | 0x1d1b8 => some (.control (.block (.legacy (.shl 0 16))),3)
  | 0x1d1bb => some (.signedDivide 3,2)
  | 0x1d1bd => some (.pop 6,1)
  | 0x1d1be => some (.pop 1,1)
  | 0x1d1bf => some (.pop 3,1)
  | 0x1d1c0 => some (.ret,1)
  | _ => none
theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def saved (s : X86Memory.State) :=
  X86Routine.pushWord (X86Routine.pushWord (X86Routine.pushWord s (s.regs 3)) (s.regs 1)) (s.regs 6)
def absBits (a : Word) := (a ^^^ X86ValueRoutine.signMask a)-X86ValueRoutine.signMask a
def guarded (s : X86Memory.State) : X86Control.State :=
  ⟨put (put (put (put (put s 1 (s.regs 0)) 3 (s.regs 2)) 0 (absBits (s.regs 2)))
    2 (X86ValueRoutine.signMask (s.regs 2))) 6 ((absBits (s.regs 0)).sshiftRight 14),
    some (compare32 ((absBits (s.regs 0)).sshiftRight 14) (absBits (s.regs 2))),
    if divGuard (s.regs 0) (s.regs 2) then 0x1d1b1 else 0x1d19c⟩
def saturated (s : X86Memory.State) : X86Control.State :=
  ⟨put (put s 3 (s.regs 3 ^^^ s.regs 1)) 0
    ((if (s.regs 3 ^^^ s.regs 1).toInt<0 then 1 else 0)+2147483647),none,0x1d1ad⟩
def quotient (s : X86Memory.State) := (divDividend (s.regs 1)).tdiv (s.regs 3).toInt
def DivSafe (s : X86Memory.State) : Prop :=
  (s.regs 3).toInt≠0 ∧ -2147483648≤quotient s ∧ quotient s≤2147483647
def divided (s : X86Memory.State) : X86Control.State :=
  ⟨put (put s 0 (BitVec.ofInt 32 (quotient s))) 2
    (BitVec.ofInt 32 ((divDividend (s.regs 1)).tmod (s.regs 3).toInt)),none,0x1d1bd⟩
def restored (s : X86Memory.State) (f : Option Flags) : X86Control.State :=
  ⟨put (put (put (put s 6 (load32 s.memory (s.regs 4)))
    1 (load32 s.memory (s.regs 4+4))) 3 (load32 s.memory (s.regs 4+8))) 4 (s.regs 4+16),
    f,(load32 s.memory (s.regs 4+12)).toNat⟩

private theorem logical_lt (v : Word) : ((logical32 v).sign != (logical32 v).overflow) = decide (v.toInt<0) := by
  have h : logical32 v=compare32 v 0 := by simp [logical32,compare32,BitVec.ult_eq_decide]
  rw [h,PlayerArmor.cmp_lt]
  rfl
private theorem byte_mask (v w : Word) :
    ((v &&& (0xffffff00#32)) ||| w) &&& (255#32)=w &&& (255#32) := by
  rw [BitVec.and_or_distrib_right,BitVec.and_assoc]
  simp
@[local simp] private theorem step_0 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x1d183] (n+1) ⟨s,f,0x1d180⟩ =
      (X86Routine.execute (.push 3) ⟨s,f,0x1d181⟩).bind (X86Routine.run listed [0x1d183] n) := by simp [X86Routine.run,listed]
@[local simp] private theorem step_1 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x1d183] (n+1) ⟨s,f,0x1d181⟩ =
      (X86Routine.execute (.push 1) ⟨s,f,0x1d182⟩).bind (X86Routine.run listed [0x1d183] n) := by simp [X86Routine.run,listed]
@[local simp] private theorem step_2 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x1d183] (n+1) ⟨s,f,0x1d182⟩ =
      (X86Routine.execute (.push 6) ⟨s,f,0x1d183⟩).bind (X86Routine.run listed [0x1d183] n) := by simp [X86Routine.run,listed]
@[local simp] private theorem stop_save_3 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x1d183] n ⟨s,f,0x1d183⟩=some ⟨s,f,0x1d183⟩ := by cases n <;> rfl
theorem save_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x1d183] 3 ⟨s,f,0x1d180⟩=some (⟨saved s,f,0x1d183⟩) := by
  have run : X86Routine.run listed [0x1d183] 3 ⟨s,f,0x1d180⟩=some (⟨saved s,f,0x1d183⟩) := by
    all_goals simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      X86Block.Address.eval,blockPreservesFlags,X86.execute,put,write,eax,saved,guarded,saturated,divided,
      X86Routine.pushWord,
      BitVec.add_assoc,-BitVec.toInt_add,-BitVec.toInt_xor]
    all_goals
      funext r
      by_cases h0 : r=0 <;> by_cases h1 : r=1 <;> by_cases h2 : r=2 <;>
        by_cases h3 : r=3 <;> by_cases h4 : r=4 <;> by_cases h6 : r=6 <;> simp [write,eax,h0,h1,h2,h3,h4,h6]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]
@[local simp] private theorem step_3 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x1d1b1,0x1d19c] (n+1) ⟨s,f,0x1d183⟩ =
      (X86Routine.execute (.control (.block (.legacy (.mov 1 0)))) ⟨s,f,0x1d185⟩).bind (X86Routine.run listed [0x1d1b1,0x1d19c] n) := by simp [X86Routine.run,listed]
@[local simp] private theorem step_5 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x1d1b1,0x1d19c] (n+1) ⟨s,f,0x1d185⟩ =
      (X86Routine.execute (.control (.block (.legacy (.mov 3 2)))) ⟨s,f,0x1d187⟩).bind (X86Routine.run listed [0x1d1b1,0x1d19c] n) := by simp [X86Routine.run,listed]
@[local simp] private theorem step_7 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x1d1b1,0x1d19c] (n+1) ⟨s,f,0x1d187⟩ =
      (X86Routine.execute (.cdq) ⟨s,f,0x1d188⟩).bind (X86Routine.run listed [0x1d1b1,0x1d19c] n) := by simp [X86Routine.run,listed]
@[local simp] private theorem step_8 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x1d1b1,0x1d19c] (n+1) ⟨s,f,0x1d188⟩ =
      (X86Routine.execute (.xorRegister 0 2) ⟨s,f,0x1d18a⟩).bind (X86Routine.run listed [0x1d1b1,0x1d19c] n) := by simp [X86Routine.run,listed]
@[local simp] private theorem step_a (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x1d1b1,0x1d19c] (n+1) ⟨s,f,0x1d18a⟩ =
      (X86Routine.execute (.control (.block (.arithmetic (.sub 0 2)))) ⟨s,f,0x1d18c⟩).bind (X86Routine.run listed [0x1d1b1,0x1d19c] n) := by simp [X86Routine.run,listed]
@[local simp] private theorem step_c (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x1d1b1,0x1d19c] (n+1) ⟨s,f,0x1d18c⟩ =
      (X86Routine.execute (.control (.block (.legacy (.mov 6 0)))) ⟨s,f,0x1d18e⟩).bind (X86Routine.run listed [0x1d1b1,0x1d19c] n) := by simp [X86Routine.run,listed]
@[local simp] private theorem step_e (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x1d1b1,0x1d19c] (n+1) ⟨s,f,0x1d18e⟩ =
      (X86Routine.execute (.control (.block (.legacy (.mov 0 3)))) ⟨s,f,0x1d190⟩).bind (X86Routine.run listed [0x1d1b1,0x1d19c] n) := by simp [X86Routine.run,listed]
@[local simp] private theorem step_10 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x1d1b1,0x1d19c] (n+1) ⟨s,f,0x1d190⟩ =
      (X86Routine.execute (.sar 6 14) ⟨s,f,0x1d193⟩).bind (X86Routine.run listed [0x1d1b1,0x1d19c] n) := by simp [X86Routine.run,listed]
@[local simp] private theorem step_13 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x1d1b1,0x1d19c] (n+1) ⟨s,f,0x1d193⟩ =
      (X86Routine.execute (.cdq) ⟨s,f,0x1d194⟩).bind (X86Routine.run listed [0x1d1b1,0x1d19c] n) := by simp [X86Routine.run,listed]
@[local simp] private theorem step_14 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x1d1b1,0x1d19c] (n+1) ⟨s,f,0x1d194⟩ =
      (X86Routine.execute (.xorRegister 0 2) ⟨s,f,0x1d196⟩).bind (X86Routine.run listed [0x1d1b1,0x1d19c] n) := by simp [X86Routine.run,listed]
@[local simp] private theorem step_16 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x1d1b1,0x1d19c] (n+1) ⟨s,f,0x1d196⟩ =
      (X86Routine.execute (.control (.block (.arithmetic (.sub 0 2)))) ⟨s,f,0x1d198⟩).bind (X86Routine.run listed [0x1d1b1,0x1d19c] n) := by simp [X86Routine.run,listed]
@[local simp] private theorem step_18 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x1d1b1,0x1d19c] (n+1) ⟨s,f,0x1d198⟩ =
      (X86Routine.execute (.compareRegisters 6 0) ⟨s,f,0x1d19a⟩).bind (X86Routine.run listed [0x1d1b1,0x1d19c] n) := by simp [X86Routine.run,listed]
@[local simp] private theorem step_1a (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x1d1b1,0x1d19c] (n+1) ⟨s,f,0x1d19a⟩ =
      (X86Routine.execute (.jumpSigned 3 21) ⟨s,f,0x1d19c⟩).bind (X86Routine.run listed [0x1d1b1,0x1d19c] n) := by simp [X86Routine.run,listed]
@[local simp] private theorem stop_guard_31 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x1d1b1,0x1d19c] n ⟨s,f,0x1d1b1⟩=some ⟨s,f,0x1d1b1⟩ := by cases n <;> rfl
@[local simp] private theorem stop_guard_1c (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x1d1b1,0x1d19c] n ⟨s,f,0x1d19c⟩=some ⟨s,f,0x1d19c⟩ := by cases n <;> rfl
theorem guard_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x1d1b1,0x1d19c] 13 ⟨s,f,0x1d183⟩=some (guarded s) := by
  have run : X86Routine.run listed [0x1d1b1,0x1d19c] 13 ⟨s,f,0x1d183⟩=some (guarded s) := by
    by_cases h : divGuard (s.regs 0) (s.regs 2)
    all_goals simp [divGuard,X86ValueRoutine.signMask,-Int.not_lt,-BitVec.toInt_xor] at h
    all_goals simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      X86Block.Address.eval,blockPreservesFlags,X86.execute,put,write,eax,saved,guarded,saturated,divided,
      divGuard,absBits,PlayerHeight.cmp_ge_prop,← Int.not_lt,X86ValueRoutine.signMask,h,
      BitVec.add_assoc,-BitVec.toInt_add,-BitVec.toInt_xor]
    all_goals
      funext r
      by_cases h0 : r=0 <;> by_cases h1 : r=1 <;> by_cases h2 : r=2 <;>
        by_cases h3 : r=3 <;> by_cases h4 : r=4 <;> by_cases h6 : r=6 <;> simp [write,eax,h0,h1,h2,h3,h4,h6]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]
@[local simp] private theorem step_1c (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x1d1ad] (n+1) ⟨s,f,0x1d19c⟩ =
      (X86Routine.execute (.xorRegister 3 1) ⟨s,f,0x1d19e⟩).bind (X86Routine.run listed [0x1d1ad] n) := by simp [X86Routine.run,listed]
@[local simp] private theorem step_1e (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x1d1ad] (n+1) ⟨s,f,0x1d19e⟩ =
      (X86Routine.execute (.control (.testWord 3 3)) ⟨s,f,0x1d1a0⟩).bind (X86Routine.run listed [0x1d1ad] n) := by simp [X86Routine.run,listed]
@[local simp] private theorem step_20 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x1d1ad] (n+1) ⟨s,f,0x1d1a0⟩ =
      (X86Routine.execute (.setLess 0) ⟨s,f,0x1d1a3⟩).bind (X86Routine.run listed [0x1d1ad] n) := by simp [X86Routine.run,listed]
@[local simp] private theorem step_23 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x1d1ad] (n+1) ⟨s,f,0x1d1a3⟩ =
      (X86Routine.execute (.control (.andEax 255)) ⟨s,f,0x1d1a8⟩).bind (X86Routine.run listed [0x1d1ad] n) := by simp [X86Routine.run,listed]
@[local simp] private theorem step_28 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x1d1ad] (n+1) ⟨s,f,0x1d1a8⟩ =
      (X86Routine.execute (.addImmediate 0 2147483647) ⟨s,f,0x1d1ad⟩).bind (X86Routine.run listed [0x1d1ad] n) := by simp [X86Routine.run,listed]
@[local simp] private theorem stop_saturation_2d (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x1d1ad] n ⟨s,f,0x1d1ad⟩=some ⟨s,f,0x1d1ad⟩ := by cases n <;> rfl
theorem saturation_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x1d1ad] 5 ⟨s,f,0x1d19c⟩=some (saturated s) := by
  have run : X86Routine.run listed [0x1d1ad] 5 ⟨s,f,0x1d19c⟩=some (saturated s) := by
    by_cases neg : (s.regs 3 ^^^ s.regs 1).toInt<0
    all_goals simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      X86Block.Address.eval,blockPreservesFlags,X86.execute,put,write,eax,saved,guarded,saturated,divided,
      logical_lt,PlayerHealth.logical_ge,←Int.not_lt,neg,putByte,byteReg,byte_mask,BitVec.and_assoc,
      BitVec.add_assoc,-BitVec.toInt_add,-BitVec.toInt_xor]
    all_goals
      funext r
      by_cases h0 : r=0 <;> by_cases h1 : r=1 <;> by_cases h2 : r=2 <;>
        by_cases h3 : r=3 <;> by_cases h4 : r=4 <;> by_cases h6 : r=6 <;> simp [write,eax,h0,h1,h2,h3,h4,h6]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]
@[local simp] private theorem step_31 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x1d1bd] (n+1) ⟨s,f,0x1d1b1⟩ =
      (X86Routine.execute (.control (.block (.legacy (.mov 0 1)))) ⟨s,f,0x1d1b3⟩).bind (X86Routine.run listed [0x1d1bd] n) := by simp [X86Routine.run,listed]
@[local simp] private theorem step_33 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x1d1bd] (n+1) ⟨s,f,0x1d1b3⟩ =
      (X86Routine.execute (.cdq) ⟨s,f,0x1d1b4⟩).bind (X86Routine.run listed [0x1d1bd] n) := by simp [X86Routine.run,listed]
@[local simp] private theorem step_34 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x1d1bd] (n+1) ⟨s,f,0x1d1b4⟩ =
      (X86Routine.execute (.shld 2 0 16) ⟨s,f,0x1d1b8⟩).bind (X86Routine.run listed [0x1d1bd] n) := by simp [X86Routine.run,listed]
@[local simp] private theorem step_38 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x1d1bd] (n+1) ⟨s,f,0x1d1b8⟩ =
      (X86Routine.execute (.control (.block (.legacy (.shl 0 16)))) ⟨s,f,0x1d1bb⟩).bind (X86Routine.run listed [0x1d1bd] n) := by simp [X86Routine.run,listed]
@[local simp] private theorem step_3b (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x1d1bd] (n+1) ⟨s,f,0x1d1bb⟩ =
      (X86Routine.execute (.signedDivide 3) ⟨s,f,0x1d1bd⟩).bind (X86Routine.run listed [0x1d1bd] n) := by simp [X86Routine.run,listed]
@[local simp] private theorem stop_division_3d (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x1d1bd] n ⟨s,f,0x1d1bd⟩=some ⟨s,f,0x1d1bd⟩ := by cases n <;> rfl
theorem division_execution (s : X86Memory.State) (f : Option Flags) (safe : DivSafe s) :
    X86Routine.run program [0x1d1bd] 5 ⟨s,f,0x1d1b1⟩=some (divided s) := by
  have run : X86Routine.run listed [0x1d1bd] 5 ⟨s,f,0x1d1b1⟩=some (divided s) := by
    have good := safe
    simp [DivSafe,quotient,divDividend,X86ValueRoutine.signMask] at good
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      X86Block.Address.eval,blockPreservesFlags,X86.execute,put,write,eax,divided,
      quotient,divDividend,X86ValueRoutine.signMask,good.1,Int.not_lt.mpr good.2.1,Int.not_lt.mpr good.2.2,
      BitVec.add_assoc,-BitVec.toInt_add,-BitVec.toInt_xor]
    funext r
    by_cases h0 : r=0 <;> by_cases h2 : r=2 <;> simp [write,eax,h0,h2]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

@[simp] theorem saved_reg (s : X86Memory.State) (r : Reg) (h : r≠4) :
    (saved s).regs r=s.regs r := by simp [saved,X86Routine.pushWord,put,write,h]
@[simp] theorem saved_sp (s : X86Memory.State) : (saved s).regs 4=s.regs 4-12 := by
  simp [saved,X86Routine.pushWord,put,write,BitVec.sub_sub]
theorem saved_memory (s : X86Memory.State) : (saved s).memory=
    store32 (store32 (store32 s.memory (s.regs 4-4) (s.regs 3))
      (s.regs 4-8) (s.regs 1)) (s.regs 4-12) (s.regs 6) := by
  simp [saved,X86Routine.pushWord,put,write,BitVec.sub_sub]
theorem saved_reads (s : X86Memory.State) :
    load32 (saved s).memory (s.regs 4-12)=s.regs 6 ∧
    load32 (saved s).memory (s.regs 4-8)=s.regs 1 ∧
    load32 (saved s).memory (s.regs 4-4)=s.regs 3 ∧
    load32 (saved s).memory (s.regs 4)=load32 s.memory (s.regs 4) := by
  have apart (i j : Fin 4) (h : i≠j) :
      Apart (s.regs 4-BitVec.ofNat 32 (4*i.val)) (s.regs 4-BitVec.ofNat 32 (4*j.val)) :=
    DeathStack.slots_apart _ ⟨i.val,by omega⟩ ⟨j.val,by omega⟩ (by intro eq; apply h; exact Fin.ext (congrArg (fun x : Fin 32 => x.val) eq))
  have a23 : Apart (s.regs 4-8) (s.regs 4-12) := apart 2 3 (by decide)
  have a13 : Apart (s.regs 4-4) (s.regs 4-12) := apart 1 3 (by decide)
  have a12 : Apart (s.regs 4-4) (s.regs 4-8) := apart 1 2 (by decide)
  have a03 : Apart (s.regs 4) (s.regs 4-12) := by
    have h := apart 0 3 (by decide)
    change Apart (s.regs 4-(0#32)) (s.regs 4-(12#32)) at h
    simpa using h
  have a02 : Apart (s.regs 4) (s.regs 4-8) := by simpa using apart 0 2 (by decide)
  have a01 : Apart (s.regs 4) (s.regs 4-4) := by simpa using apart 0 1 (by decide)
  rw [saved_memory]
  simp only [load_store,load_store_apart _ _ _ _ a23,load_store_apart _ _ _ _ a13,
    load_store_apart _ _ _ _ a12,load_store_apart _ _ _ _ a03,
    load_store_apart _ _ _ _ a02,load_store_apart _ _ _ _ a01,and_self]

theorem saved_frame (s : X86Memory.State) (a : Word)
    (safe : ∀ off∈[(4#32),8,12], Apart a (s.regs 4-off)) :
    load32 (saved s).memory a=load32 s.memory a := by
  rw [saved_memory,load_store_apart _ _ _ _ (safe 12 (by simp)),
    load_store_apart _ _ _ _ (safe 8 (by simp)),load_store_apart _ _ _ _ (safe 4 (by simp))]

/-- Restore reads only the three saved slots and the caller's return word.
The slots remain distinct even when the stack wraps through address zero. -/
theorem restored_saved (s t : X86Memory.State) (f : Option Flags)
    (mem : t.memory=(saved s).memory) (sp : t.regs 4=s.regs 4-12) :
    (restored t f).core.regs 6=s.regs 6 ∧
    (restored t f).core.regs 1=s.regs 1 ∧
    (restored t f).core.regs 3=s.regs 3 ∧
    (restored t f).core.regs 4=s.regs 4+4 ∧
    (restored t f).pc=(load32 s.memory (s.regs 4)).toNat := by
  have reads := saved_reads s
  have h : load32 (saved s).memory (s.regs 4-12)=s.regs 6 ∧
      load32 (saved s).memory (s.regs 4-8)=s.regs 1 ∧
      load32 (saved s).memory (s.regs 4-4)=s.regs 3 ∧
      s.regs 4+4=s.regs 4+4 ∧
      (load32 (saved s).memory (s.regs 4)).toNat=(load32 s.memory (s.regs 4)).toNat :=
    ⟨reads.1,reads.2.1,reads.2.2.1,rfl,congrArg BitVec.toNat reads.2.2.2⟩
  simpa [restored,put,write,mem,sp,BitVec.sub_eq_add_neg,BitVec.add_assoc] using h

def popped (s : X86Memory.State) : X86Memory.State :=
  put (put (put (put s 6 (load32 s.memory (s.regs 4)))
    1 (load32 s.memory (s.regs 4+4))) 3 (load32 s.memory (s.regs 4+8))) 4 (s.regs 4+12)

theorem pops_execution (s : X86Memory.State) (f : Option Flags) (normal : Bool) :
    X86Routine.run program [if normal then 0x1d1c0 else 0x1d1b0] 3
      ⟨s,f,if normal then 0x1d1bd else 0x1d1ad⟩ =
      some ⟨popped s,f,if normal then 0x1d1c0 else 0x1d1b0⟩ := by
  have run : X86Routine.run listed [if normal then 0x1d1c0 else 0x1d1b0] 3
      ⟨s,f,if normal then 0x1d1bd else 0x1d1ad⟩ =
      some ⟨popped s,f,if normal then 0x1d1c0 else 0x1d1b0⟩ := by
    cases normal <;> simp [X86Routine.run,listed,X86Routine.execute,popped,put,write,BitVec.add_assoc]
    all_goals
      funext r
      by_cases h1 : r=1 <;> by_cases h3 : r=3 <;> by_cases h4 : r=4 <;>
        by_cases h6 : r=6 <;> simp [write,h1,h3,h4,h6]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

theorem return_path (s : X86Memory.State) (f : Option Flags) (normal : Bool) :
    ∃ n≤4, X86Routine.Prefix program [] n
      ⟨s,f,if normal then 0x1d1bd else 0x1d1ad⟩ (restored s f) := by
  obtain ⟨n,hn,path,_⟩ := X86Routine.run_path (pops_execution s f normal)
  have path := path.transfer program [] (fun _ _ => rfl) (by simp)
  have ret : X86Routine.Prefix program [] 1
      ⟨popped s,f,if normal then 0x1d1c0 else 0x1d1b0⟩ (restored s f) := by
    apply X86Routine.Prefix.step (op := .ret) (length := 1) (middle := restored s f) (by simp)
    · change program (if normal then 0x1d1c0 else 0x1d1b0)=some (.ret,1)
      cases normal <;> decide +kernel
    · simp [X86Routine.execute,popped,restored,put,write,BitVec.add_assoc]
      funext r
      by_cases h : r=4 <;> simp [write,h]
    · exact X86Routine.Prefix.nil _
  exact ⟨n+1,by omega,OriginalGroupBounds.prefix_join path ret⟩

/-- The IDIV guard is a concrete arithmetic condition, not a callee-summary
assumption. Saturation needs no extra condition. -/
def Safe (s : X86Memory.State) : Prop :=
  divGuard (s.regs 0) (s.regs 2) → DivSafe (guarded (saved s)).core
def body (s : X86Memory.State) :=
  if divGuard (s.regs 0) (s.regs 2) then divided (guarded (saved s)).core
  else saturated (guarded (saved s)).core
def result (s : X86Memory.State) := restored (body s).core none

/-- Every successful operand pair, through the original RET and real stack
writes. Return targets may be arbitrary, including addresses within this code. -/
theorem execution_path (s : X86Memory.State) (f : Option Flags) (safe : Safe s) :
    ∃ n≤25, X86Routine.Prefix program [] n ⟨s,f,0x1d180⟩ (result s) := by
  obtain ⟨a,ha,pa,_⟩ := X86Routine.run_path (save_execution s f)
  have pa := pa.transfer program [] (fun _ _ => rfl) (by simp)
  obtain ⟨b,hb,pb,_⟩ := X86Routine.run_path (guard_execution (saved s) f)
  have pb := pb.transfer program [] (fun _ _ => rfl) (by simp)
  have start := OriginalGroupBounds.prefix_join pa pb
  by_cases g : divGuard (s.regs 0) (s.regs 2)
  · obtain ⟨c,hc,pc,_⟩ := X86Routine.run_path
      (division_execution (guarded (saved s)).core (guarded (saved s)).flags (safe g))
    have pc := pc.transfer program [] (fun _ _ => rfl) (by simp)
    have guardPc : (guarded (saved s)).pc=0x1d1b1 := by simp [guarded,saved_reg,g]
    have same : (⟨(guarded (saved s)).core,(guarded (saved s)).flags,0x1d1b1⟩ : X86Control.State)=guarded (saved s) := by rw [←guardPc]
    rw [same] at pc
    obtain ⟨d,hd,pd⟩ := return_path (divided (guarded (saved s)).core).core none true
    exact ⟨a+b+c+d,by omega,by simpa only [result,body,if_pos g] using
      OriginalGroupBounds.prefix_join (OriginalGroupBounds.prefix_join start pc) pd⟩
  · obtain ⟨c,hc,pc,_⟩ := X86Routine.run_path
      (saturation_execution (guarded (saved s)).core (guarded (saved s)).flags)
    have pc := pc.transfer program [] (fun _ _ => rfl) (by simp)
    have guardPc : (guarded (saved s)).pc=0x1d19c := by simp [guarded,saved_reg,g]
    have same : (⟨(guarded (saved s)).core,(guarded (saved s)).flags,0x1d19c⟩ : X86Control.State)=guarded (saved s) := by rw [←guardPc]
    rw [same] at pc
    obtain ⟨d,hd,pd⟩ := return_path (saturated (guarded (saved s)).core).core none false
    exact ⟨a+b+c+d,by omega,by simpa only [result,body,if_neg g] using
      OriginalGroupBounds.prefix_join (OriginalGroupBounds.prefix_join start pc) pd⟩

@[simp] theorem body_memory (s : X86Memory.State) : (body s).core.memory=(saved s).memory := by
  unfold body
  split <;> rfl
@[simp] theorem body_sp (s : X86Memory.State) : (body s).core.regs 4=s.regs 4-12 := by
  unfold body
  split <;> simp [divided,saturated,guarded,put,write,saved_sp]
theorem restored_registers (s : X86Memory.State) :
    (result s).core.regs 6=s.regs 6 ∧ (result s).core.regs 1=s.regs 1 ∧
    (result s).core.regs 3=s.regs 3 ∧ (result s).core.regs 4=s.regs 4+4 ∧
    (result s).pc=(load32 s.memory (s.regs 4)).toNat :=
  restored_saved s (body s).core none (body_memory s) (body_sp s)

def answer (a b : Word) : Word :=
  if divGuard a b then BitVec.ofInt 32 ((divDividend a).tdiv b.toInt)
  else (if (b ^^^ a).toInt<0 then 1 else 0)+2147483647

theorem result_value (s : X86Memory.State) : (result s).core.regs 0=answer (s.regs 0) (s.regs 2) := by
  unfold result body answer
  split <;> simp [restored,divided,saturated,guarded,quotient,put,write,saved_reg]

theorem safe_iff (s : X86Memory.State) : Safe s ↔
    (divGuard (s.regs 0) (s.regs 2) → (s.regs 2).toInt≠0 ∧
      -2147483648≤(divDividend (s.regs 0)).tdiv (s.regs 2).toInt ∧
      (divDividend (s.regs 0)).tdiv (s.regs 2).toInt≤2147483647) := by
  simp [Safe,DivSafe,quotient,guarded,put,write,saved_reg]

/-- Reuses the previously proved arithmetic equality; only the concrete
stack/register implementation is new. -/
theorem result_matches_fixed (s : X86Memory.State) (safe : Safe s) :
    (Fixed.divChecked ⟨Int32.ofBitVec (s.regs 0)⟩ ⟨Int32.ofBitVec (s.regs 2)⟩).toOption.map
      (fun v => v.raw.toBitVec) = some ((result s).core.regs 0) := by
  have arithmetic := div_execution (⟨Int32.ofBitVec (s.regs 0)⟩ : Fixed) (⟨Int32.ofBitVec (s.regs 2)⟩ : Fixed)
  rw [div_program_matches] at arithmetic
  simp only [Int32.toBitVec_ofBitVec,Int32.toInt_ofBitVec,Option.some.injEq] at arithmetic
  have successful : divisionAnswer (Fixed.divChecked ⟨Int32.ofBitVec (s.regs 0)⟩ ⟨Int32.ofBitVec (s.regs 2)⟩)=
      .ok (answer (s.regs 0) (s.regs 2)) := by
    rw [arithmetic]
    unfold answer
    by_cases g : divGuard (s.regs 0) (s.regs 2)
    · have good := (safe_iff s).mp safe g
      simp [g,good.1,Int.not_lt.mpr good.2.1,Int.not_lt.mpr good.2.2]
    · simp [g]
  rw [result_value]
  cases h : Fixed.divChecked ⟨Int32.ofBitVec (s.regs 0)⟩ ⟨Int32.ofBitVec (s.regs 2)⟩ with
  | ok v =>
    simp only [h,Except.toOption,Option.map_some,Option.some.injEq]
    simpa only [h,divisionAnswer,Except.ok.injEq] using successful
  | error e => cases e <;> simp [h,divisionAnswer] at successful

theorem result_frame (s : X86Memory.State) (a : Word)
    (safe : ∀ off∈[(4#32),8,12], Apart a (s.regs 4-off)) :
    load32 (result s).core.memory a=load32 s.memory a := by
  change load32 (body s).core.memory a=_
  rw [body_memory]
  exact saved_frame s a safe

/-- Successful engine arithmetic discharges the machine's IDIV condition. -/
theorem safe_of_fixed_success (s : X86Memory.State)
    (ok : (Fixed.divChecked ⟨Int32.ofBitVec (s.regs 0)⟩ ⟨Int32.ofBitVec (s.regs 2)⟩).isOk=true) : Safe s := by
  apply (safe_iff s).mpr
  intro g
  have arithmetic := div_execution (⟨Int32.ofBitVec (s.regs 0)⟩ : Fixed) (⟨Int32.ofBitVec (s.regs 2)⟩ : Fixed)
  rw [div_program_matches] at arithmetic
  simp only [Int32.toBitVec_ofBitVec,Int32.toInt_ofBitVec,Option.some.injEq,if_pos g] at arithmetic
  cases h : Fixed.divChecked ⟨Int32.ofBitVec (s.regs 0)⟩ ⟨Int32.ofBitVec (s.regs 2)⟩ with
  | error e => simp [h,Except.isOk,Except.toBool] at ok
  | ok v =>
    simp only [h,divisionAnswer] at arithmetic
    by_cases zero : (s.regs 2).toInt=0
    · simp [zero] at arithmetic
    · by_cases overflow : (divDividend (s.regs 0)).tdiv (s.regs 2).toInt < -2147483648 ∨
          2147483647 < (divDividend (s.regs 0)).tdiv (s.regs 2).toInt
      · simp [zero,overflow] at arithmetic
      · exact ⟨zero,by omega,by omega⟩

end Doom.Proofs.OriginalDivMemory
