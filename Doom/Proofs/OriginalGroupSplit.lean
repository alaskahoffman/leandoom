import Doom.Proofs.OriginalGroupHandoff
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalGroupSplit
open Verification X86 X86Memory X86Control BlockSummary
def splitBytes : List UInt8 := [0x83,0x7b,0x4,0x0,0x75,0xbf,0x8b,0x3,0x39,0xc1,0x7f,0xb9,0x89,0xc2,0x29,0xca,0x83,0xfa,0x40,0x7e,0x24,0x8d,0x4,0xb,0xc7,0x40,0x4,0x0,0x0,0x0,0x0,0xc7,0x40,0x8,0x0,0x0,0x0,0x0,0x89,0x10,0x89,0x58,0x14,0x8b,0x53,0x10,0x89,0x50,0x10,0x89,0x42,0x14,0x89,0x43,0x10,0x89,0xb]
def bytesProgram (code : List UInt8) : X86Routine.Program := fun pc =>
  if 0x396f8≤pc ∧ pc<0x39731 then X86Routine.decodeAt code (pc-0x396f8) else none
def program := bytesProgram splitBytes
def listed : X86Routine.Program
  | 0x396f8 => some (.control (.cmpImmediate ⟨some 3,none,0,4⟩ 0),4)
  | 0x396fc => some (.control (.jumpZero false (-65)),2)
  | 0x396fe => some (.control (.block (.legacy (.load 0 3 0))),2)
  | 0x39700 => some (.compareRegisters 1 0,2)
  | 0x39702 => some (.jumpSigned 2 (-71),2)
  | 0x39704 => some (.control (.block (.legacy (.mov 2 0))),2)
  | 0x39706 => some (.control (.block (.arithmetic (.sub 2 1))),2)
  | 0x39708 => some (.compareRegister 2 64,3)
  | 0x3970b => some (.jumpSigned 1 36,2)
  | 0x3970d => some (.control (.block (.lea 0 ⟨some 3,some 1,0,0⟩)),3)
  | 0x39710 => some (.storeImmediate ⟨some 0,none,0,4⟩ 0,7)
  | 0x39717 => some (.storeImmediate ⟨some 0,none,0,8⟩ 0,7)
  | 0x3971e => some (.control (.block (.store ⟨some 0,none,0,0⟩ 2)),2)
  | 0x39720 => some (.control (.block (.store ⟨some 0,none,0,20⟩ 3)),3)
  | 0x39723 => some (.control (.block (.legacy (.load 2 3 16))),3)
  | 0x39726 => some (.control (.block (.store ⟨some 0,none,0,16⟩ 2)),3)
  | 0x39729 => some (.control (.block (.store ⟨some 2,none,0,20⟩ 0)),3)
  | 0x3972c => some (.control (.block (.store ⟨some 3,none,0,16⟩ 0)),3)
  | 0x3972f => some (.control (.block (.store ⟨some 3,none,0,0⟩ 1)),2)
  | _ => none
theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def candidateSize (s : X86Memory.State) := load32 s.memory (s.regs 3)
def candidate (s : X86Memory.State) : X86Control.State :=
  let owner := load32 s.memory (s.regs 3+4)
  if owner≠0 then ⟨s,some (compare32 owner 0),0x396bd⟩
  else ⟨put s 0 (candidateSize s),some (compare32 (s.regs 1) (candidateSize s)),
    if (candidateSize s).toInt<(s.regs 1).toInt then 0x396bd else 0x39704⟩
/-- Wrapping subtraction, followed by the original signed comparison. -/
def extra (s : X86Memory.State) := s.regs 0-s.regs 1
def remainder (s : X86Memory.State) := s.regs 3+s.regs 1
def freeHeader (s : X86Memory.State) :=
  store32 (store32 (store32 (store32 s.memory (remainder s+4) 0)
    (remainder s+8) 0) (remainder s) (extra s)) (remainder s+20) (s.regs 3)
/-- This load occurs after four writes; aliasing is retained in the summary. -/
def successor (s : X86Memory.State) := load32 (freeHeader s) (s.regs 3+16)
def linked (s : X86Memory.State) :=
  store32 (store32 (store32 (store32 (freeHeader s) (remainder s+16) (successor s))
    (successor s+20) (remainder s)) (s.regs 3+16) (remainder s)) (s.regs 3) (s.regs 1)
def result (s : X86Memory.State) : X86Control.State :=
  if (extra s).toInt≤64 then ⟨put s 2 (extra s),some (compare32 (extra s) 64),0x39731⟩
  else ⟨{put (put s 0 (remainder s)) 2 (successor s) with memory:=linked s},
    some (compare32 (extra s) 64),0x39731⟩
@[local simp] private theorem step_396f8 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x396bd,0x39704] (n+1) ⟨s,f,0x396f8⟩=
      (X86Routine.execute (.control (.cmpImmediate ⟨some 3,none,0,4⟩ 0)) ⟨s,f,0x396fc⟩).bind (X86Routine.run listed [0x396bd,0x39704] n) := by rfl
@[local simp] private theorem step_396fc (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x396bd,0x39704] (n+1) ⟨s,f,0x396fc⟩=
      (X86Routine.execute (.control (.jumpZero false (-65))) ⟨s,f,0x396fe⟩).bind (X86Routine.run listed [0x396bd,0x39704] n) := by rfl
@[local simp] private theorem step_396fe (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x396bd,0x39704] (n+1) ⟨s,f,0x396fe⟩=
      (X86Routine.execute (.control (.block (.legacy (.load 0 3 0)))) ⟨s,f,0x39700⟩).bind (X86Routine.run listed [0x396bd,0x39704] n) := by rfl
@[local simp] private theorem step_39700 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x396bd,0x39704] (n+1) ⟨s,f,0x39700⟩=
      (X86Routine.execute (.compareRegisters 1 0) ⟨s,f,0x39702⟩).bind (X86Routine.run listed [0x396bd,0x39704] n) := by rfl
@[local simp] private theorem step_39702 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x396bd,0x39704] (n+1) ⟨s,f,0x39702⟩=
      (X86Routine.execute (.jumpSigned 2 (-71)) ⟨s,f,0x39704⟩).bind (X86Routine.run listed [0x396bd,0x39704] n) := by rfl
@[local simp] private theorem stop_396bd (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x396bd,0x39704] n ⟨s,f,0x396bd⟩=some ⟨s,f,0x396bd⟩ := by cases n <;> rfl
@[local simp] private theorem stop_39704 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x396bd,0x39704] n ⟨s,f,0x39704⟩=some ⟨s,f,0x39704⟩ := by cases n <;> rfl
@[local simp] private theorem step_39704 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x39731] (n+1) ⟨s,f,0x39704⟩=
      (X86Routine.execute (.control (.block (.legacy (.mov 2 0)))) ⟨s,f,0x39706⟩).bind (X86Routine.run listed [0x39731] n) := by rfl
@[local simp] private theorem step_39706 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x39731] (n+1) ⟨s,f,0x39706⟩=
      (X86Routine.execute (.control (.block (.arithmetic (.sub 2 1)))) ⟨s,f,0x39708⟩).bind (X86Routine.run listed [0x39731] n) := by rfl
@[local simp] private theorem step_39708 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x39731] (n+1) ⟨s,f,0x39708⟩=
      (X86Routine.execute (.compareRegister 2 64) ⟨s,f,0x3970b⟩).bind (X86Routine.run listed [0x39731] n) := by rfl
@[local simp] private theorem step_3970b (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x39731] (n+1) ⟨s,f,0x3970b⟩=
      (X86Routine.execute (.jumpSigned 1 36) ⟨s,f,0x3970d⟩).bind (X86Routine.run listed [0x39731] n) := by rfl
@[local simp] private theorem step_3970d (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x39731] (n+1) ⟨s,f,0x3970d⟩=
      (X86Routine.execute (.control (.block (.lea 0 ⟨some 3,some 1,0,0⟩))) ⟨s,f,0x39710⟩).bind (X86Routine.run listed [0x39731] n) := by rfl
@[local simp] private theorem step_39710 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x39731] (n+1) ⟨s,f,0x39710⟩=
      (X86Routine.execute (.storeImmediate ⟨some 0,none,0,4⟩ 0) ⟨s,f,0x39717⟩).bind (X86Routine.run listed [0x39731] n) := by rfl
@[local simp] private theorem step_39717 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x39731] (n+1) ⟨s,f,0x39717⟩=
      (X86Routine.execute (.storeImmediate ⟨some 0,none,0,8⟩ 0) ⟨s,f,0x3971e⟩).bind (X86Routine.run listed [0x39731] n) := by rfl
@[local simp] private theorem step_3971e (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x39731] (n+1) ⟨s,f,0x3971e⟩=
      (X86Routine.execute (.control (.block (.store ⟨some 0,none,0,0⟩ 2))) ⟨s,f,0x39720⟩).bind (X86Routine.run listed [0x39731] n) := by rfl
@[local simp] private theorem step_39720 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x39731] (n+1) ⟨s,f,0x39720⟩=
      (X86Routine.execute (.control (.block (.store ⟨some 0,none,0,20⟩ 3))) ⟨s,f,0x39723⟩).bind (X86Routine.run listed [0x39731] n) := by rfl
@[local simp] private theorem step_39723 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x39731] (n+1) ⟨s,f,0x39723⟩=
      (X86Routine.execute (.control (.block (.legacy (.load 2 3 16)))) ⟨s,f,0x39726⟩).bind (X86Routine.run listed [0x39731] n) := by rfl
@[local simp] private theorem step_39726 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x39731] (n+1) ⟨s,f,0x39726⟩=
      (X86Routine.execute (.control (.block (.store ⟨some 0,none,0,16⟩ 2))) ⟨s,f,0x39729⟩).bind (X86Routine.run listed [0x39731] n) := by rfl
@[local simp] private theorem step_39729 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x39731] (n+1) ⟨s,f,0x39729⟩=
      (X86Routine.execute (.control (.block (.store ⟨some 2,none,0,20⟩ 0))) ⟨s,f,0x3972c⟩).bind (X86Routine.run listed [0x39731] n) := by rfl
@[local simp] private theorem step_3972c (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x39731] (n+1) ⟨s,f,0x3972c⟩=
      (X86Routine.execute (.control (.block (.store ⟨some 3,none,0,16⟩ 0))) ⟨s,f,0x3972f⟩).bind (X86Routine.run listed [0x39731] n) := by rfl
@[local simp] private theorem step_3972f (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x39731] (n+1) ⟨s,f,0x3972f⟩=
      (X86Routine.execute (.control (.block (.store ⟨some 3,none,0,0⟩ 1))) ⟨s,f,0x39731⟩).bind (X86Routine.run listed [0x39731] n) := by rfl
@[local simp] private theorem stop_39731 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x39731] n ⟨s,f,0x39731⟩=some ⟨s,f,0x39731⟩ := by cases n <;> rfl
theorem candidate_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x396bd,0x39704] 5 ⟨s,f,0x396f8⟩=some (candidate s) := by
  have run : X86Routine.run listed [0x396bd,0x39704] 5 ⟨s,f,0x396f8⟩=some (candidate s) := by
    by_cases owner : load32 s.memory (s.regs 3+(4#32))=(0#32)
    all_goals by_cases size : (load32 s.memory (s.regs 3)).toInt<(s.regs 1).toInt
    all_goals have opposite : (s.regs 1).toInt≤(load32 s.memory (s.regs 3)).toInt ↔ ¬(load32 s.memory (s.regs 3)).toInt<(s.regs 1).toInt := by omega
    all_goals simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      X86Block.Address.eval,X86.execute,blockPreservesFlags,candidate,candidateSize,
      cmp32_zero,cmp32_signed_le,put,write,owner,size,opposite,-BitVec.toInt_add]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

theorem execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x39731] 14 ⟨s,f,0x39704⟩=some (result s) := by
  have run : X86Routine.run listed [0x39731] 14 ⟨s,f,0x39704⟩=some (result s) := by
    by_cases h : (s.regs 0-s.regs 1).toInt≤64
    all_goals simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      X86Block.Address.eval,X86.execute,blockPreservesFlags,result,extra,remainder,freeHeader,successor,linked,
      cmp32_signed_le,put,write,h,-BitVec.toInt_add,-BitVec.toInt_sub]
    all_goals funext r
    all_goals by_cases h0 : r=0 <;> by_cases h2 : r=2 <;> simp [write,h0,h2]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

def SafeWord (a : Word) (s : X86Memory.State) : Prop :=
  ∀ b∈[remainder s+4,remainder s+8,remainder s,remainder s+20,
    remainder s+16,successor s+20,s.regs 3+16,s.regs 3], Apart a b

theorem frame (s : X86Memory.State) (a : Word) (safe : SafeWord a s) :
    load32 (result s).core.memory a=load32 s.memory a := by
  simp only [SafeWord,List.forall_mem_cons,List.not_mem_nil,false_implies,implies_true,and_true] at safe
  simp only [result]
  split
  · rfl
  · change load32 (linked s) a=_
    unfold linked freeHeader
    rw [load_store_apart _ _ _ _ safe.2.2.2.2.2.2.2,
      load_store_apart _ _ _ _ safe.2.2.2.2.2.2.1,
      load_store_apart _ _ _ _ safe.2.2.2.2.2.1,
      load_store_apart _ _ _ _ safe.2.2.2.2.1,
      load_store_apart _ _ _ _ safe.2.2.2.1,
      load_store_apart _ _ _ _ safe.2.2.1,
      load_store_apart _ _ _ _ safe.2.1,
      load_store_apart _ _ _ _ safe.1]

theorem registers (s : X86Memory.State) (r : Reg) (h0 : r≠0) (h2 : r≠2) :
    (result s).core.regs r=s.regs r := by
  by_cases h : (extra s).toInt≤64 <;> simp [result,h,put,write,h0,h2]
theorem result_pc (s : X86Memory.State) : (result s).pc=0x39731 := by
  simp only [result]; split <;> rfl
/-- Byte accounting is exact modulo 2^32, even before heap-validity assumptions. -/
theorem byte_partition (s : X86Memory.State) : extra s+s.regs 1=s.regs 0 :=
  BitVec.sub_add_cancel _ _
theorem no_split_memory (s : X86Memory.State) (h : (extra s).toInt≤64) :
    (result s).core.memory=s.memory := by simp [result,h,put]
theorem split_memory (s : X86Memory.State) (h : 64<(extra s).toInt) :
    (result s).core.memory=linked s := by
  simp [result,show ¬(extra s).toInt≤64 by omega]
end Doom.Proofs.OriginalGroupSplit
