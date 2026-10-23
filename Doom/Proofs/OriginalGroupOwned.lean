import Doom.Proofs.OriginalGroupHeap
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalGroupOwned
open Verification X86 X86Memory X86Control BlockSummary
abbrev program := OriginalGroupAllocation.program
def listed : X86Routine.Program
  | 0x39731 => some (.control (.testWord 7 7),2)
  | 0x39733 => some (.control (.jumpZero true 10),2)
  | 0x39735 => some (.control (.block (.legacy (.lea 0 3 24))),3)
  | 0x39738 => some (.control (.block (.store ⟨some 3,none,0,4⟩ 7)),3)
  | 0x3973b => some (.control (.block (.store ⟨some 7,none,0,0⟩ 0)),2)
  | 0x3973d => some (.jump 25,2)
  | 0x39758 => some (.control (.block (.load 2 ⟨none,none,0,0x74fe0⟩)),6)
  | 0x3975e => some (.control (.block (.legacy (.load 0 3 16))),3)
  | 0x39761 => some (.control (.block (.store ⟨some 3,none,0,8⟩ 5)),3)
  | 0x39764 => some (.control (.block (.store ⟨some 2,none,0,28⟩ 0)),3)
  | 0x39767 => some (.control (.block (.legacy (.lea 0 3 24))),3)
  | 0x3976a => some (.storeImmediate ⟨some 3,none,0,12⟩ 0x1d4a11,7)
  | _ => none
theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

/-- Owner publication precedes both later loads, retaining possible aliases. -/
def owned (s : X86Memory.State) :=
  store32 (store32 s.memory (s.regs 3+4) (s.regs 7)) (s.regs 7) (s.regs 3+24)
def zone (s : X86Memory.State) := load32 (owned s) 0x74fe0
def next (s : X86Memory.State) := load32 (owned s) (s.regs 3+16)
def tagged (s : X86Memory.State) := store32 (owned s) (s.regs 3+8) (s.regs 5)
def advanced (s : X86Memory.State) := store32 (tagged s) (zone s+28) (next s)
def committed (s : X86Memory.State) : X86Memory.State :=
  {put (put s 2 (zone s)) 0 (s.regs 3+24) with memory := store32 (advanced s) (s.regs 3+12) 0x1d4a11}
def result (s : X86Memory.State) : X86Control.State :=
  ⟨committed s,some (logical32 (s.regs 7)),0x39771⟩
@[local simp] private theorem step_39731 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x39771] (n+1) ⟨s,f,0x39731⟩=
      (X86Routine.execute (.control (.testWord 7 7)) ⟨s,f,0x39733⟩).bind (X86Routine.run listed [0x39771] n) := by rfl
@[local simp] private theorem step_39733 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x39771] (n+1) ⟨s,f,0x39733⟩=
      (X86Routine.execute (.control (.jumpZero true 10)) ⟨s,f,0x39735⟩).bind (X86Routine.run listed [0x39771] n) := by rfl
@[local simp] private theorem step_39735 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x39771] (n+1) ⟨s,f,0x39735⟩=
      (X86Routine.execute (.control (.block (.legacy (.lea 0 3 24)))) ⟨s,f,0x39738⟩).bind (X86Routine.run listed [0x39771] n) := by rfl
@[local simp] private theorem step_39738 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x39771] (n+1) ⟨s,f,0x39738⟩=
      (X86Routine.execute (.control (.block (.store ⟨some 3,none,0,4⟩ 7))) ⟨s,f,0x3973b⟩).bind (X86Routine.run listed [0x39771] n) := by rfl
@[local simp] private theorem step_3973b (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x39771] (n+1) ⟨s,f,0x3973b⟩=
      (X86Routine.execute (.control (.block (.store ⟨some 7,none,0,0⟩ 0))) ⟨s,f,0x3973d⟩).bind (X86Routine.run listed [0x39771] n) := by rfl
@[local simp] private theorem step_3973d (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x39771] (n+1) ⟨s,f,0x3973d⟩=
      (X86Routine.execute (.jump 25) ⟨s,f,0x3973f⟩).bind (X86Routine.run listed [0x39771] n) := by rfl
@[local simp] private theorem step_39758 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x39771] (n+1) ⟨s,f,0x39758⟩=
      (X86Routine.execute (.control (.block (.load 2 ⟨none,none,0,0x74fe0⟩))) ⟨s,f,0x3975e⟩).bind (X86Routine.run listed [0x39771] n) := by rfl
@[local simp] private theorem step_3975e (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x39771] (n+1) ⟨s,f,0x3975e⟩=
      (X86Routine.execute (.control (.block (.legacy (.load 0 3 16)))) ⟨s,f,0x39761⟩).bind (X86Routine.run listed [0x39771] n) := by rfl
@[local simp] private theorem step_39761 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x39771] (n+1) ⟨s,f,0x39761⟩=
      (X86Routine.execute (.control (.block (.store ⟨some 3,none,0,8⟩ 5))) ⟨s,f,0x39764⟩).bind (X86Routine.run listed [0x39771] n) := by rfl
@[local simp] private theorem step_39764 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x39771] (n+1) ⟨s,f,0x39764⟩=
      (X86Routine.execute (.control (.block (.store ⟨some 2,none,0,28⟩ 0))) ⟨s,f,0x39767⟩).bind (X86Routine.run listed [0x39771] n) := by rfl
@[local simp] private theorem step_39767 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x39771] (n+1) ⟨s,f,0x39767⟩=
      (X86Routine.execute (.control (.block (.legacy (.lea 0 3 24)))) ⟨s,f,0x3976a⟩).bind (X86Routine.run listed [0x39771] n) := by rfl
@[local simp] private theorem step_3976a (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x39771] (n+1) ⟨s,f,0x3976a⟩=
      (X86Routine.execute (.storeImmediate ⟨some 3,none,0,12⟩ 0x1d4a11) ⟨s,f,0x39771⟩).bind (X86Routine.run listed [0x39771] n) := by rfl
@[local simp] private theorem stopped (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x39771] n ⟨s,f,0x39771⟩=some ⟨s,f,0x39771⟩ := by cases n <;> rfl

theorem execution (s : X86Memory.State) (f : Option Flags) (user : s.regs 7≠(0#32)) :
    X86Routine.run program [0x39771] 12 ⟨s,f,0x39731⟩=some (result s) := by
  have run : X86Routine.run listed [0x39771] 12 ⟨s,f,0x39731⟩=some (result s) := by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      X86Block.Address.eval,X86.execute,blockPreservesFlags,result,committed,
      advanced,tagged,owned,zone,next,user,put,write,BitVec.add_assoc]
    funext r
    by_cases h : r=0 <;> simp [write,h]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

def SafeWord (a : Word) (s : X86Memory.State) : Prop :=
  Apart a (s.regs 3+4) ∧ Apart a (s.regs 7) ∧ Apart a (s.regs 3+8) ∧
    Apart a (zone s+28) ∧ Apart a (s.regs 3+12)

theorem frame (s : X86Memory.State) (a : Word) (safe : SafeWord a s) :
    load32 (committed s).memory a=load32 s.memory a := by
  change load32 (store32 (advanced s) (s.regs 3+12) 0x1d4a11) a=_
  unfold advanced tagged owned
  rw [load_store_apart _ _ _ _ safe.2.2.2.2,
    load_store_apart _ _ _ _ safe.2.2.2.1,load_store_apart _ _ _ _ safe.2.2.1,
    load_store_apart _ _ _ _ safe.2.1,load_store_apart _ _ _ _ safe.1]

end Doom.Proofs.OriginalGroupOwned
