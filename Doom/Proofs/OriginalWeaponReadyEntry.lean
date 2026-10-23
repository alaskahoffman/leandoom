import Doom.Proofs.E1M1WeaponReadyGate
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.WeaponReadyEntry
open Verification X86 X86Memory X86Control BlockSummary

def code : List UInt8 := [0x53,0x51,0x56,0x57,0x89,0xc1,0x89,0xd7,0x8b,0x0,0x8b,0x50,0x64,0x81,0xfa,0x0,0x6b,0x1,0x0,0x74,0x8,0x81,0xfa,0x1c,0x6b,0x1,0x0,0x75,0xc,0xba,0x95,0x0,0x0,0x0,0x8b,0x1,0xe8,0x87,0x3b,0x0,0x0,0x83,0x79,0x70,0x7,0x75,0x14,0x81,0x3f,0x7c,0x61,0x1,0x0,0x75,0xc,0xba,0xb,0x0,0x0,0x0,0x8b,0x1,0xe8,0x3d,0x20,0x1,0x0]
def bytesProgram (bs : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2d2f0 ≤ pc ∧ pc < 0x2d333 then X86Routine.decodeAt bs (pc-0x2d2f0) else none
def program := bytesProgram code
def listed : X86Routine.Program
  | 0x2d2f0 => some (.push 3,1)
  | 0x2d2f1 => some (.push 1,1)
  | 0x2d2f2 => some (.push 6,1)
  | 0x2d2f3 => some (.push 7,1)
  | 0x2d2f4 => some (.control (.block (.legacy (.mov 1 0))),2)
  | 0x2d2f6 => some (.control (.block (.legacy (.mov 7 2))),2)
  | 0x2d2f8 => some (.control (.block (.legacy (.load 0 0 0))),2)
  | 0x2d2fa => some (.control (.block (.legacy (.load 2 0 100))),3)
  | 0x2d2fd => some (.compareRegister 2 0x16b00,6)
  | 0x2d303 => some (.control (.jumpZero true 8),2)
  | 0x2d305 => some (.compareRegister 2 0x16b1c,6)
  | 0x2d30b => some (.control (.jumpZero false 12),2)
  | 0x2d30d => some (.immediate 2 149,5)
  | 0x2d312 => some (.control (.block (.legacy (.load 0 1 0))),2)
  | 0x2d314 => some (.call 15239,5)
  | 0x2d319 => some (.control (.cmpImmediate ⟨some 1,none,0,112⟩ 7),4)
  | 0x2d31d => some (.control (.jumpZero false 20),2)
  | 0x2d31f => some (.control (.cmpImmediate ⟨some 7,none,0,0⟩ 0x1617c),6)
  | 0x2d325 => some (.control (.jumpZero false 12),2)
  | 0x2d327 => some (.immediate 2 11,5)
  | 0x2d32c => some (.control (.block (.legacy (.load 0 1 0))),2)
  | 0x2d32e => some (.call 73789,5)
  | _ => none

theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide
@[local simp] theorem step_2d2fd (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d30d,0x2d319] (n+1) ⟨s,f,0x2d2fd⟩ =
      (X86Routine.execute (.compareRegister 2 0x16b00) ⟨s,f,0x2d303⟩).bind (X86Routine.run listed [0x2d30d,0x2d319] n) := by rfl
@[local simp] theorem step_2d303 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d30d,0x2d319] (n+1) ⟨s,f,0x2d303⟩ =
      (X86Routine.execute (.control (.jumpZero true 8)) ⟨s,f,0x2d305⟩).bind (X86Routine.run listed [0x2d30d,0x2d319] n) := by rfl
@[local simp] theorem step_2d305 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d30d,0x2d319] (n+1) ⟨s,f,0x2d305⟩ =
      (X86Routine.execute (.compareRegister 2 0x16b1c) ⟨s,f,0x2d30b⟩).bind (X86Routine.run listed [0x2d30d,0x2d319] n) := by rfl
@[local simp] theorem step_2d30b (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d30d,0x2d319] (n+1) ⟨s,f,0x2d30b⟩ =
      (X86Routine.execute (.control (.jumpZero false 12)) ⟨s,f,0x2d30d⟩).bind (X86Routine.run listed [0x2d30d,0x2d319] n) := by rfl
@[local simp] theorem stop_2d30d (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d30d,0x2d319] n ⟨s,f,0x2d30d⟩=some ⟨s,f,0x2d30d⟩ := by cases n <;> rfl
@[local simp] theorem stop_2d319 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d30d,0x2d319] n ⟨s,f,0x2d319⟩=some ⟨s,f,0x2d319⟩ := by cases n <;> rfl
@[local simp] theorem step_2d319 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d333,0x3f370] (n+1) ⟨s,f,0x2d319⟩ =
      (X86Routine.execute (.control (.cmpImmediate ⟨some 1,none,0,112⟩ 7)) ⟨s,f,0x2d31d⟩).bind (X86Routine.run listed [0x2d333,0x3f370] n) := by rfl
@[local simp] theorem step_2d31d (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d333,0x3f370] (n+1) ⟨s,f,0x2d31d⟩ =
      (X86Routine.execute (.control (.jumpZero false 20)) ⟨s,f,0x2d31f⟩).bind (X86Routine.run listed [0x2d333,0x3f370] n) := by rfl
@[local simp] theorem step_2d31f (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d333,0x3f370] (n+1) ⟨s,f,0x2d31f⟩ =
      (X86Routine.execute (.control (.cmpImmediate ⟨some 7,none,0,0⟩ 0x1617c)) ⟨s,f,0x2d325⟩).bind (X86Routine.run listed [0x2d333,0x3f370] n) := by rfl
@[local simp] theorem step_2d325 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d333,0x3f370] (n+1) ⟨s,f,0x2d325⟩ =
      (X86Routine.execute (.control (.jumpZero false 12)) ⟨s,f,0x2d327⟩).bind (X86Routine.run listed [0x2d333,0x3f370] n) := by rfl
@[local simp] theorem step_2d327 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d333,0x3f370] (n+1) ⟨s,f,0x2d327⟩ =
      (X86Routine.execute (.immediate 2 11) ⟨s,f,0x2d32c⟩).bind (X86Routine.run listed [0x2d333,0x3f370] n) := by rfl
@[local simp] theorem step_2d32c (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d333,0x3f370] (n+1) ⟨s,f,0x2d32c⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 0 1 0)))) ⟨s,f,0x2d32e⟩).bind (X86Routine.run listed [0x2d333,0x3f370] n) := by rfl
@[local simp] theorem step_2d32e (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d333,0x3f370] (n+1) ⟨s,f,0x2d32e⟩ =
      (X86Routine.execute (.call 73789) ⟨s,f,0x2d333⟩).bind (X86Routine.run listed [0x2d333,0x3f370] n) := by simp [X86Routine.run,listed]
@[local simp] theorem stop_2d333 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d333,0x3f370] n ⟨s,f,0x2d333⟩=some ⟨s,f,0x2d333⟩ := by cases n <;> rfl
@[local simp] theorem stop_3f370 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d333,0x3f370] n ⟨s,f,0x3f370⟩=some ⟨s,f,0x3f370⟩ := by cases n <;> rfl

def saved (s : X86Memory.State) :=
  X86Routine.pushWord (X86Routine.pushWord (X86Routine.pushWord (X86Routine.pushWord s (s.regs 3)) (s.regs 1)) (s.regs 6)) (s.regs 7)
def object (s : X86Memory.State) := load32 (saved s).memory (s.regs 0)
def pose (s : X86Memory.State) := load32 (saved s).memory (object s+(100#32))
def prepared (s : X86Memory.State) :=
  put (put (put (put (saved s) 1 (s.regs 0)) 7 (s.regs 2)) 0 (object s)) 2 (pose s)

theorem prologue (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 8 ⟨s,f,0x2d2f0⟩ ⟨prepared s,f,0x2d2fd⟩ := by
  let a := X86Routine.pushWord s (s.regs 3)
  let b := X86Routine.pushWord a (s.regs 1)
  let c := X86Routine.pushWord b (s.regs 6)
  have p : X86Routine.Prefix listed [] 8 ⟨s,f,0x2d2f0⟩ ⟨prepared s,f,0x2d2fd⟩ := by
    apply X86Routine.Prefix.step (middle := ⟨a,f,0x2d2f1⟩) (by simp) (by rfl) rfl
    apply X86Routine.Prefix.step (middle := ⟨b,f,0x2d2f2⟩) (by simp) (by rfl) rfl
    apply X86Routine.Prefix.step (middle := ⟨c,f,0x2d2f3⟩) (by simp) (by rfl) rfl
    apply X86Routine.Prefix.step (middle := ⟨saved s,f,0x2d2f4⟩) (by simp) (by rfl) rfl
    apply X86Routine.Prefix.step (middle := ⟨put (saved s) 1 (s.regs 0),f,0x2d2f6⟩) (by simp) (by rfl) rfl
    apply X86Routine.Prefix.step (middle := ⟨put (put (saved s) 1 (s.regs 0)) 7 (s.regs 2),f,0x2d2f8⟩) (by simp) (by rfl) rfl
    apply X86Routine.Prefix.step (middle := ⟨put (put (put (saved s) 1 (s.regs 0)) 7 (s.regs 2)) 0 (object s),f,0x2d2fa⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,blockPreservesFlags,object,put,write,saved,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := ⟨prepared s,f,0x2d2fd⟩) (by simp) (by rfl) rfl
    exact X86Routine.Prefix.nil _
  exact p.transfer program [] decoded (by simp)

abbrev needsReset (s : X86Memory.State) := s.regs 2=(0x16b00#32) ∨ s.regs 2=(0x16b1c#32)
def branch (s : X86Memory.State) : X86Control.State :=
  ⟨s,some (compare32 (s.regs 2) (if s.regs 2=(0x16b00#32) then 0x16b00 else 0x16b1c)),
    if needsReset s then 0x2d30d else 0x2d319⟩
theorem branch_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x2d30d,0x2d319] 4 ⟨s,f,0x2d2fd⟩=some (branch s) := by
  have run : X86Routine.run listed [0x2d30d,0x2d319] 4 ⟨s,f,0x2d2fd⟩=some (branch s) := by
    by_cases a : s.regs 2=(0x16b00#32) <;> by_cases b : s.regs 2=(0x16b1c#32) <;>
      simp [branch,needsReset,X86Routine.execute,X86Control.execute,cmp32_zero,a,b]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

def resetCall (s : X86Memory.State) (f : Option Flags) : X86Control.State :=
  ⟨X86Routine.pushWord (put (put s 2 149) 0 (load32 s.memory (s.regs 1))) 0x2d319,f,0x30ea0⟩
theorem reset_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x30ea0] 3 ⟨s,f,0x2d30d⟩=some (resetCall s f) := by
  have run : X86Routine.run listed [0x30ea0] 3 ⟨s,f,0x2d30d⟩=some (resetCall s f) := by
    simp [X86Routine.run,listed,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      blockPreservesFlags,resetCall,put,write,X86Routine.pushWord]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

def weapon (s : X86Memory.State) := load32 s.memory (s.regs 1+(112#32))
def sprite (s : X86Memory.State) := load32 s.memory (s.regs 7)
def sound (s : X86Memory.State) : X86Control.State :=
  if weapon s≠(7#32) then ⟨s,some (compare32 (weapon s) 7),0x2d333⟩
  else if sprite s≠(0x1617c#32) then ⟨s,some (compare32 (sprite s) 0x1617c),0x2d333⟩
  else ⟨X86Routine.pushWord (put (put s 2 11) 0 (load32 s.memory (s.regs 1))) 0x2d333,
    some (compare32 (sprite s) 0x1617c),0x3f370⟩
theorem sound_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x2d333,0x3f370] 7 ⟨s,f,0x2d319⟩=some (sound s) := by
  have run : X86Routine.run listed [0x2d333,0x3f370] 7 ⟨s,f,0x2d319⟩=some (sound s) := by
    by_cases w : weapon s=(7#32) <;> by_cases p : sprite s=(0x1617c#32) <;>
      simp only [weapon,sprite] at w p <;>
      simp [sound,weapon,sprite,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
        X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,cmp32_zero,w,p]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

private theorem prefix_trans {p stops n m s t u}
    (a : X86Routine.Prefix p stops n s t) (b : X86Routine.Prefix p stops m t u) :
    X86Routine.Prefix p stops (n+m) s u := by
  induction a with
  | nil => simpa using b
  | @step n s middle last op len active decoded executed rest ih =>
    simpa only [Nat.succ_add] using X86Routine.Prefix.step active decoded executed (ih b)

def result (s : X86Memory.State) : X86Control.State :=
  let t := prepared s
  if needsReset t then resetCall t (branch t).flags else sound t

/-- All entry paths, including stack aliases, through real calls or the decision
entry. A pose-reset or sound callee is not assumed to execute or return. -/
theorem execution (s : X86Memory.State) (f : Option Flags) :
    ∃ n, n≤19 ∧ X86Routine.Prefix program [] n ⟨s,f,0x2d2f0⟩ (result s) := by
  have a := prologue s f
  obtain ⟨n,hn,b,_⟩ := X86Routine.run_path (branch_execution (prepared s) f)
  have b := b.transfer program [] (by intros; rfl) (by simp)
  have ab := prefix_trans a b
  by_cases reset : needsReset (prepared s)
  · have eq : branch (prepared s)=⟨prepared s,(branch (prepared s)).flags,0x2d30d⟩ := by simp [branch,reset]
    rw [eq] at ab
    obtain ⟨m,hm,c,_⟩ := X86Routine.run_path (reset_execution (prepared s) (branch (prepared s)).flags)
    have c := c.transfer program [] (by intros; rfl) (by simp)
    exact ⟨8+n+m,by omega,by simpa only [result,if_pos reset] using prefix_trans ab c⟩
  · have eq : branch (prepared s)=⟨prepared s,(branch (prepared s)).flags,0x2d319⟩ := by simp [branch,reset]
    rw [eq] at ab
    obtain ⟨m,hm,c,_⟩ := X86Routine.run_path (sound_execution (prepared s) (branch (prepared s)).flags)
    have c := c.transfer program [] (by intros; rfl) (by simp)
    exact ⟨8+n+m,by omega,by simpa only [result,if_neg reset] using prefix_trans ab c⟩

/-- A relation at the post-prologue boundary: byte separation/loader invariants
must establish these reads from a live entry state. -/
structure Inputs (s : X86Memory.State) (frame : Fin 967) (w : Fin 3) : Prop where
  poseValue : pose s=BitVec.ofNat 32 (0x15a28+28*frame.val)
  weaponValue : weapon (prepared s)=BitVec.ofNat 32 w.val

theorem pose_decision (s : X86Memory.State) (frame : Fin 967) (w : Fin 3) (h : Inputs s frame w) :
    needsReset (prepared s) ↔ frame.val=154 ∨ frame.val=155 := by
  have checked : ∀ i : Fin 967,
      (BitVec.ofNat 32 (0x15a28+28*i.val)=(0x16b00#32) ∨ BitVec.ofNat 32 (0x15a28+28*i.val)=(0x16b1c#32)) ↔
      i.val=154 ∨ i.val=155 := by decide
  simpa [needsReset,prepared,put,write,h.poseValue] using checked frame

theorem no_chainsaw (s : X86Memory.State) (frame : Fin 967) (w : Fin 3) (h : Inputs s frame w) :
    sound (prepared s)=⟨prepared s,some (compare32 (weapon (prepared s)) 7),0x2d333⟩ := by
  have ne : weapon (prepared s)≠(7#32) := by
    rw [h.weaponValue]
    have cases : w.val=0 ∨ w.val=1 ∨ w.val=2 := by omega
    rcases cases with e | e | e <;> rw [e] <;> decide
  simp only [sound,if_pos ne]

theorem ready_boundary (s : X86Memory.State) (frame : Fin 967) (w : Fin 3) (h : Inputs s frame w)
    (idlePose : frame.val≠154 ∧ frame.val≠155) :
    result s=⟨prepared s,some (compare32 (weapon (prepared s)) 7),0x2d333⟩ := by
  have no : ¬needsReset (prepared s) := by rw [pose_decision s frame w h]; omega
  simp only [result,if_neg no,no_chainsaw s frame w h]

theorem reset_arguments (s : X86Memory.State) (f : Option Flags) :
    (resetCall s f).core.regs 0=load32 s.memory (s.regs 1) ∧
    (resetCall s f).core.regs 2=149 ∧ (resetCall s f).core.regs 4=s.regs 4-4 ∧
    load32 (resetCall s f).core.memory (s.regs 4-4)=0x2d319 := by
  simp [resetCall,X86Routine.pushWord,put,write,load_store]
end Doom.Proofs.WeaponReadyEntry
