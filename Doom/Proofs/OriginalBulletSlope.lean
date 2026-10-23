import Doom.Verification.X86Routine
import Doom.Proofs.BlockSummary
import Doom.Fixed
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalBulletSlope
open Verification X86 X86Memory X86Control BlockSummary

/-- Original P_BulletSlope. The geometry callee at 0x2bb80 is a separate obligation. -/
def code : List UInt8 := [0x53,0x51,0x52,0x56,0x89,0xc6,0x8b,0x48,0x20,0xbb,0x0,0x0,0x0,0x4,0x89,0xca,0xe8,0xab,0xe3,0xff,0xff,0x8b,0x15,0xf8,0xb9,0x2,0x0,0xa3,0xc0,0xc0,0x2,0x0,0x85,0xd2,0x75,0x3a,0xbb,0x0,0x0,0x0,0x4,0x81,0xc1,0x0,0x0,0x0,0x4,0x89,0xf0,0x89,0xca,0xe8,0x88,0xe3,0xff,0xff,0x8b,0x1d,0xf8,0xb9,0x2,0x0,0xa3,0xc0,0xc0,0x2,0x0,0x85,0xdb,0x75,0x17,0xbb,0x0,0x0,0x0,0x4,0x8d,0x91,0x0,0x0,0x0,0xf8,0x89,0xf0,0xe8,0x67,0xe3,0xff,0xff,0xa3,0xc0,0xc0,0x2,0x0,0x5e,0x5a,0x59,0x5b,0xc3]
def bytesProgram (bytes : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2d7c0 ≤ pc ∧ pc < 0x2d823 then X86Routine.decodeAt bytes (pc-0x2d7c0) else none
def program := bytesProgram code

def listed : X86Routine.Program
  | 0x2d7c0 => some (.push 3,1)
  | 0x2d7c1 => some (.push 1,1)
  | 0x2d7c2 => some (.push 2,1)
  | 0x2d7c3 => some (.push 6,1)
  | 0x2d7c4 => some (.control (.block (.legacy (.mov 6 0))),2)
  | 0x2d7c6 => some (.control (.block (.legacy (.load 1 0 32))),3)
  | 0x2d7c9 => some (.immediate 3 0x04000000,5)
  | 0x2d7ce => some (.control (.block (.legacy (.mov 2 1))),2)
  | 0x2d7d0 => some (.call (-7253),5)
  | 0x2d7d5 => some (.control (.block (.load 2 ⟨none,none,0,0x2b9f8⟩)),6)
  | 0x2d7db => some (.control (.storeEax 0x2c0c0),5)
  | 0x2d7e0 => some (.control (.testWord 2 2),2)
  | 0x2d7e2 => some (.control (.jumpZero false 58),2)
  | 0x2d7e4 => some (.immediate 3 0x04000000,5)
  | 0x2d7e9 => some (.addImmediate 1 0x04000000,6)
  | 0x2d7ef => some (.control (.block (.legacy (.mov 0 6))),2)
  | 0x2d7f1 => some (.control (.block (.legacy (.mov 2 1))),2)
  | 0x2d7f3 => some (.call (-7288),5)
  | 0x2d7f8 => some (.control (.block (.load 3 ⟨none,none,0,0x2b9f8⟩)),6)
  | 0x2d7fe => some (.control (.storeEax 0x2c0c0),5)
  | 0x2d803 => some (.control (.testWord 3 3),2)
  | 0x2d805 => some (.control (.jumpZero false 23),2)
  | 0x2d807 => some (.immediate 3 0x04000000,5)
  | 0x2d80c => some (.control (.block (.lea 2 ⟨some 1,none,0,0xf8000000⟩)),6)
  | 0x2d812 => some (.control (.block (.legacy (.mov 0 6))),2)
  | 0x2d814 => some (.call (-7321),5)
  | 0x2d819 => some (.control (.storeEax 0x2c0c0),5)
  | 0x2d81e => some (.pop 6,1)
  | 0x2d81f => some (.pop 2,1)
  | 0x2d820 => some (.pop 1,1)
  | 0x2d821 => some (.pop 3,1)
  | 0x2d822 => some (.ret,1)
  | _ => none

theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def saved (s : X86Memory.State) :=
  X86Routine.pushWord (X86Routine.pushWord (X86Routine.pushWord
    (X86Routine.pushWord s (s.regs 3)) (s.regs 1)) (s.regs 2)) (s.regs 6)
def initialAngle (s : X86Memory.State) := load32 (saved s).memory (s.regs 0+32)
def firstCall (s : X86Memory.State) (f : Option Flags) : X86Control.State :=
  ⟨X86Routine.pushWord (put (put (put (put (saved s) 6 (s.regs 0))
    1 (initialAngle s)) 3 0x04000000) 2 (initialAngle s)) 0x2d7d5,f,0x2bb80⟩

def target (s : X86Memory.State) := load32 s.memory 0x2b9f8
def stored (s : X86Memory.State) : X86Memory.State :=
  {s with memory := store32 s.memory 0x2c0c0 (s.regs 0)}
def decision (second : Bool) (s : X86Memory.State) : X86Control.State :=
  ⟨put (stored s) (if second then 3 else 2) (target s),some (logical32 (target s)),
    if target s=0 then (if second then 0x2d807 else 0x2d7e4) else 0x2d81e⟩
def retry (second : Bool) (s : X86Memory.State) : X86Control.State :=
  let t := put s 3 0x04000000
  let t := if second then t else put t 1 (s.regs 1+0x04000000)
  let t := put t 0 (s.regs 6)
  let t := put t 2 (if second then s.regs 1+0xf8000000 else s.regs 1+0x04000000)
  ⟨X86Routine.pushWord t (if second then 0x2d819 else 0x2d7f8),
    none,0x2bb80⟩
-- The second retry is LEA/MOV only and preserves incoming flags.
def retryState (second : Bool) (s : X86Memory.State) (f : Option Flags) : X86Control.State :=
  {retry second s with flags := if second then f else none}

def pop (s : X86Memory.State) (r : Reg) : X86Memory.State :=
  put (put s 4 (s.regs 4+4)) r (load32 s.memory (s.regs 4))
def finished (s : X86Memory.State) (f : Option Flags) : X86Control.State :=
  let t := pop (pop (pop (pop s 6) 2) 1) 3
  ⟨put t 4 (t.regs 4+4),f,(load32 t.memory (t.regs 4)).toNat⟩

theorem first_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 9 ⟨s,f,0x2d7c0⟩ (firstCall s f) := by
  let c1 := X86Routine.pushWord s (s.regs 3)
  let c2 := X86Routine.pushWord c1 (s.regs 1)
  let c3 := X86Routine.pushWord c2 (s.regs 2)
  let c4 := X86Routine.pushWord c3 (s.regs 6)
  let c5 := put c4 6 (s.regs 0)
  let c6 := put c5 1 (initialAngle s)
  let c7 := put c6 3 0x04000000
  let c8 := put c7 2 (initialAngle s)
  have path : X86Routine.Prefix listed [] 9 ⟨s,f,0x2d7c0⟩ (firstCall s f) := by
    apply X86Routine.Prefix.step (middle := ⟨c1,f,0x2d7c1⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,X86Memory.execute,put,write,X86Routine.pushWord,blockPreservesFlags,c1,initialAngle,saved])
    apply X86Routine.Prefix.step (middle := ⟨c2,f,0x2d7c2⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,X86Memory.execute,put,write,X86Routine.pushWord,blockPreservesFlags,c2,c1,initialAngle,saved])
    apply X86Routine.Prefix.step (middle := ⟨c3,f,0x2d7c3⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,X86Memory.execute,put,write,X86Routine.pushWord,blockPreservesFlags,c3,c2,c1,initialAngle,saved])
    apply X86Routine.Prefix.step (middle := ⟨c4,f,0x2d7c4⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,X86Memory.execute,put,write,X86Routine.pushWord,blockPreservesFlags,c4,c3,c2,c1,initialAngle,saved])
    apply X86Routine.Prefix.step (middle := ⟨c5,f,0x2d7c6⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,X86Memory.execute,put,write,X86Routine.pushWord,blockPreservesFlags,c5,c4,c3,c2,c1,initialAngle,saved])
    apply X86Routine.Prefix.step (middle := ⟨c6,f,0x2d7c9⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,X86Memory.execute,put,write,X86Routine.pushWord,blockPreservesFlags,c6,c5,c4,c3,c2,c1,initialAngle,saved])
    apply X86Routine.Prefix.step (middle := ⟨c7,f,0x2d7ce⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,X86Memory.execute,put,write,X86Routine.pushWord,blockPreservesFlags,c7,c6,c5,c4,c3,c2,c1,initialAngle,saved])
    apply X86Routine.Prefix.step (middle := ⟨c8,f,0x2d7d0⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,X86Memory.execute,put,write,X86Routine.pushWord,blockPreservesFlags,c8,c7,c6,c5,c4,c3,c2,c1,initialAngle,saved])
    apply X86Routine.Prefix.step (middle := firstCall s f) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,X86Memory.execute,put,write,X86Routine.pushWord,blockPreservesFlags,firstCall,c8,c7,c6,c5,c4,c3,c2,c1,saved])
    exact X86Routine.Prefix.nil _
  exact path.transfer program [] decoded (by simp)

theorem decision_execution (second : Bool) (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 4 ⟨s,f,if second then 0x2d7f8 else 0x2d7d5⟩ (decision second s) := by
  have path : X86Routine.Prefix listed [] 4 ⟨s,f,if second then 0x2d7f8 else 0x2d7d5⟩ (decision second s) := by
    cases second with
    | false =>
      let c1 := put s 2 (target s)
      let c2 : X86Memory.State := {c1 with memory := (stored s).memory}
      apply X86Routine.Prefix.step (middle := ⟨c1,f,0x2d7db⟩) (by simp) (by rfl) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,X86Memory.execute,put,write,X86Routine.pushWord,blockPreservesFlags,c1,target])
      apply X86Routine.Prefix.step (middle := ⟨c2,f,0x2d7e0⟩) (by simp) (by rfl) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,X86Memory.execute,put,write,X86Routine.pushWord,blockPreservesFlags,c2,c1,stored,eax])
      apply X86Routine.Prefix.step (middle := ⟨c2,some (logical32 (target s)),0x2d7e2⟩) (by simp) (by rfl) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,X86Memory.execute,put,write,X86Routine.pushWord,blockPreservesFlags,c2,c1])
      apply X86Routine.Prefix.step (middle := decision false s) (by simp) (by rfl) (by
        by_cases h : target s=(0#32) <;> simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,X86Memory.execute,put,write,X86Routine.pushWord,blockPreservesFlags,decision,c2,c1,stored,logical32,h])
      exact X86Routine.Prefix.nil _
    | true =>
      let c1 := put s 3 (target s)
      let c2 : X86Memory.State := {c1 with memory := (stored s).memory}
      apply X86Routine.Prefix.step (middle := ⟨c1,f,0x2d7fe⟩) (by simp) (by rfl) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,X86Memory.execute,put,write,X86Routine.pushWord,blockPreservesFlags,c1,target])
      apply X86Routine.Prefix.step (middle := ⟨c2,f,0x2d803⟩) (by simp) (by rfl) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,X86Memory.execute,put,write,X86Routine.pushWord,blockPreservesFlags,c2,c1,stored,eax])
      apply X86Routine.Prefix.step (middle := ⟨c2,some (logical32 (target s)),0x2d805⟩) (by simp) (by rfl) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,X86Memory.execute,put,write,X86Routine.pushWord,blockPreservesFlags,c2,c1])
      apply X86Routine.Prefix.step (middle := decision true s) (by simp) (by rfl) (by
        by_cases h : target s=(0#32) <;> simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,X86Memory.execute,put,write,X86Routine.pushWord,blockPreservesFlags,decision,c2,c1,stored,logical32,h])
      exact X86Routine.Prefix.nil _
  exact path.transfer program [] decoded (by simp)

theorem retry_execution (second : Bool) (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] (if second then 4 else 5)
      ⟨s,f,if second then 0x2d807 else 0x2d7e4⟩ (retryState second s f) := by
  have path : X86Routine.Prefix listed [] (if second then 4 else 5)
      ⟨s,f,if second then 0x2d807 else 0x2d7e4⟩ (retryState second s f) := by
    cases second with
    | false =>
      let c1 := put s 3 0x04000000
      let c2 := put c1 1 (s.regs 1+0x04000000)
      let c3 := put c2 0 (s.regs 6)
      let c4 := put c3 2 (s.regs 1+0x04000000)
      apply X86Routine.Prefix.step (middle := ⟨c1,f,0x2d7e9⟩) (by simp) (by rfl) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,X86Memory.execute,put,write,X86Routine.pushWord,blockPreservesFlags,c1])
      apply X86Routine.Prefix.step (middle := ⟨c2,none,0x2d7ef⟩) (by simp) (by rfl) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,X86Memory.execute,put,write,X86Routine.pushWord,blockPreservesFlags,c2,c1])
      apply X86Routine.Prefix.step (middle := ⟨c3,none,0x2d7f1⟩) (by simp) (by rfl) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,X86Memory.execute,put,write,X86Routine.pushWord,blockPreservesFlags,c3,c2,c1])
      apply X86Routine.Prefix.step (middle := ⟨c4,none,0x2d7f3⟩) (by simp) (by rfl) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,X86Memory.execute,put,write,X86Routine.pushWord,blockPreservesFlags,c4,c3,c2,c1])
      apply X86Routine.Prefix.step (middle := retryState false s f) (by simp) (by rfl) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,X86Memory.execute,put,write,X86Routine.pushWord,blockPreservesFlags,retryState,retry,c4,c3,c2,c1])
      exact X86Routine.Prefix.nil _
    | true =>
      let c1 := put s 3 0x04000000
      let c2 := put c1 2 (s.regs 1+0xf8000000)
      let c3 := put c2 0 (s.regs 6)
      apply X86Routine.Prefix.step (middle := ⟨c1,f,0x2d80c⟩) (by simp) (by rfl) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,X86Memory.execute,put,write,X86Routine.pushWord,blockPreservesFlags,c1])
      apply X86Routine.Prefix.step (middle := ⟨c2,f,0x2d812⟩) (by simp) (by rfl) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,X86Memory.execute,put,write,X86Routine.pushWord,blockPreservesFlags,c2,c1])
      apply X86Routine.Prefix.step (middle := ⟨c3,f,0x2d814⟩) (by simp) (by rfl) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,X86Memory.execute,put,write,X86Routine.pushWord,blockPreservesFlags,c3,c2,c1])
      apply X86Routine.Prefix.step (middle := retryState true s f) (by simp) (by rfl) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,X86Memory.execute,put,write,X86Routine.pushWord,blockPreservesFlags,retryState,retry,c3,c2,c1]
        funext r
        by_cases h0 : r=0 <;> by_cases h2 : r=2 <;> by_cases h3 : r=3 <;> by_cases h4 : r=4 <;> simp_all [write])
      exact X86Routine.Prefix.nil _
  exact path.transfer program [] decoded (by simp)

theorem last_store_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x2d81e] 1 ⟨s,f,0x2d819⟩=some ⟨stored s,f,0x2d81e⟩ := by
  have run : X86Routine.run listed [0x2d81e] 1 ⟨s,f,0x2d819⟩=some ⟨stored s,f,0x2d81e⟩ := by
    simp [X86Routine.run,listed,X86Routine.execute,X86Control.execute,stored]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

theorem finish_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 5 ⟨s,f,0x2d81e⟩ (finished s f) := by
  let s1 := pop s 6
  let s2 := pop s1 2
  let s3 := pop s2 1
  let s4 := pop s3 3
  have path : X86Routine.Prefix listed [] 5 ⟨s,f,0x2d81e⟩ (finished s f) := by
    apply X86Routine.Prefix.step (middle := ⟨s1,f,0x2d81f⟩) (by simp) (by rfl) (by rfl)
    apply X86Routine.Prefix.step (middle := ⟨s2,f,0x2d820⟩) (by simp) (by rfl) (by rfl)
    apply X86Routine.Prefix.step (middle := ⟨s3,f,0x2d821⟩) (by simp) (by rfl) (by rfl)
    apply X86Routine.Prefix.step (middle := ⟨s4,f,0x2d822⟩) (by simp) (by rfl) (by rfl)
    apply X86Routine.Prefix.step (middle := finished s f) (by simp) (by rfl) (by rfl)
    exact X86Routine.Prefix.nil _
  exact path.transfer program [] decoded (by simp)

/-- Branches inspect target presence, never the returned slope's sign or value. -/
theorem stored_slope (s : X86Memory.State) : load32 (stored s).memory 0x2c0c0=s.regs 0 := by
  simp [stored,load_store]
theorem finished_slope (s : X86Memory.State) (f : Option Flags) :
    load32 (finished s f).core.memory 0x2c0c0=load32 s.memory 0x2c0c0 := rfl

def saveWrites (s : X86Memory.State) : List Word :=
  [s.regs 4-4,s.regs 4-8,s.regs 4-12,s.regs 4-16]
theorem saved_frame (s : X86Memory.State) (a : Word)
    (safe : ∀ b, b ∈ saveWrites s → Apart a b) :
    load32 (saved s).memory a=load32 s.memory a := by
  simp only [saved,X86Routine.pushWord,put,write,ite_true]
  simp [BitVec.sub_sub]
  repeat rw [load_store_apart _ _ _ _ (safe _ (by simp [saveWrites]))]
theorem initial_angle (s : X86Memory.State) (angle : Angle)
    (value : load32 s.memory (s.regs 0+32)=angle.raw.toBitVec)
    (safe : ∀ b, b ∈ saveWrites s → Apart (s.regs 0+32) b) :
    initialAngle s=angle.raw.toBitVec := by
  rw [initialAngle,saved_frame s _ safe,value]

theorem first_arguments (s : X86Memory.State) (f : Option Flags) :
    (firstCall s f).core.regs 0=s.regs 0 ∧ (firstCall s f).core.regs 2=initialAngle s ∧
    (firstCall s f).core.regs 3=0x04000000 := by
  simp [firstCall,put,write,X86Routine.pushWord,saved]
theorem retry_arguments (second : Bool) (s : X86Memory.State) (f : Option Flags) :
    (retryState second s f).core.regs 0=s.regs 6 ∧
    (retryState second s f).core.regs 2=s.regs 1+(if second then 0xf8000000 else 0x04000000) ∧
    (retryState second s f).core.regs 3=0x04000000 := by
  cases second <;> simp [retryState,retry,put,write,X86Routine.pushWord]

end Doom.Proofs.OriginalBulletSlope
