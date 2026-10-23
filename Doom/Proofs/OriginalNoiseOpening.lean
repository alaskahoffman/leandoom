import Doom.Proofs.E1M1NoiseTraversal
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.NoiseOpening
open Verification X86 X86Memory X86Control BlockSummary
def openingBytes : List UInt8 := [0x53,0x51,0x52,0x56,0x89,0xc2,0xf,0xbf,0x40,0x18,0x83,0xf8,0xff,0x75,0x4,0x31,0xd2,0xeb,0x4c,0x8b,0x42,0x2e,0x8b,0x52,0x32,0x8b,0x58,0x4,0x8b,0x4a,0x4,0x39,0xcb,0x7d,0x8,0x89,0x1d,0x34,0xc0,0x2,0x0,0xeb,0x6,0x89,0xd,0x34,0xc0,0x2,0x0,0x8b,0x18,0x8b,0x32,0x39,0xf3,0x7e,0xe,0x89,0x1d,0x30,0xc0,0x2,0x0,0x89,0x35,0x2c,0xc0,0x2,0x0,0xeb,0xc,0x89,0x35,0x30,0xc0,0x2,0x0,0x89,0x1d,0x2c,0xc0,0x2,0x0,0x8b,0x15,0x34,0xc0,0x2,0x0,0x2b,0x15,0x30,0xc0,0x2,0x0,0x89,0x15,0x38,0xc0,0x2,0x0,0x5e,0x5a,0x59,0x5b,0xc3]
def neighborBytes : List UInt8 := [0xf,0xbf,0x42,0x16,0x6b,0xc0,0x12,0x8b,0x3d,0x18,0xc1,0x2,0x0,0x1,0xf8,0x89,0x3c,0x24,0x8b,0x78,0xe,0x39,0xfb,0x75,0xf,0xf,0xbf,0x42,0x18,0x6b,0xc0,0x12,0x3,0x4,0x24,0x8b,0x40,0xe,0xeb,0x2,0x89,0xf8]
def bytesProgram (opening neighbor : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2c340≤pc ∧ pc<0x2c3aa then X86Routine.decodeAt opening (pc-0x2c340)
  else if 0x26fc4≤pc ∧ pc<0x26fee then X86Routine.decodeAt neighbor (pc-0x26fc4) else none
def program := bytesProgram openingBytes neighborBytes
def listed : X86Routine.Program
  | 0x2c340 => some (.push 3,1)
  | 0x2c341 => some (.push 1,1)
  | 0x2c342 => some (.push 2,1)
  | 0x2c343 => some (.push 6,1)
  | 0x2c344 => some (.control (.block (.legacy (.mov 2 0))),2)
  | 0x2c346 => some (.control (.block (.legacy (.movsx16 0 0 24))),4)
  | 0x2c34a => some (.compareRegister 0 0xffffffff,3)
  | 0x2c34d => some (.control (.jumpZero false 4),2)
  | 0x2c34f => some (.xorRegister 2 2,2)
  | 0x2c351 => some (.jump 76,2)
  | 0x2c353 => some (.control (.block (.legacy (.load 0 2 46))),3)
  | 0x2c356 => some (.control (.block (.legacy (.load 2 2 50))),3)
  | 0x2c359 => some (.control (.block (.legacy (.load 3 0 4))),3)
  | 0x2c35c => some (.control (.block (.legacy (.load 1 2 4))),3)
  | 0x2c35f => some (.compareRegisters 3 1,2)
  | 0x2c361 => some (.jumpSigned 0 8,2)
  | 0x2c363 => some (.control (.block (.store ⟨none,none,0,0x2c034⟩ 3)),6)
  | 0x2c369 => some (.jump 6,2)
  | 0x2c36b => some (.control (.block (.store ⟨none,none,0,0x2c034⟩ 1)),6)
  | 0x2c371 => some (.control (.block (.legacy (.load 3 0 0))),2)
  | 0x2c373 => some (.control (.block (.legacy (.load 6 2 0))),2)
  | 0x2c375 => some (.compareRegisters 3 6,2)
  | 0x2c377 => some (.jumpSigned 1 14,2)
  | 0x2c379 => some (.control (.block (.store ⟨none,none,0,0x2c030⟩ 3)),6)
  | 0x2c37f => some (.control (.block (.store ⟨none,none,0,0x2c02c⟩ 6)),6)
  | 0x2c385 => some (.jump 12,2)
  | 0x2c387 => some (.control (.block (.store ⟨none,none,0,0x2c030⟩ 6)),6)
  | 0x2c38d => some (.control (.block (.store ⟨none,none,0,0x2c02c⟩ 3)),6)
  | 0x2c393 => some (.control (.block (.load 2 ⟨none,none,0,0x2c034⟩)),6)
  | 0x2c399 => some (.subMemory 2 ⟨none,none,0,0x2c030⟩,6)
  | 0x2c39f => some (.control (.block (.store ⟨none,none,0,0x2c038⟩ 2)),6)
  | 0x2c3a5 => some (.pop 6,1)
  | 0x2c3a6 => some (.pop 2,1)
  | 0x2c3a7 => some (.pop 1,1)
  | 0x2c3a8 => some (.pop 3,1)
  | 0x2c3a9 => some (.ret,1)
  | 0x26fc4 => some (.control (.block (.legacy (.movsx16 0 2 22))),4)
  | 0x26fc8 => some (.multiplyImmediate 0 0 18,3)
  | 0x26fcb => some (.control (.block (.load 7 ⟨none,none,0,0x2c118⟩)),6)
  | 0x26fd1 => some (.control (.block (.arithmetic (.add 0 7))),2)
  | 0x26fd3 => some (.control (.block (.store ⟨some 4,none,0,0⟩ 7)),3)
  | 0x26fd6 => some (.control (.block (.legacy (.load 7 0 14))),3)
  | 0x26fd9 => some (.compareRegisters 3 7,2)
  | 0x26fdb => some (.control (.jumpZero false 15),2)
  | 0x26fdd => some (.control (.block (.legacy (.movsx16 0 2 24))),4)
  | 0x26fe1 => some (.multiplyImmediate 0 0 18,3)
  | 0x26fe4 => some (.addMemory 0 ⟨some 4,none,0,0⟩,3)
  | 0x26fe7 => some (.control (.block (.legacy (.load 0 0 14))),3)
  | 0x26fea => some (.jump 2,2)
  | 0x26fec => some (.control (.block (.legacy (.mov 0 7))),2)
  | _ => none

theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def saved (s : X86Memory.State) :=
  let s := X86Routine.pushWord s (s.regs 3)
  let s := X86Routine.pushWord s (s.regs 1)
  let s := X86Routine.pushWord s (s.regs 2)
  X86Routine.pushWord s (s.regs 6)
def prepared (s : X86Memory.State) :=
  let t := put (saved s) 2 ((saved s).regs 0)
  put t 0 ((load16 t.memory (t.regs 0+24)).signExtend 32)
def entry (s : X86Memory.State) : X86Control.State :=
  let t := prepared s
  ⟨t,some (compare32 (t.regs 0) 0xffffffff),if t.regs 0=(0xffffffff#32) then 0x2c34f else 0x2c353⟩
def closed (s : X86Memory.State) : X86Control.State := ⟨put s 2 0,some (logical32 0),0x2c39f⟩
def ceilingInputs (s : X86Memory.State) :=
  let t := put s 0 (load32 s.memory (s.regs 2+46))
  let t := put t 2 (load32 t.memory (t.regs 2+50))
  let t := put t 3 (load32 t.memory (t.regs 0+4))
  put t 1 (load32 t.memory (t.regs 2+4))
def ceiling (s : X86Memory.State) : X86Control.State :=
  let t := ceilingInputs s
  ⟨{t with memory := store32 t.memory 0x2c034 (if (t.regs 1).toInt≤(t.regs 3).toInt then t.regs 1 else t.regs 3)},
    some (compare32 (t.regs 3) (t.regs 1)),0x2c371⟩
def floorInputs (s : X86Memory.State) :=
  let t := put s 3 (load32 s.memory (s.regs 0+0))
  put t 6 (load32 t.memory (t.regs 2+0))
def floor (s : X86Memory.State) : X86Control.State :=
  let t := floorInputs s
  let le := (t.regs 3).toInt≤(t.regs 6).toInt
  ⟨{t with memory := store32 (store32 t.memory 0x2c030
      (if le then t.regs 6 else t.regs 3)) 0x2c02c (if le then t.regs 3 else t.regs 6)},
    some (compare32 (t.regs 3) (t.regs 6)),0x2c393⟩
def range (s : X86Memory.State) : X86Control.State :=
  let t := put s 2 (load32 s.memory (0x2c034#32))
  ⟨put t 2 (t.regs 2-load32 t.memory (0x2c030#32)),none,0x2c39f⟩
def returned (s : X86Memory.State) (f : Option Flags) : X86Control.State :=
  let t := {s with memory := store32 s.memory 0x2c038 (s.regs 2)}
  let t := PspriteLoop.popped (PspriteLoop.popped (PspriteLoop.popped (PspriteLoop.popped t 6) 2) 1) 3
  ⟨put t 4 (t.regs 4+4),f,(load32 t.memory (t.regs 4)).toNat⟩
def neighborInputs (s : X86Memory.State) :=
  let t := put s 0 ((load16 s.memory (s.regs 2+22)).signExtend 32)
  let t := put t 0 (t.regs 0*18)
  let t := put t 7 (load32 t.memory (0x2c118#32))
  let t := put t 0 (t.regs 0+t.regs 7)
  let t := {t with memory := store32 t.memory (t.regs 4) (t.regs 7)}
  put t 7 (load32 t.memory (t.regs 0+14))
def neighborGate (s : X86Memory.State) : X86Control.State :=
  let t := neighborInputs s
  ⟨t,some (compare32 (t.regs 3) (t.regs 7)),if t.regs 3=t.regs 7 then 0x26fdd else 0x26fec⟩
def backNeighbor (s : X86Memory.State) : X86Control.State :=
  let t := put s 0 ((load16 s.memory (s.regs 2+24)).signExtend 32)
  let t := put t 0 (t.regs 0*18)
  let t := put t 0 (t.regs 0+load32 t.memory (t.regs 4))
  ⟨put t 0 (load32 t.memory (t.regs 0+14)),none,0x26fee⟩
def frontNeighbor (s : X86Memory.State) (f : Option Flags) : X86Control.State :=
  ⟨put s 0 (s.regs 7),f,0x26fee⟩

@[local simp] private theorem step_entry_2c340 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2c34f,0x2c353] (n+1) ⟨s,f,0x2c340⟩ =
      (X86Routine.execute (.push 3) ⟨s,f,0x2c341⟩).bind (X86Routine.run listed [0x2c34f,0x2c353] n) := by rfl

@[local simp] private theorem step_entry_2c341 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2c34f,0x2c353] (n+1) ⟨s,f,0x2c341⟩ =
      (X86Routine.execute (.push 1) ⟨s,f,0x2c342⟩).bind (X86Routine.run listed [0x2c34f,0x2c353] n) := by rfl

@[local simp] private theorem step_entry_2c342 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2c34f,0x2c353] (n+1) ⟨s,f,0x2c342⟩ =
      (X86Routine.execute (.push 2) ⟨s,f,0x2c343⟩).bind (X86Routine.run listed [0x2c34f,0x2c353] n) := by rfl

@[local simp] private theorem step_entry_2c343 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2c34f,0x2c353] (n+1) ⟨s,f,0x2c343⟩ =
      (X86Routine.execute (.push 6) ⟨s,f,0x2c344⟩).bind (X86Routine.run listed [0x2c34f,0x2c353] n) := by rfl

@[local simp] private theorem step_entry_2c344 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2c34f,0x2c353] (n+1) ⟨s,f,0x2c344⟩ =
      (X86Routine.execute (.control (.block (.legacy (.mov 2 0)))) ⟨s,f,0x2c346⟩).bind (X86Routine.run listed [0x2c34f,0x2c353] n) := by rfl

@[local simp] private theorem step_entry_2c346 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2c34f,0x2c353] (n+1) ⟨s,f,0x2c346⟩ =
      (X86Routine.execute (.control (.block (.legacy (.movsx16 0 0 24)))) ⟨s,f,0x2c34a⟩).bind (X86Routine.run listed [0x2c34f,0x2c353] n) := by rfl

@[local simp] private theorem step_entry_2c34a (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2c34f,0x2c353] (n+1) ⟨s,f,0x2c34a⟩ =
      (X86Routine.execute (.compareRegister 0 0xffffffff) ⟨s,f,0x2c34d⟩).bind (X86Routine.run listed [0x2c34f,0x2c353] n) := by rfl

@[local simp] private theorem step_entry_2c34d (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2c34f,0x2c353] (n+1) ⟨s,f,0x2c34d⟩ =
      (X86Routine.execute (.control (.jumpZero false 4)) ⟨s,f,0x2c34f⟩).bind (X86Routine.run listed [0x2c34f,0x2c353] n) := by rfl
@[local simp] private theorem stop_entry_2c34f (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2c34f,0x2c353] n ⟨s,f,0x2c34f⟩=some ⟨s,f,0x2c34f⟩ := by cases n <;> rfl
@[local simp] private theorem stop_entry_2c353 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2c34f,0x2c353] n ⟨s,f,0x2c353⟩=some ⟨s,f,0x2c353⟩ := by cases n <;> rfl

theorem entry_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x2c34f,0x2c353] 8 ⟨s,f,0x2c340⟩=some (entry s) := by
  have run : X86Routine.run listed [0x2c34f,0x2c353] 8 ⟨s,f,0x2c340⟩=some (entry s) := by
    by_cases side : (prepared s).regs 0=(0xffffffff#32)
    all_goals
      simp [prepared,saved,put,write] at side
    all_goals
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
        X86Block.Address.eval,X86.execute,blockPreservesFlags,entry,prepared,saved,side,cmp32_zero,put,write,-BitVec.toInt_add]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

@[local simp] private theorem step_closed_2c34f (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2c39f] (n+1) ⟨s,f,0x2c34f⟩ =
      (X86Routine.execute (.xorRegister 2 2) ⟨s,f,0x2c351⟩).bind (X86Routine.run listed [0x2c39f] n) := by rfl

@[local simp] private theorem step_closed_2c351 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2c39f] (n+1) ⟨s,f,0x2c351⟩ =
      (X86Routine.execute (.jump 76) ⟨s,f,0x2c353⟩).bind (X86Routine.run listed [0x2c39f] n) := by rfl
@[local simp] private theorem stop_closed_2c39f (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2c39f] n ⟨s,f,0x2c39f⟩=some ⟨s,f,0x2c39f⟩ := by cases n <;> rfl

theorem closed_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x2c39f] 2 ⟨s,f,0x2c34f⟩=some (closed s) := by
  have run : X86Routine.run listed [0x2c39f] 2 ⟨s,f,0x2c34f⟩=some (closed s) := by
    
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
        X86Block.Address.eval,X86.execute,blockPreservesFlags,closed,logical32,put,write,-BitVec.toInt_add]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

@[local simp] private theorem step_ceiling_2c353 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2c371] (n+1) ⟨s,f,0x2c353⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 0 2 46)))) ⟨s,f,0x2c356⟩).bind (X86Routine.run listed [0x2c371] n) := by rfl

@[local simp] private theorem step_ceiling_2c356 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2c371] (n+1) ⟨s,f,0x2c356⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 2 2 50)))) ⟨s,f,0x2c359⟩).bind (X86Routine.run listed [0x2c371] n) := by rfl

@[local simp] private theorem step_ceiling_2c359 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2c371] (n+1) ⟨s,f,0x2c359⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 3 0 4)))) ⟨s,f,0x2c35c⟩).bind (X86Routine.run listed [0x2c371] n) := by rfl

@[local simp] private theorem step_ceiling_2c35c (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2c371] (n+1) ⟨s,f,0x2c35c⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 1 2 4)))) ⟨s,f,0x2c35f⟩).bind (X86Routine.run listed [0x2c371] n) := by rfl

@[local simp] private theorem step_ceiling_2c35f (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2c371] (n+1) ⟨s,f,0x2c35f⟩ =
      (X86Routine.execute (.compareRegisters 3 1) ⟨s,f,0x2c361⟩).bind (X86Routine.run listed [0x2c371] n) := by rfl

@[local simp] private theorem step_ceiling_2c361 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2c371] (n+1) ⟨s,f,0x2c361⟩ =
      (X86Routine.execute (.jumpSigned 0 8) ⟨s,f,0x2c363⟩).bind (X86Routine.run listed [0x2c371] n) := by rfl

@[local simp] private theorem step_ceiling_2c363 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2c371] (n+1) ⟨s,f,0x2c363⟩ =
      (X86Routine.execute (.control (.block (.store ⟨none,none,0,0x2c034⟩ 3))) ⟨s,f,0x2c369⟩).bind (X86Routine.run listed [0x2c371] n) := by rfl

@[local simp] private theorem step_ceiling_2c369 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2c371] (n+1) ⟨s,f,0x2c369⟩ =
      (X86Routine.execute (.jump 6) ⟨s,f,0x2c36b⟩).bind (X86Routine.run listed [0x2c371] n) := by rfl

@[local simp] private theorem step_ceiling_2c36b (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2c371] (n+1) ⟨s,f,0x2c36b⟩ =
      (X86Routine.execute (.control (.block (.store ⟨none,none,0,0x2c034⟩ 1))) ⟨s,f,0x2c371⟩).bind (X86Routine.run listed [0x2c371] n) := by rfl
@[local simp] private theorem stop_ceiling_2c371 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2c371] n ⟨s,f,0x2c371⟩=some ⟨s,f,0x2c371⟩ := by cases n <;> rfl

theorem ceiling_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x2c371] 8 ⟨s,f,0x2c353⟩=some (ceiling s) := by
  have run : X86Routine.run listed [0x2c371] 8 ⟨s,f,0x2c353⟩=some (ceiling s) := by
    by_cases le : ((ceilingInputs s).regs 1).toInt≤((ceilingInputs s).regs 3).toInt
    all_goals
      simp [ceilingInputs,put,write,-Int.not_le] at le
    all_goals
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
        X86Block.Address.eval,X86.execute,blockPreservesFlags,ceiling,ceilingInputs,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge,le,put,write,-BitVec.toInt_add]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

@[local simp] private theorem step_floor_2c371 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2c393] (n+1) ⟨s,f,0x2c371⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 3 0 0)))) ⟨s,f,0x2c373⟩).bind (X86Routine.run listed [0x2c393] n) := by rfl

@[local simp] private theorem step_floor_2c373 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2c393] (n+1) ⟨s,f,0x2c373⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 6 2 0)))) ⟨s,f,0x2c375⟩).bind (X86Routine.run listed [0x2c393] n) := by rfl

@[local simp] private theorem step_floor_2c375 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2c393] (n+1) ⟨s,f,0x2c375⟩ =
      (X86Routine.execute (.compareRegisters 3 6) ⟨s,f,0x2c377⟩).bind (X86Routine.run listed [0x2c393] n) := by rfl

@[local simp] private theorem step_floor_2c377 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2c393] (n+1) ⟨s,f,0x2c377⟩ =
      (X86Routine.execute (.jumpSigned 1 14) ⟨s,f,0x2c379⟩).bind (X86Routine.run listed [0x2c393] n) := by rfl

@[local simp] private theorem step_floor_2c379 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2c393] (n+1) ⟨s,f,0x2c379⟩ =
      (X86Routine.execute (.control (.block (.store ⟨none,none,0,0x2c030⟩ 3))) ⟨s,f,0x2c37f⟩).bind (X86Routine.run listed [0x2c393] n) := by rfl

@[local simp] private theorem step_floor_2c37f (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2c393] (n+1) ⟨s,f,0x2c37f⟩ =
      (X86Routine.execute (.control (.block (.store ⟨none,none,0,0x2c02c⟩ 6))) ⟨s,f,0x2c385⟩).bind (X86Routine.run listed [0x2c393] n) := by rfl

@[local simp] private theorem step_floor_2c385 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2c393] (n+1) ⟨s,f,0x2c385⟩ =
      (X86Routine.execute (.jump 12) ⟨s,f,0x2c387⟩).bind (X86Routine.run listed [0x2c393] n) := by rfl

@[local simp] private theorem step_floor_2c387 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2c393] (n+1) ⟨s,f,0x2c387⟩ =
      (X86Routine.execute (.control (.block (.store ⟨none,none,0,0x2c030⟩ 6))) ⟨s,f,0x2c38d⟩).bind (X86Routine.run listed [0x2c393] n) := by rfl

@[local simp] private theorem step_floor_2c38d (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2c393] (n+1) ⟨s,f,0x2c38d⟩ =
      (X86Routine.execute (.control (.block (.store ⟨none,none,0,0x2c02c⟩ 3))) ⟨s,f,0x2c393⟩).bind (X86Routine.run listed [0x2c393] n) := by rfl
@[local simp] private theorem stop_floor_2c393 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2c393] n ⟨s,f,0x2c393⟩=some ⟨s,f,0x2c393⟩ := by cases n <;> rfl

theorem floor_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x2c393] 7 ⟨s,f,0x2c371⟩=some (floor s) := by
  have run : X86Routine.run listed [0x2c393] 7 ⟨s,f,0x2c371⟩=some (floor s) := by
    by_cases le : ((floorInputs s).regs 3).toInt≤((floorInputs s).regs 6).toInt
    all_goals
      simp [floorInputs,put,write,-Int.not_le] at le
    all_goals
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
        X86Block.Address.eval,X86.execute,blockPreservesFlags,floor,floorInputs,cmp32_signed_le,le,put,write,-BitVec.toInt_add]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

@[local simp] private theorem step_range_2c393 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2c39f] (n+1) ⟨s,f,0x2c393⟩ =
      (X86Routine.execute (.control (.block (.load 2 ⟨none,none,0,0x2c034⟩))) ⟨s,f,0x2c399⟩).bind (X86Routine.run listed [0x2c39f] n) := by rfl

@[local simp] private theorem step_range_2c399 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2c39f] (n+1) ⟨s,f,0x2c399⟩ =
      (X86Routine.execute (.subMemory 2 ⟨none,none,0,0x2c030⟩) ⟨s,f,0x2c39f⟩).bind (X86Routine.run listed [0x2c39f] n) := by rfl
@[local simp] private theorem stop_range_2c39f (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2c39f] n ⟨s,f,0x2c39f⟩=some ⟨s,f,0x2c39f⟩ := by cases n <;> rfl

theorem range_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x2c39f] 2 ⟨s,f,0x2c393⟩=some (range s) := by
  have run : X86Routine.run listed [0x2c39f] 2 ⟨s,f,0x2c393⟩=some (range s) := by
    
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
        X86Block.Address.eval,X86.execute,blockPreservesFlags,range,put,write,-BitVec.toInt_add]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

@[local simp] private theorem step_neighbor_gate_26fc4 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x26fdd,0x26fec] (n+1) ⟨s,f,0x26fc4⟩ =
      (X86Routine.execute (.control (.block (.legacy (.movsx16 0 2 22)))) ⟨s,f,0x26fc8⟩).bind (X86Routine.run listed [0x26fdd,0x26fec] n) := by rfl

@[local simp] private theorem step_neighbor_gate_26fc8 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x26fdd,0x26fec] (n+1) ⟨s,f,0x26fc8⟩ =
      (X86Routine.execute (.multiplyImmediate 0 0 18) ⟨s,f,0x26fcb⟩).bind (X86Routine.run listed [0x26fdd,0x26fec] n) := by rfl

@[local simp] private theorem step_neighbor_gate_26fcb (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x26fdd,0x26fec] (n+1) ⟨s,f,0x26fcb⟩ =
      (X86Routine.execute (.control (.block (.load 7 ⟨none,none,0,0x2c118⟩))) ⟨s,f,0x26fd1⟩).bind (X86Routine.run listed [0x26fdd,0x26fec] n) := by rfl

@[local simp] private theorem step_neighbor_gate_26fd1 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x26fdd,0x26fec] (n+1) ⟨s,f,0x26fd1⟩ =
      (X86Routine.execute (.control (.block (.arithmetic (.add 0 7)))) ⟨s,f,0x26fd3⟩).bind (X86Routine.run listed [0x26fdd,0x26fec] n) := by rfl

@[local simp] private theorem step_neighbor_gate_26fd3 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x26fdd,0x26fec] (n+1) ⟨s,f,0x26fd3⟩ =
      (X86Routine.execute (.control (.block (.store ⟨some 4,none,0,0⟩ 7))) ⟨s,f,0x26fd6⟩).bind (X86Routine.run listed [0x26fdd,0x26fec] n) := by rfl

@[local simp] private theorem step_neighbor_gate_26fd6 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x26fdd,0x26fec] (n+1) ⟨s,f,0x26fd6⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 7 0 14)))) ⟨s,f,0x26fd9⟩).bind (X86Routine.run listed [0x26fdd,0x26fec] n) := by rfl

@[local simp] private theorem step_neighbor_gate_26fd9 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x26fdd,0x26fec] (n+1) ⟨s,f,0x26fd9⟩ =
      (X86Routine.execute (.compareRegisters 3 7) ⟨s,f,0x26fdb⟩).bind (X86Routine.run listed [0x26fdd,0x26fec] n) := by rfl

@[local simp] private theorem step_neighbor_gate_26fdb (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x26fdd,0x26fec] (n+1) ⟨s,f,0x26fdb⟩ =
      (X86Routine.execute (.control (.jumpZero false 15)) ⟨s,f,0x26fdd⟩).bind (X86Routine.run listed [0x26fdd,0x26fec] n) := by rfl
@[local simp] private theorem stop_neighbor_gate_26fdd (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x26fdd,0x26fec] n ⟨s,f,0x26fdd⟩=some ⟨s,f,0x26fdd⟩ := by cases n <;> rfl
@[local simp] private theorem stop_neighbor_gate_26fec (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x26fdd,0x26fec] n ⟨s,f,0x26fec⟩=some ⟨s,f,0x26fec⟩ := by cases n <;> rfl

theorem neighbor_gate_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x26fdd,0x26fec] 8 ⟨s,f,0x26fc4⟩=some (neighborGate s) := by
  have run : X86Routine.run listed [0x26fdd,0x26fec] 8 ⟨s,f,0x26fc4⟩=some (neighborGate s) := by
    by_cases eq : (neighborInputs s).regs 3=(neighborInputs s).regs 7
    all_goals
      simp [neighborInputs,put,write] at eq
    all_goals
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
        X86Block.Address.eval,X86.execute,blockPreservesFlags,neighborGate,neighborInputs,cmp32_zero,eq,put,write,-BitVec.toInt_add]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

@[local simp] private theorem step_back_neighbor_26fdd (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x26fee] (n+1) ⟨s,f,0x26fdd⟩ =
      (X86Routine.execute (.control (.block (.legacy (.movsx16 0 2 24)))) ⟨s,f,0x26fe1⟩).bind (X86Routine.run listed [0x26fee] n) := by rfl

@[local simp] private theorem step_back_neighbor_26fe1 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x26fee] (n+1) ⟨s,f,0x26fe1⟩ =
      (X86Routine.execute (.multiplyImmediate 0 0 18) ⟨s,f,0x26fe4⟩).bind (X86Routine.run listed [0x26fee] n) := by rfl

@[local simp] private theorem step_back_neighbor_26fe4 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x26fee] (n+1) ⟨s,f,0x26fe4⟩ =
      (X86Routine.execute (.addMemory 0 ⟨some 4,none,0,0⟩) ⟨s,f,0x26fe7⟩).bind (X86Routine.run listed [0x26fee] n) := by rfl

@[local simp] private theorem step_back_neighbor_26fe7 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x26fee] (n+1) ⟨s,f,0x26fe7⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 0 0 14)))) ⟨s,f,0x26fea⟩).bind (X86Routine.run listed [0x26fee] n) := by rfl

@[local simp] private theorem step_back_neighbor_26fea (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x26fee] (n+1) ⟨s,f,0x26fea⟩ =
      (X86Routine.execute (.jump 2) ⟨s,f,0x26fec⟩).bind (X86Routine.run listed [0x26fee] n) := by rfl
@[local simp] private theorem stop_back_neighbor_26fee (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x26fee] n ⟨s,f,0x26fee⟩=some ⟨s,f,0x26fee⟩ := by cases n <;> rfl

theorem back_neighbor_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x26fee] 5 ⟨s,f,0x26fdd⟩=some (backNeighbor s) := by
  have run : X86Routine.run listed [0x26fee] 5 ⟨s,f,0x26fdd⟩=some (backNeighbor s) := by
    
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
        X86Block.Address.eval,X86.execute,blockPreservesFlags,backNeighbor,put,write,-BitVec.toInt_add]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

@[local simp] private theorem step_front_neighbor_26fec (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x26fee] (n+1) ⟨s,f,0x26fec⟩ =
      (X86Routine.execute (.control (.block (.legacy (.mov 0 7)))) ⟨s,f,0x26fee⟩).bind (X86Routine.run listed [0x26fee] n) := by rfl
@[local simp] private theorem stop_front_neighbor_26fee (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x26fee] n ⟨s,f,0x26fee⟩=some ⟨s,f,0x26fee⟩ := by cases n <;> rfl

theorem front_neighbor_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x26fee] 1 ⟨s,f,0x26fec⟩=some (frontNeighbor s f) := by
  have run : X86Routine.run listed [0x26fee] 1 ⟨s,f,0x26fec⟩=some (frontNeighbor s f) := by
    
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
        X86Block.Address.eval,X86.execute,blockPreservesFlags,frontNeighbor,put,write,-BitVec.toInt_add]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

theorem return_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 6 ⟨s,f,0x2c39f⟩ (returned s f) := by
  let a := {s with memory := store32 s.memory 0x2c038 (s.regs 2)}
  let b := PspriteLoop.popped a 6
  let c := PspriteLoop.popped b 2
  let d := PspriteLoop.popped c 1
  let e := PspriteLoop.popped d 3
  have p : X86Routine.Prefix listed [] 6 ⟨s,f,0x2c39f⟩ (returned s f) := by
    apply X86Routine.Prefix.step (middle := ⟨a,f,0x2c3a5⟩) (by simp) rfl (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,a])
    apply X86Routine.Prefix.step (middle := ⟨b,f,0x2c3a6⟩) (by simp) rfl rfl
    apply X86Routine.Prefix.step (middle := ⟨c,f,0x2c3a7⟩) (by simp) rfl rfl
    apply X86Routine.Prefix.step (middle := ⟨d,f,0x2c3a8⟩) (by simp) rfl rfl
    apply X86Routine.Prefix.step (middle := ⟨e,f,0x2c3a9⟩) (by simp) rfl rfl
    apply X86Routine.Prefix.step (middle := returned s f) (by simp) rfl rfl
    exact X86Routine.Prefix.nil _
  exact p.transfer program [] decoded (by simp)
end Doom.Proofs.NoiseOpening
