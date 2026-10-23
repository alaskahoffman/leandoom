import Doom.Proofs.OriginalPlayerArmor
import Doom.Proofs.OriginalFloorDamage
import Doom.Proofs.OriginalHeightFrame

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.PlayerDamageEntry
open Verification X86 X86Memory X86Control BlockSummary

def entryBytes : List UInt8 := [0x56,0x57,0x55,0x83,0xec,0xc,0x89,0xc6,0x89,0x14,0x24,0x89,0x5c,0x24,0x4,0x89,0xcf,0xf6,0x40,0x68,0x4,0xf,0x84,0xcc,0x2,0x0,0x0,0x83,0x7e,0x6c,0x0,0xf,0x8e,0xc2,0x2,0x0,0x0,0xf6,0x46,0x6b,0x1,0x74,0x10,0xc7,0x46,0x50,0x0,0x0,0x0,0x0,0x8b,0x46,0x50,0x89,0x46,0x4c,0x89,0x46,0x48,0x8b,0xae,0x84,0x0,0x0,0x0,0x85,0xed,0x74,0xb,0x83,0x3d,0xe0,0xb3,0x2,0x0,0x0,0x75,0x2,0xd1,0xff,0x83,0x3c,0x24,0x0,0xf,0x84,0xde,0x0,0x0,0x0,0xf6,0x46,0x69,0x10,0xf,0x85,0xd4,0x0,0x0,0x0,0x8b,0x44,0x24,0x4,0x85,0xc0,0x74,0x14,0x8b,0x90,0x84,0x0,0x0,0x0,0x85,0xd2,0x74,0xa,0x83,0x7a,0x70,0x7,0xf,0x84,0xb8,0x0,0x0,0x0,0x8b,0x14,0x24,0x8b,0x4,0x24,0x8b,0x4e,0x10,0x8b,0x5e,0xc,0x8b,0x52,0x10,0x8b,0x40,0xc,0xe8,0x49,0xb2,0x0,0x0,0x89,0xc3,0x8d,0x4,0xbd,0x0,0x0,0x0,0x0,0x29,0xf8,0x8d,0x4,0xc5,0x0,0x0,0x0,0x0,0x8d,0x14,0x7,0xc1,0xe2,0xf,0x8b,0x4e,0x5c,0x89,0xd0,0xc1,0xfa,0x1f,0xf7,0x79,0x48,0x89,0xc1,0x83,0xff,0x28,0x7d,0x36,0x3b,0x7e,0x6c,0x7e,0x31,0x8b,0x46,0x14,0x89,0x44,0x24,0x8,0x8b,0x4,0x24,0x8b,0x54,0x24,0x8,0x8b,0x40,0x14,0x29,0xc2,0x81,0xfa,0x0,0x0,0x40,0x0,0x7e,0x16,0xe8,0x1a,0x9c,0xff,0xff,0xa8,0x1,0x74,0xd,0x8d,0xc,0x8d,0x0,0x0,0x0,0x0,0x81,0xc3,0x0,0x0,0x0,0x80,0xc1,0xeb,0x13,0x8d,0x1c,0x9d,0x0,0x0,0x0,0x0,0x89,0x5c,0x24,0x8,0x8b,0x44,0x24,0x8,0x8b,0x1d,0x84,0x35,0x1,0x0,0x1,0xc3,0x89,0xc8,0x8b,0x1b,0xf7,0xeb,0xf,0xac,0xd0,0x10,0x8b,0x56,0x48,0x1,0xc2,0x8b,0x5c,0x24,0x8,0x89,0x56,0x48,0x89,0xc8,0x8b,0x9b,0x84,0x5a,0x0,0x0,0xf7,0xeb,0xf,0xac,0xd0,0x10,0x1,0x46,0x4c,0x85,0xed,0xf,0x84,0xfa,0x0,0x0,0x0,0x8b,0x46,0x34,0x8b,0x0,0x66,0x83,0x78,0xe,0xb,0x75,0xa,0x8b,0x4e,0x6c,0x39,0xcf,0x7c,0x3,0x8d,0x79,0xff,0x81,0xff,0xe8,0x3,0x0,0x0,0x7d,0x17,0xf6,0x85,0xc4,0x0,0x0,0x0,0x2,0xf,0x85,0x7c,0x1,0x0,0x0,0x83,0x7d,0x2c,0x0,0xf,0x85,0x72,0x1,0x0,0x0]

def tenCallBytes : List UInt8 := [0xe8,0xe5,0xa8,0xff,0xff]

def fiveCallBytes : List UInt8 := [0xe8,0xbb,0xa8,0xff,0xff]

def twentyCallBytes : List UInt8 := [0xe8,0x89,0xa8,0xff,0xff]

def bytesProgram (entry ten five twenty armor : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2a460 ≤ pc ∧ pc < 0x2a5d5 then X86Routine.decodeAt entry (pc-0x2a460)
  else if 0x2a5d5 ≤ pc ∧ pc < 0x2a616 then X86Routine.decodeAt armor (pc-0x2a5d5)
  else if pc = 0x2fb76 then X86Routine.decodeAt ten 0
  else if pc = 0x2fba0 then X86Routine.decodeAt five 0
  else if pc = 0x2fbd2 then X86Routine.decodeAt twenty 0
  else none

def program := bytesProgram entryBytes tenCallBytes fiveCallBytes twentyCallBytes PlayerArmor.code

def guardListed : X86Routine.Program
  | 0x2a471 => some (.testMemoryByte ⟨some 0,none,0,104⟩ 4,4)
  | 0x2a475 => some (.control (.jumpZero true 716),6)
  | 0x2a47b => some (.control (.cmpImmediate ⟨some 6,none,0,108⟩ 0),4)
  | 0x2a47f => some (.jumpSigned 1 706,6)
  | 0x2a485 => some (.testMemoryByte ⟨some 6,none,0,107⟩ 1,4)
  | 0x2a489 => some (.control (.jumpZero true 16),2)
  | 0x2a49b => some (.control (.block (.load 5 ⟨some 6,none,0,132⟩)),6)
  | 0x2a4a1 => some (.control (.testWord 5 5),2)
  | 0x2a4a3 => some (.control (.jumpZero true 11),2)
  | 0x2a4a5 => some (.control (.cmpImmediate ⟨none,none,0,0x2b3e0⟩ 0),7)
  | 0x2a4ac => some (.control (.jumpZero false 2),2)
  | 0x2a4ae => some (.sar 7 1,2)
  | 0x2a4b0 => some (.control (.cmpImmediate ⟨some 4,none,0,0⟩ 0),4)
  | 0x2a4b4 => some (.control (.jumpZero true 222),6)
  | 0x2a598 => some (.control (.testWord 5 5),2)
  | 0x2a59a => some (.control (.jumpZero true 250),6)
  | 0x2a5a0 => some (.control (.block (.legacy (.load 0 6 52))),3)
  | 0x2a5a3 => some (.control (.block (.legacy (.load 0 0 0))),2)
  | 0x2a5a5 => some (.compareHalf ⟨some 0,none,0,14⟩ 11,5)
  | 0x2a5aa => some (.control (.jumpZero false 10),2)
  | 0x2a5b6 => some (.compareRegister 7 1000,6)
  | 0x2a5bc => some (.jumpSigned 0 23,2)
  | 0x2a5be => some (.testMemoryByte ⟨some 5,none,0,196⟩ 2,7)
  | 0x2a5c5 => some (.control (.jumpZero false 380),6)
  | 0x2a5cb => some (.control (.cmpImmediate ⟨some 5,none,0,44⟩ 0),4)
  | 0x2a5cf => some (.control (.jumpZero false 370),6)
  | _ => none

theorem guards_decoded (pc : Nat) (h : guardListed pc ≠ none) : program pc = guardListed pc := by
  fun_cases guardListed pc <;> simp_all [guardListed] <;> decide

def object (s : X86Memory.State) := s.regs 6
def player (s : X86Memory.State) := load32 s.memory (object s+(132#32))
def subsector (s : X86Memory.State) := load32 s.memory (object s+(52#32))
def sector (s : X86Memory.State) := load32 s.memory (subsector s)
def skillDamage (d : Int32) (baby : Bool) := if baby then d >>> 1 else d

def accepted (v : PlayerDamage.State) (d : Int32) (baby : Bool) : Bool :=
  v.shootable && decide (0 < v.health) &&
    !(decide (skillDamage d baby < 1000) && (v.god || v.invulnerable))

structure GuardInputs (s : X86Memory.State) (v : PlayerDamage.State) (d : Int32) (baby : Bool) : Prop where
  target : s.regs 0 = object s
  damage : s.regs 7 = d.toBitVec
  shootable : (s.memory (object s+(104#32)) &&& (4#8) == 0) = !v.shootable
  health : load32 s.memory (object s+(108#32)) = v.health.toBitVec
  noSkull : s.memory (object s+(107#32)) &&& (1#8) = 0
  isPlayer : player s ≠ (0#32)
  skill : (load32 s.memory (0x2b3e0#32) == 0) = baby
  inflictor : load32 s.memory (s.regs 4) = 0
  ordinary : load16 s.memory (sector s+(14#32)) ≠ (11#16)
  god : (s.memory (player s+(196#32)) &&& (2#8) == 0) = !v.god
  invulnerable : (load32 s.memory (player s+(44#32)) == 0) = !v.invulnerable

def early (v : PlayerDamage.State) := !v.shootable || decide (v.health ≤ 0)
def guardObservation (t : X86Control.State) :=
  (t.pc,t.core.regs 7,t.core.regs 5,t.core.regs 6,t.core.regs 4,t.core.memory)
def expected (s : X86Memory.State) (v : PlayerDamage.State) (d : Int32) (baby : Bool) :=
  (if accepted v d baby then 0x2a5d5 else 0x2a747,
   if early v then d.toBitVec else (skillDamage d baby).toBitVec,
   if early v then s.regs 5 else player s,object s,s.regs 4,s.memory)

@[simp] theorem step_0x2a471 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run guardListed [0x2a5d5,0x2a747] (n+1) ⟨s,f,0x2a471⟩ =
      (X86Routine.execute (.testMemoryByte ⟨some 0,none,0,104⟩ 4) ⟨s,f,0x2a475⟩).bind (X86Routine.run guardListed [0x2a5d5,0x2a747] n) := by rfl

@[simp] theorem step_0x2a475 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run guardListed [0x2a5d5,0x2a747] (n+1) ⟨s,f,0x2a475⟩ =
      (X86Routine.execute (.control (.jumpZero true 716)) ⟨s,f,0x2a47b⟩).bind (X86Routine.run guardListed [0x2a5d5,0x2a747] n) := by rfl

@[simp] theorem step_0x2a47b (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run guardListed [0x2a5d5,0x2a747] (n+1) ⟨s,f,0x2a47b⟩ =
      (X86Routine.execute (.control (.cmpImmediate ⟨some 6,none,0,108⟩ 0)) ⟨s,f,0x2a47f⟩).bind (X86Routine.run guardListed [0x2a5d5,0x2a747] n) := by rfl

@[simp] theorem step_0x2a47f (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run guardListed [0x2a5d5,0x2a747] (n+1) ⟨s,f,0x2a47f⟩ =
      (X86Routine.execute (.jumpSigned 1 706) ⟨s,f,0x2a485⟩).bind (X86Routine.run guardListed [0x2a5d5,0x2a747] n) := by rfl

@[simp] theorem step_0x2a485 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run guardListed [0x2a5d5,0x2a747] (n+1) ⟨s,f,0x2a485⟩ =
      (X86Routine.execute (.testMemoryByte ⟨some 6,none,0,107⟩ 1) ⟨s,f,0x2a489⟩).bind (X86Routine.run guardListed [0x2a5d5,0x2a747] n) := by rfl

@[simp] theorem step_0x2a489 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run guardListed [0x2a5d5,0x2a747] (n+1) ⟨s,f,0x2a489⟩ =
      (X86Routine.execute (.control (.jumpZero true 16)) ⟨s,f,0x2a48b⟩).bind (X86Routine.run guardListed [0x2a5d5,0x2a747] n) := by rfl

@[simp] theorem step_0x2a49b (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run guardListed [0x2a5d5,0x2a747] (n+1) ⟨s,f,0x2a49b⟩ =
      (X86Routine.execute (.control (.block (.load 5 ⟨some 6,none,0,132⟩))) ⟨s,f,0x2a4a1⟩).bind (X86Routine.run guardListed [0x2a5d5,0x2a747] n) := by rfl

@[simp] theorem step_0x2a4a1 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run guardListed [0x2a5d5,0x2a747] (n+1) ⟨s,f,0x2a4a1⟩ =
      (X86Routine.execute (.control (.testWord 5 5)) ⟨s,f,0x2a4a3⟩).bind (X86Routine.run guardListed [0x2a5d5,0x2a747] n) := by rfl

@[simp] theorem step_0x2a4a3 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run guardListed [0x2a5d5,0x2a747] (n+1) ⟨s,f,0x2a4a3⟩ =
      (X86Routine.execute (.control (.jumpZero true 11)) ⟨s,f,0x2a4a5⟩).bind (X86Routine.run guardListed [0x2a5d5,0x2a747] n) := by rfl

@[simp] theorem step_0x2a4a5 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run guardListed [0x2a5d5,0x2a747] (n+1) ⟨s,f,0x2a4a5⟩ =
      (X86Routine.execute (.control (.cmpImmediate ⟨none,none,0,0x2b3e0⟩ 0)) ⟨s,f,0x2a4ac⟩).bind (X86Routine.run guardListed [0x2a5d5,0x2a747] n) := by rfl

@[simp] theorem step_0x2a4ac (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run guardListed [0x2a5d5,0x2a747] (n+1) ⟨s,f,0x2a4ac⟩ =
      (X86Routine.execute (.control (.jumpZero false 2)) ⟨s,f,0x2a4ae⟩).bind (X86Routine.run guardListed [0x2a5d5,0x2a747] n) := by rfl

@[simp] theorem step_0x2a4ae (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run guardListed [0x2a5d5,0x2a747] (n+1) ⟨s,f,0x2a4ae⟩ =
      (X86Routine.execute (.sar 7 1) ⟨s,f,0x2a4b0⟩).bind (X86Routine.run guardListed [0x2a5d5,0x2a747] n) := by rfl

@[simp] theorem step_0x2a4b0 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run guardListed [0x2a5d5,0x2a747] (n+1) ⟨s,f,0x2a4b0⟩ =
      (X86Routine.execute (.control (.cmpImmediate ⟨some 4,none,0,0⟩ 0)) ⟨s,f,0x2a4b4⟩).bind (X86Routine.run guardListed [0x2a5d5,0x2a747] n) := by rfl

@[simp] theorem step_0x2a4b4 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run guardListed [0x2a5d5,0x2a747] (n+1) ⟨s,f,0x2a4b4⟩ =
      (X86Routine.execute (.control (.jumpZero true 222)) ⟨s,f,0x2a4ba⟩).bind (X86Routine.run guardListed [0x2a5d5,0x2a747] n) := by rfl

@[simp] theorem step_0x2a598 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run guardListed [0x2a5d5,0x2a747] (n+1) ⟨s,f,0x2a598⟩ =
      (X86Routine.execute (.control (.testWord 5 5)) ⟨s,f,0x2a59a⟩).bind (X86Routine.run guardListed [0x2a5d5,0x2a747] n) := by rfl

@[simp] theorem step_0x2a59a (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run guardListed [0x2a5d5,0x2a747] (n+1) ⟨s,f,0x2a59a⟩ =
      (X86Routine.execute (.control (.jumpZero true 250)) ⟨s,f,0x2a5a0⟩).bind (X86Routine.run guardListed [0x2a5d5,0x2a747] n) := by rfl

@[simp] theorem step_0x2a5a0 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run guardListed [0x2a5d5,0x2a747] (n+1) ⟨s,f,0x2a5a0⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 0 6 52)))) ⟨s,f,0x2a5a3⟩).bind (X86Routine.run guardListed [0x2a5d5,0x2a747] n) := by rfl

@[simp] theorem step_0x2a5a3 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run guardListed [0x2a5d5,0x2a747] (n+1) ⟨s,f,0x2a5a3⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 0 0 0)))) ⟨s,f,0x2a5a5⟩).bind (X86Routine.run guardListed [0x2a5d5,0x2a747] n) := by rfl

@[simp] theorem step_0x2a5a5 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run guardListed [0x2a5d5,0x2a747] (n+1) ⟨s,f,0x2a5a5⟩ =
      (X86Routine.execute (.compareHalf ⟨some 0,none,0,14⟩ 11) ⟨s,f,0x2a5aa⟩).bind (X86Routine.run guardListed [0x2a5d5,0x2a747] n) := by rfl

@[simp] theorem step_0x2a5aa (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run guardListed [0x2a5d5,0x2a747] (n+1) ⟨s,f,0x2a5aa⟩ =
      (X86Routine.execute (.control (.jumpZero false 10)) ⟨s,f,0x2a5ac⟩).bind (X86Routine.run guardListed [0x2a5d5,0x2a747] n) := by rfl

@[simp] theorem step_0x2a5b6 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run guardListed [0x2a5d5,0x2a747] (n+1) ⟨s,f,0x2a5b6⟩ =
      (X86Routine.execute (.compareRegister 7 1000) ⟨s,f,0x2a5bc⟩).bind (X86Routine.run guardListed [0x2a5d5,0x2a747] n) := by rfl

@[simp] theorem step_0x2a5bc (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run guardListed [0x2a5d5,0x2a747] (n+1) ⟨s,f,0x2a5bc⟩ =
      (X86Routine.execute (.jumpSigned 0 23) ⟨s,f,0x2a5be⟩).bind (X86Routine.run guardListed [0x2a5d5,0x2a747] n) := by rfl

@[simp] theorem step_0x2a5be (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run guardListed [0x2a5d5,0x2a747] (n+1) ⟨s,f,0x2a5be⟩ =
      (X86Routine.execute (.testMemoryByte ⟨some 5,none,0,196⟩ 2) ⟨s,f,0x2a5c5⟩).bind (X86Routine.run guardListed [0x2a5d5,0x2a747] n) := by rfl

@[simp] theorem step_0x2a5c5 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run guardListed [0x2a5d5,0x2a747] (n+1) ⟨s,f,0x2a5c5⟩ =
      (X86Routine.execute (.control (.jumpZero false 380)) ⟨s,f,0x2a5cb⟩).bind (X86Routine.run guardListed [0x2a5d5,0x2a747] n) := by rfl

@[simp] theorem step_0x2a5cb (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run guardListed [0x2a5d5,0x2a747] (n+1) ⟨s,f,0x2a5cb⟩ =
      (X86Routine.execute (.control (.cmpImmediate ⟨some 5,none,0,44⟩ 0)) ⟨s,f,0x2a5cf⟩).bind (X86Routine.run guardListed [0x2a5d5,0x2a747] n) := by rfl

@[simp] theorem step_0x2a5cf (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run guardListed [0x2a5d5,0x2a747] (n+1) ⟨s,f,0x2a5cf⟩ =
      (X86Routine.execute (.control (.jumpZero false 370)) ⟨s,f,0x2a5d5⟩).bind (X86Routine.run guardListed [0x2a5d5,0x2a747] n) := by rfl

@[simp] theorem done_0x2a5d5 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run guardListed [0x2a5d5,0x2a747] n ⟨s,f,0x2a5d5⟩ = some ⟨s,f,0x2a5d5⟩ := by cases n <;> rfl

@[simp] theorem done_0x2a747 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run guardListed [0x2a5d5,0x2a747] n ⟨s,f,0x2a747⟩ = some ⟨s,f,0x2a747⟩ := by cases n <;> rfl

theorem half_zero (a b : BitVec 16) : (X86Routine.compare16 a b).zero = (a == b) := by
  apply Bool.eq_iff_iff.mpr
  simp [X86Routine.compare16,BitVec.sub_eq_iff_eq_add]

/-- Entry guards for ordinary floor damage to a player without MF_SKULLFLY.
No call/RNG or game-memory write occurs between this boundary and armor. -/
theorem guards (s : X86Memory.State) (f : Option Flags) (v : PlayerDamage.State) (d : Int32)
    (baby : Bool) (h : GuardInputs s v d baby) :
    (X86Routine.run guardListed [0x2a5d5,0x2a747] 26 ⟨s,f,0x2a471⟩).map guardObservation =
      some (expected s v d baby) := by
  rcases h with ⟨target,damage,shootable,health,noSkull,isPlayer,skill,inflictor,ordinary,god,invulnerable⟩
  dsimp [player,sector,subsector,object] at *
  have skillZero : load32 s.memory (0x2b3e0#32) = (0#32) ↔ baby = true := by
    rw [← beq_iff_eq,skill]
  have hz : (skillDamage d baby).toBitVec = if baby then d.toBitVec.sshiftRight 1 else d.toBitVec := by
    cases baby <;> rfl
  cases hb : baby <;> cases hs : v.shootable <;> cases hg : v.god <;> cases hi : v.invulnerable <;>
    by_cases hh : 0 < v.health.toInt <;> by_cases hd : (skillDamage d baby).toInt < 1000
  all_goals
    simp only [skillDamage,hb,Bool.false_eq_true,ite_false,ite_true] at hd
    have ds : (d.toBitVec.sshiftRight 1).toInt = (d >>> 1).toInt := rfl
    simp [hb,hs,hg,hi] at shootable skill god invulnerable
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      X86Block.Address.eval,put,write,blockPreservesFlags,logical8,logical32,
      cmp32_zero,cmp32_signed_le,PlayerHeight.cmp_ge_prop,half_zero,
      target,damage,shootable,health,noSkull,isPlayer,skillZero,skill,inflictor,ordinary,god,invulnerable,
      guardObservation,expected,accepted,early,object,player,sector,subsector,skillDamage,
      hb,hs,hg,hi,hh,hd,ds,← Int.not_lt,Int32.lt_iff_toInt_lt,Int32.le_iff_toInt_le]

/-- On the live ordinary-floor path, accepted damage enters the real finish
continuation, and rejected damage leaves the complete state and RNG unchanged. -/
theorem live_entry (v : PlayerDamage.State) (d : Int32) (baby chainsaw : Bool) (rng : DoomRandom)
    (skull : v.skullFly = false) (ordinary : v.sectorSpecial ≠ 11) :
    PlayerDamage.apply v d none chainsaw baby rng =
      if accepted v d baby then PlayerDamage.finish v (skillDamage d baby) rng
      else ⟨v,rng,false,false,false⟩ := by
  cases hb : baby <;> cases hs : v.shootable <;> cases hg : v.god <;> cases hi : v.invulnerable <;>
    by_cases hh : v.health ≤ 0 <;> by_cases hd : skillDamage d baby < 1000
  all_goals
    cases v
    simp_all [PlayerDamage.apply,DamageThrust.apply,accepted,skillDamage,Id.run,pure,bind,
      Int32.lt_iff_toInt_lt,Int32.le_iff_toInt_le,← Int.not_lt]


def sites : List Nat := [0x2fb76,0x2fba0,0x2fbd2]
def slots (s : X86Memory.State) : List Word :=
  [s.regs 4-(4#32),s.regs 4-(8#32),s.regs 4-(12#32),s.regs 4-(16#32),s.regs 4-(28#32),s.regs 4-(24#32)]
def saved (s : X86Memory.State) (pc : Nat) : Memory :=
  let m := store32 s.memory (s.regs 4-(4#32)) (BitVec.ofNat 32 (pc+5))
  let m := store32 m (s.regs 4-(8#32)) (s.regs 6)
  let m := store32 m (s.regs 4-(12#32)) (s.regs 7)
  let m := store32 m (s.regs 4-(16#32)) (s.regs 5)
  let m := store32 m (s.regs 4-(28#32)) (s.regs 2)
  store32 m (s.regs 4-(24#32)) (s.regs 3)
def entered (s : X86Memory.State) (pc : Nat) : X86Memory.State :=
  ⟨write (write (write s.regs 4 (s.regs 4-(28#32))) 6 (s.regs 0)) 7 (s.regs 1),saved s pc⟩

theorem call_decoded (pc : Nat) (site : pc ∈ sites) :
    program pc = some (.call ((0x2a460 : Int)-(pc+5)),5) := by
  simp [sites] at site
  rcases site with rfl | rfl | rfl <;> decide

/-- Real floor CALL, saved registers, local allocation, and saved null sources. -/
theorem prologue (s : X86Memory.State) (f : Option Flags) (pc : Nat) (site : pc ∈ sites) :
    X86Routine.Prefix program [0x2a616,0x2a747] 9 ⟨s,f,pc⟩ ⟨entered s pc,none,0x2a471⟩ := by
  let c := X86Routine.pushWord s (BitVec.ofNat 32 (pc+5))
  let p1 := X86Routine.pushWord c (s.regs 6)
  let p2 := X86Routine.pushWord p1 (s.regs 7)
  let p3 := X86Routine.pushWord p2 (s.regs 5)
  let p4 := put p3 4 (p3.regs 4-12)
  let p5 := put p4 6 (s.regs 0)
  let p6 : X86Memory.State := {p5 with memory := store32 p5.memory (p5.regs 4) (s.regs 2)}
  let p7 : X86Memory.State := {p6 with memory := store32 p6.memory (p6.regs 4+4) (s.regs 3)}
  let p8 := put p7 7 (s.regs 1)
  apply X86Routine.Prefix.step (middle := ⟨c,f,0x2a460⟩)
    (by simp [sites] at site; rcases site with rfl|rfl|rfl <;> simp)
    (call_decoded pc site) (by
      simp [sites] at site
      rcases site with rfl|rfl|rfl <;> simp [X86Routine.execute,c])
  apply X86Routine.Prefix.step (middle := ⟨p1,f,0x2a461⟩) (by simp)
    (show program 0x2a460 = some (.push 6,1) from by decide) (by simp [X86Routine.execute,c,p1,X86Routine.pushWord,write])
  apply X86Routine.Prefix.step (middle := ⟨p2,f,0x2a462⟩) (by simp)
    (show program 0x2a461 = some (.push 7,1) from by decide) (by simp [X86Routine.execute,c,p1,p2,X86Routine.pushWord,write])
  apply X86Routine.Prefix.step (middle := ⟨p3,f,0x2a463⟩) (by simp)
    (show program 0x2a462 = some (.push 5,1) from by decide) (by simp [X86Routine.execute,c,p1,p2,p3,X86Routine.pushWord,write])
  apply X86Routine.Prefix.step (middle := ⟨p4,none,0x2a466⟩) (by simp)
    (show program 0x2a463 = some (.addImmediate 4 (-12),3) from by decide) (by simp [X86Routine.execute,p4,BitVec.sub_eq_add_neg])
  apply X86Routine.Prefix.step (middle := ⟨p5,none,0x2a468⟩) (by simp)
    (show program 0x2a466 = some (.control (.block (.legacy (.mov 6 0))),2) from by decide) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,blockPreservesFlags,p5,p4,p3,p2,p1,c,X86Routine.pushWord,put,write])
  apply X86Routine.Prefix.step (middle := ⟨p6,none,0x2a46b⟩) (by simp)
    (show program 0x2a468 = some (.control (.block (.store ⟨some 4,none,0,0⟩ 2)),3) from by decide) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,p6,p5,p4,p3,p2,p1,c,X86Routine.pushWord,put,write])
  apply X86Routine.Prefix.step (middle := ⟨p7,none,0x2a46f⟩) (by simp)
    (show program 0x2a46b = some (.control (.block (.store ⟨some 4,none,0,4⟩ 3)),4) from by decide) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,p7,p6,p5,p4,p3,p2,p1,c,X86Routine.pushWord,put,write])
  apply X86Routine.Prefix.step (middle := ⟨p8,none,0x2a471⟩) (by simp)
    (show program 0x2a46f = some (.control (.block (.legacy (.mov 7 1))),2) from by decide) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,blockPreservesFlags,p8,p7,p6,p5,p4,p3,p2,p1,c,X86Routine.pushWord,put,write])
  have equal : p8 = entered s pc := by
    simp [p8,p7,p6,p5,p4,p3,p2,p1,c,entered,saved,X86Routine.pushWord,put,write,
      BitVec.sub_sub,BitVec.sub_eq_add_neg,BitVec.add_assoc]
    funext r
    by_cases h4 : r = 4 <;> by_cases h6 : r = 6 <;> by_cases h7 : r = 7 <;> simp [write,h4,h6,h7]
  rw [equal]
  exact X86Routine.Prefix.nil _

theorem saved_frame (s : X86Memory.State) (pc : Nat) : PlayerHeight.Frame s.memory (saved s pc) (slots s) := by
  intro a safe
  unfold saved
  repeat rw [load_store_apart _ _ _ _ (safe _ (by simp [slots]))]


def inputPlayer (s : X86Memory.State) := load32 s.memory (s.regs 0+(132#32))
def inputSubsector (s : X86Memory.State) := load32 s.memory (s.regs 0+(52#32))
def inputSector (s : X86Memory.State) := load32 s.memory (inputSubsector s)
def reads (s : X86Memory.State) : List Word :=
  [s.regs 0+104,s.regs 0+108,s.regs 0+107,s.regs 0+132,0x2b3e0,s.regs 0+52,inputSubsector s,
   inputSector s+14,inputSector s+15,inputPlayer s+196,inputPlayer s+44,inputPlayer s+36,inputPlayer s+40]

/-- Initial call-boundary relation, before any CALL/prologue write. Ordinary
floor sectors and normal (non-skull-flying) players are the supported domain. -/
structure Inputs (s : X86Memory.State) (v : PlayerDamage.State) (d : Int32) (baby : Bool) : Prop where
  damage : s.regs 1 = d.toBitVec
  inflictor : s.regs 2 = 0
  source : s.regs 3 = 0
  shootable : (s.memory (s.regs 0+(104#32)) &&& (4#8) == 0) = !v.shootable
  health : load32 s.memory (s.regs 0+(108#32)) = v.health.toBitVec
  noSkull : s.memory (s.regs 0+(107#32)) &&& (1#8) = 0
  liveSkull : v.skullFly = false
  isPlayer : inputPlayer s ≠ (0#32)
  skill : (load32 s.memory (0x2b3e0#32) == 0) = baby
  ordinary : load16 s.memory (inputSector s+(14#32)) ≠ (11#16)
  liveOrdinary : v.sectorSpecial ≠ 11
  god : (s.memory (inputPlayer s+(196#32)) &&& (2#8) == 0) = !v.god
  invulnerable : (load32 s.memory (inputPlayer s+(44#32)) == 0) = !v.invulnerable
  armor : load32 s.memory (inputPlayer s+(36#32)) = v.armor.toBitVec
  armorType : load32 s.memory (inputPlayer s+(40#32)) = v.armorType.toBitVec
  stackSafe : ∀ a, a ∈ reads s → ∀ b, b ∈ slots s → Apart a b

theorem saved_read (s : X86Memory.State) (pc : Nat) (v : PlayerDamage.State) (d : Int32) (baby : Bool)
    (h : Inputs s v d baby) (a : Word) (ha : a ∈ reads s) :
    load32 (saved s pc) a = load32 s.memory a := saved_frame s pc a (h.stackSafe a ha)

theorem saved_byte (s : X86Memory.State) (pc : Nat) (v : PlayerDamage.State) (d : Int32) (baby : Bool)
    (h : Inputs s v d baby) (a : Word) (ha : a ∈ reads s) :
    saved s pc a = s.memory a := (saved_frame s pc).byte a (h.stackSafe a ha)

theorem transport (s : X86Memory.State) (pc : Nat) (v : PlayerDamage.State) (d : Int32) (baby : Bool)
    (h : Inputs s v d baby) : GuardInputs (entered s pc) v d baby := by
  have word := saved_read s pc v d baby h
  have byte := saved_byte s pc v d baby h
  have pl : player (entered s pc) = inputPlayer s := by
    simp only [player,object,entered,write,ite_true,show (6:Reg) ≠ 7 from by decide,ite_false]
    exact word _ (by simp [reads])
  have sub : subsector (entered s pc) = inputSubsector s := by
    simp only [subsector,object,entered,write,ite_true,show (6:Reg) ≠ 7 from by decide,ite_false]
    exact word _ (by simp [reads])
  have sec : sector (entered s pc) = inputSector s := by
    unfold sector
    rw [sub]
    exact word _ (by simp [reads])
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [entered,object,write]
  · simpa [entered,write] using h.damage
  · simpa only [object,entered,write,ite_true,show (6:Reg) ≠ 7 from by decide,ite_false,
      byte (s.regs 0+(104#32)) (by simp [reads])] using h.shootable
  · simpa only [object,entered,write,ite_true,show (6:Reg) ≠ 7 from by decide,ite_false,
      word (s.regs 0+(108#32)) (by simp [reads])] using h.health
  · simpa only [object,entered,write,ite_true,show (6:Reg) ≠ 7 from by decide,ite_false,
      byte (s.regs 0+(107#32)) (by simp [reads])] using h.noSkull
  · simpa [pl] using h.isPlayer
  · simpa only [entered,word (0x2b3e0#32) (by simp [reads])] using h.skill
  · simp only [entered,write,show (4:Reg) ≠ 7 from by decide,show (4:Reg) ≠ 6 from by decide,ite_false,ite_true]
    have apart : Apart (s.regs 4-(28#32)) (s.regs 4-(24#32)) := by
      simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using
        PlayerHeight.slots_apart (s.regs 4-(28#32)) 0 1 (by decide)
    rw [saved,load_store_apart _ _ _ _ apart,load_store,h.inflictor]
  · rw [sec]
    change load16 (saved s pc) (inputSector s+(14#32)) ≠ 11
    simpa [load16,BitVec.add_assoc,byte (inputSector s+(14#32)) (by simp [reads]),
      byte (inputSector s+(15#32)) (by simp [reads])] using h.ordinary
  · rw [pl]
    simpa only [entered,byte (inputPlayer s+(196#32)) (by simp [reads])] using h.god
  · rw [pl]
    simpa only [entered,word (inputPlayer s+(44#32)) (by simp [reads])] using h.invulnerable


theorem guards_active (pc : Nat) (h : guardListed pc ≠ none) : pc ∉ [0x2a616,0x2a747] := by
  fun_cases guardListed pc <;> simp_all [guardListed]

theorem contains_armor (pc : Nat) (h : PlayerArmor.program pc ≠ none) : program pc = PlayerArmor.program pc := by
  unfold PlayerArmor.program at h ⊢
  split at h
  next bound =>
    unfold program bytesProgram
    rw [if_neg (by omega),if_pos bound,if_pos bound]
  next bound => simp_all

theorem armor_active (pc : Nat) (h : PlayerArmor.program pc ≠ none) : pc ∉ [0x2a616,0x2a747] := by
  unfold PlayerArmor.program at h
  split at h
  next bound => simp; omega
  next bound => simp_all

def writes (s : X86Memory.State) := slots s ++ [inputPlayer s+36,inputPlayer s+40]
def observation (s : X86Memory.State) (t : X86Control.State) : Option (Word × Word × Word) :=
  if t.pc = 0x2a747 then none else some
    (t.core.regs 7,load32 t.core.memory (inputPlayer s+36),load32 t.core.memory (inputPlayer s+40))
def answer (v : PlayerDamage.State) (d : Int32) (baby : Bool) : Option (Word × Word × Word) :=
  if accepted v d baby then
    let out := PlayerDamage.absorbArmor v (skillDamage d baby)
    some (out.2.toBitVec,out.1.armor.toBitVec,out.1.armorType.toBitVec)
  else none

/-- Continuous original-byte run: real floor CALL, prologue, entry guards and
armor. The theorem carries the initial relation through all intervening writes. -/
theorem execution_detailed (s : X86Memory.State) (f : Option Flags) (pc : Nat) (site : pc ∈ sites)
    (v : PlayerDamage.State) (d : Int32) (baby : Bool) (h : Inputs s v d baby) :
    ∃ t, X86Routine.run program [0x2a616,0x2a747] 59 ⟨s,f,pc⟩ = some t ∧
      observation s t = answer v d baby ∧
      t.pc = (if accepted v d baby then 0x2a616 else 0x2a747) ∧
      t.core.regs 4 = s.regs 4-(28#32) ∧ t.core.regs 6 = s.regs 0 ∧
      PlayerHeight.Frame s.memory t.core.memory (writes s) ∧
      (accepted v d baby = true → t.core.regs 5 = inputPlayer s) ∧
      PlayerHeight.Frame (saved s pc) t.core.memory [inputPlayer s+36,inputPlayer s+40] := by
  have guardsRun := guards (entered s pc) none v d baby (transport s pc v d baby h)
  cases hr : X86Routine.run guardListed [0x2a5d5,0x2a747] 26 ⟨entered s pc,none,0x2a471⟩ with
  | none => simp [hr] at guardsRun
  | some g =>
    obtain ⟨n,hn,path,_⟩ := X86Routine.run_path hr
    have path := path.transfer program [0x2a616,0x2a747] guards_decoded guards_active
    have pl : player (entered s pc) = inputPlayer s := by
      simp only [player,object,entered,write,ite_true,show (6:Reg) ≠ 7 from by decide,ite_false]
      exact saved_read s pc v d baby h _ (by simp [reads])
    simp only [hr,Option.map_some,Option.some.injEq,guardObservation,expected,Prod.mk.injEq] at guardsRun
    rcases guardsRun with ⟨gpc,gd,gp,go,gs,gm⟩
    have gsp : g.core.regs 4 = s.regs 4-(28#32) := by simpa [entered,write] using gs
    have gobj : g.core.regs 6 = s.regs 0 := by simpa [object,entered,write] using go
    change g.core.memory = saved s pc at gm
    by_cases accept : accepted v d baby = true
    · have notEarly : early v = false := by
        have ha := accept
        simp only [accepted,Bool.and_eq_true,decide_eq_true_eq] at ha
        have pos : 0 < v.health.toInt := by simpa using Int32.lt_iff_toInt_lt.mp ha.1.2
        simp [early,ha.1.1,Int32.le_iff_toInt_le,← Int.not_lt,pos]
      simp only [accept,ite_true,notEarly,Bool.false_eq_true,ite_false,pl] at gpc gd gp
      have armorPoints : PlayerArmor.armor g.core = v.armor.toBitVec := by
        simp only [PlayerArmor.armor,PlayerArmor.pointer,gp,gm]
        rw [saved_read s pc v d baby h (inputPlayer s+(36#32)) (by simp [reads])]
        exact h.armor
      have armorType : PlayerArmor.kind g.core = v.armorType.toBitVec := by
        simp only [PlayerArmor.kind,PlayerArmor.pointer,gp,gm]
        rw [saved_read s pc v d baby h (inputPlayer s+(40#32)) (by simp [reads])]
        exact h.armorType
      have arun := PlayerArmor.original_execution g.core g.flags
      have acorrect := PlayerArmor.correspondence g.core g.flags v (skillDamage d baby) gd armorPoints armorType
      simp only [← gpc] at arun acorrect
      cases ha : X86Routine.run PlayerArmor.program [0x2a616] 24 g with
      | none => simp [ha] at arun
      | some t =>
        obtain ⟨k,hk,apath,_⟩ := X86Routine.run_path ha
        have apath := apath.transfer program [0x2a616,0x2a747] contains_armor armor_active
        simp only [ha,Option.map_some,Option.some.injEq,Prod.mk.injEq] at arun
        rcases arun with ⟨_,tm,tpl,ts,to,tp⟩
        have tail : X86Routine.run program [0x2a616,0x2a747] 24 g = some t :=
          apath.finish (fuel := 0) (by simp [X86Routine.run,tp]) 24 (by omega)
        have rest := path.finish tail 50 (by omega)
        refine ⟨t,(prologue s f pc site).finish rest 59 (by decide),?_,?_,ts.trans gsp,to.trans gobj,?_,(fun _ => tpl.trans gp),?_⟩
        · simpa [ha,observation,answer,accept,tp,PlayerArmor.pointer,gp] using acorrect
        · simp [accept,tp]
        · intro a safe
          rw [tm,PlayerArmor.memory_frame g.core a]
          · rw [gm]
            exact saved_frame s pc a (fun b hb => safe b (by simp [writes,hb]))
          · simpa [PlayerArmor.pointer,gp] using safe (inputPlayer s+36) (by simp [writes])
          · simpa [PlayerArmor.pointer,gp] using safe (inputPlayer s+40) (by simp [writes])
        · intro a safe
          rw [tm,PlayerArmor.memory_frame g.core a]
          · rw [gm]
          · simpa [PlayerArmor.pointer,gp] using safe (inputPlayer s+36) (by simp)
          · simpa [PlayerArmor.pointer,gp] using safe (inputPlayer s+40) (by simp)
    · have reject : accepted v d baby = false := by simpa using accept
      simp only [reject,Bool.false_eq_true,ite_false] at gpc
      have rest : X86Routine.run program [0x2a616,0x2a747] 50 ⟨entered s pc,none,0x2a471⟩ = some g :=
        path.finish (fuel := 0) (by simp [X86Routine.run,gpc]) 50 (by omega)
      refine ⟨g,(prologue s f pc site).finish rest 59 (by decide),?_,?_,gsp,gobj,?_,(by simp [reject]),?_⟩
      · simp [observation,answer,reject,gpc]
      · simp [reject,gpc]
      · rw [gm]
        intro a safe
        exact saved_frame s pc a (fun b hb => safe b (by simp [writes,hb]))
      · rw [gm]
        intro a _
        rfl

theorem execution (s : X86Memory.State) (f : Option Flags) (pc : Nat) (site : pc ∈ sites)
    (v : PlayerDamage.State) (d : Int32) (baby : Bool) (h : Inputs s v d baby) :
    ∃ t, X86Routine.run program [0x2a616,0x2a747] 59 ⟨s,f,pc⟩ = some t ∧
      observation s t = answer v d baby ∧
      t.pc = (if accepted v d baby then 0x2a616 else 0x2a747) ∧
      t.core.regs 4 = s.regs 4-(28#32) ∧ t.core.regs 6 = s.regs 0 ∧
      PlayerHeight.Frame s.memory t.core.memory (writes s) := by
  obtain ⟨t,run,observe,pc',sp,obj,frame,_⟩ := execution_detailed s f pc site v d baby h
  exact ⟨t,run,observe,pc',sp,obj,frame⟩

theorem correspondence (s : X86Memory.State) (f : Option Flags) (pc : Nat) (site : pc ∈ sites)
    (v : PlayerDamage.State) (d : Int32) (baby : Bool) (h : Inputs s v d baby) :
    (X86Routine.run program [0x2a616,0x2a747] 59 ⟨s,f,pc⟩).map (observation s) = some (answer v d baby) := by
  obtain ⟨t,run,observe,_⟩ := execution s f pc site v d baby h
  simp [run,observe]

def liveObservation (v : PlayerDamage.State) (out : PlayerDamage.Result) : Option (Word × Word × Word) :=
  if out.applied then some ((v.health-out.state.health).toBitVec,out.state.armor.toBitVec,out.state.armorType.toBitVec)
  else none

theorem finish_observation (v : PlayerDamage.State) (d : Int32) (rng : DoomRandom) :
    liveObservation v (PlayerDamage.finish v d rng) =
      let a := PlayerDamage.absorbArmor v d
      some (a.2.toBitVec,a.1.armor.toBitVec,a.1.armorType.toBitVec) := by
  have health : (PlayerDamage.absorbArmor v d).1.health = v.health := by
    unfold PlayerDamage.absorbArmor
    split <;> rfl
  have cancel (a b : Int32) : (a-(a-b)).toBitVec = b.toBitVec := by
    simp only [Int32.toBitVec_sub]
    rw [BitVec.sub_eq_iff_eq_add,BitVec.add_comm,BitVec.sub_add_cancel]
  unfold PlayerDamage.finish
  simp only [Id.run,pure,bind]
  split <;> simp [liveObservation,PlayerDamage.bookkeep,health,cancel]

theorem live_answer (v : PlayerDamage.State) (d : Int32) (baby : Bool) (rng : DoomRandom)
    (skull : v.skullFly = false) (ordinary : v.sectorSpecial ≠ 11) :
    liveObservation v (PlayerDamage.apply v d none false baby rng) = answer v d baby := by
  rw [live_entry v d baby false rng skull ordinary]
  by_cases h : accepted v d baby = true
  · simp [h,answer,finish_observation]
  · simp [h,answer,liveObservation]

/-- The observed damage/armor result equals actual live PlayerDamage.apply.
The health difference here only recovers damage remaining after armor; this
is not a proof of the original health-writing or pain/death instructions. -/
theorem live_correspondence (s : X86Memory.State) (f : Option Flags) (pc : Nat) (site : pc ∈ sites)
    (v : PlayerDamage.State) (d : Int32) (baby : Bool) (rng : DoomRandom) (h : Inputs s v d baby) :
    (X86Routine.run program [0x2a616,0x2a747] 59 ⟨s,f,pc⟩).map (observation s) =
      some (liveObservation v (PlayerDamage.apply v d none false baby rng)) := by
  rw [live_answer v d baby rng h.liveSkull h.liveOrdinary]
  exact correspondence s f pc site v d baby h

/-- Every nonzero request produced by the preceding proved floor decision
reaches one of these exact CALL sites with null source and inflictor. -/
theorem floor_handoff (kind : FloorDamage.Kind) (s : X86Memory.State) (f : Option Flags)
    (time : Nat) (suit : Bool) (rng : DoomRandom) (h : FloorDamage.Inputs s time suit rng)
    (due : FloorDamage.requested (FloorDamage.result kind s rng) ≠ 0) :
    let t := FloorDamage.result kind s rng
    t.pc ∈ sites ∧ t.core.regs 0 = load32 s.memory (FloorDamage.player s) ∧
      t.core.regs 2 = (0#32) ∧ t.core.regs 3 = (0#32) := by
  have run := FloorDamage.execution kind s f rng h.random
  obtain ⟨_,_,_,done⟩ := X86Routine.run_path run
  have skip : (FloorDamage.result kind s rng).pc ≠ 0x2fc39 := by
    intro eq
    exact due (by simp [FloorDamage.requested,eq])
  have site : (FloorDamage.result kind s rng).pc ∈ sites := by
    simpa [FloorDamage.exits,sites,skip] using done
  have args := FloorDamage.damage_arguments kind s time suit rng h due
  exact ⟨site,args.1,args.2.1,args.2.2.1⟩

end Doom.Proofs.PlayerDamageEntry
