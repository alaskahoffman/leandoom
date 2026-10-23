import Doom.Proofs.E1M1AimTextureDash
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalTextureTable
open Verification X86 X86Memory X86Control BlockSummary
def tableBytes : List UInt8 := [0x8b,0x15,0xe4,0x0,0x3,0x0,0x31,0xc9,0x85,0xd2,0x7e,0x30,0x31,0xf6,0xa1,0xe0,0x0,0x3,0x0,0xbb,0x8,0x0,0x0,0x0,0x89,0xfa,0x8b,0x4,0x6,0xe8,0x6a,0xd2,0x0,0x0]
def missingBytes : List UInt8 := [0xb8,0xff,0xff,0xff,0xff]
def bytesProgram (table missing : List UInt8) : X86Routine.Program := fun pc =>
  if 0x34700≤pc ∧ pc<0x34722 then X86Routine.decodeAt table (pc-0x34700)
  else if 0x3473c≤pc ∧ pc<0x34741 then X86Routine.decodeAt missing (pc-0x3473c) else none
def program := bytesProgram tableBytes missingBytes
def listed : X86Routine.Program
  | 0x34700 => some (.control (.block (.load 2 ⟨none,none,0,0x300e4⟩)),6)
  | 0x34706 => some (.xorRegister 1 1,2)
  | 0x34708 => some (.control (.testWord 2 2),2)
  | 0x3470a => some (.jumpSigned 1 48,2)
  | 0x3470c => some (.xorRegister 6 6,2)
  | 0x3470e => some (.control (.block (.load 0 ⟨none,none,0,0x300e0⟩)),5)
  | 0x34713 => some (.immediate 3 8,5)
  | 0x34718 => some (.control (.block (.legacy (.mov 2 7))),2)
  | 0x3471a => some (.control (.block (.load 0 ⟨some 6,some 0,0,0⟩)),3)
  | 0x3471d => some (.call 53866,5)
  | 0x3473c => some (.immediate 0 0xffffffff,5)
  | _ => none
theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def count (s : X86Memory.State) : Word := load32 s.memory 0x300e4
def tested (s : X86Memory.State) : X86Control.State :=
  ⟨put (put s 2 (count s)) 1 0,some (logical32 (count s)),
    if (count s).toInt≤0 then 0x3473c else 0x3470c⟩
def missing (s : X86Memory.State) (f : Option Flags) : X86Control.State :=
  ⟨put s 0 0xffffffff,f,0x34741⟩
def firstTexture (s : X86Memory.State) : Word := load32 s.memory (load32 s.memory 0x300e0)
def comparison (s : X86Memory.State) : X86Control.State :=
  ⟨X86Routine.pushWord (put (put (put (put s 6 0) 0 (firstTexture s)) 3 8) 2 (s.regs 7))
    0x34722,some (logical32 0),0x4198c⟩
private theorem one_step (p : X86Routine.Program) (exits : List Nat) (n : Nat)
    (s : X86Control.State) (op : X86Routine.Op) (len : Nat)
    (active : s.pc∉exits) (decode : p s.pc=some (op,len)) :
    X86Routine.run p exits (n+1) s=
      (X86Routine.execute op {s with pc:=s.pc+len}).bind (X86Routine.run p exits n) := by
  rw [X86Routine.run,if_neg active,decode]; rfl
@[local simp] private theorem step_34700 (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x34700∉exits) :
    X86Routine.run listed exits (n+1) ⟨s,f,0x34700⟩=
      (X86Routine.execute (.control (.block (.load 2 ⟨none,none,0,0x300e4⟩))) ⟨s,f,0x34706⟩).bind (X86Routine.run listed exits n) := by
  exact @one_step listed exits n ⟨s,f,0x34700⟩ (.control (.block (.load 2 ⟨none,none,0,0x300e4⟩))) 6 h (by rfl)
@[local simp] private theorem step_34706 (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x34706∉exits) :
    X86Routine.run listed exits (n+1) ⟨s,f,0x34706⟩=
      (X86Routine.execute (.xorRegister 1 1) ⟨s,f,0x34708⟩).bind (X86Routine.run listed exits n) := by
  exact @one_step listed exits n ⟨s,f,0x34706⟩ (.xorRegister 1 1) 2 h (by rfl)
@[local simp] private theorem step_34708 (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x34708∉exits) :
    X86Routine.run listed exits (n+1) ⟨s,f,0x34708⟩=
      (X86Routine.execute (.control (.testWord 2 2)) ⟨s,f,0x3470a⟩).bind (X86Routine.run listed exits n) := by
  exact @one_step listed exits n ⟨s,f,0x34708⟩ (.control (.testWord 2 2)) 2 h (by rfl)
@[local simp] private theorem step_3470a (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x3470a∉exits) :
    X86Routine.run listed exits (n+1) ⟨s,f,0x3470a⟩=
      (X86Routine.execute (.jumpSigned 1 48) ⟨s,f,0x3470c⟩).bind (X86Routine.run listed exits n) := by
  exact @one_step listed exits n ⟨s,f,0x3470a⟩ (.jumpSigned 1 48) 2 h (by rfl)
@[local simp] private theorem step_3470c (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x3470c∉exits) :
    X86Routine.run listed exits (n+1) ⟨s,f,0x3470c⟩=
      (X86Routine.execute (.xorRegister 6 6) ⟨s,f,0x3470e⟩).bind (X86Routine.run listed exits n) := by
  exact @one_step listed exits n ⟨s,f,0x3470c⟩ (.xorRegister 6 6) 2 h (by rfl)
@[local simp] private theorem step_3470e (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x3470e∉exits) :
    X86Routine.run listed exits (n+1) ⟨s,f,0x3470e⟩=
      (X86Routine.execute (.control (.block (.load 0 ⟨none,none,0,0x300e0⟩))) ⟨s,f,0x34713⟩).bind (X86Routine.run listed exits n) := by
  exact @one_step listed exits n ⟨s,f,0x3470e⟩ (.control (.block (.load 0 ⟨none,none,0,0x300e0⟩))) 5 h (by rfl)
@[local simp] private theorem step_34713 (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x34713∉exits) :
    X86Routine.run listed exits (n+1) ⟨s,f,0x34713⟩=
      (X86Routine.execute (.immediate 3 8) ⟨s,f,0x34718⟩).bind (X86Routine.run listed exits n) := by
  exact @one_step listed exits n ⟨s,f,0x34713⟩ (.immediate 3 8) 5 h (by rfl)
@[local simp] private theorem step_34718 (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x34718∉exits) :
    X86Routine.run listed exits (n+1) ⟨s,f,0x34718⟩=
      (X86Routine.execute (.control (.block (.legacy (.mov 2 7)))) ⟨s,f,0x3471a⟩).bind (X86Routine.run listed exits n) := by
  exact @one_step listed exits n ⟨s,f,0x34718⟩ (.control (.block (.legacy (.mov 2 7)))) 2 h (by rfl)
@[local simp] private theorem step_3471a (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x3471a∉exits) :
    X86Routine.run listed exits (n+1) ⟨s,f,0x3471a⟩=
      (X86Routine.execute (.control (.block (.load 0 ⟨some 6,some 0,0,0⟩))) ⟨s,f,0x3471d⟩).bind (X86Routine.run listed exits n) := by
  exact @one_step listed exits n ⟨s,f,0x3471a⟩ (.control (.block (.load 0 ⟨some 6,some 0,0,0⟩))) 3 h (by rfl)
@[local simp] private theorem step_3471d (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x3471d∉exits) :
    X86Routine.run listed exits (n+1) ⟨s,f,0x3471d⟩=
      (X86Routine.execute (.call 53866) ⟨s,f,0x34722⟩).bind (X86Routine.run listed exits n) := by
  exact @one_step listed exits n ⟨s,f,0x3471d⟩ (.call 53866) 5 h (by rfl)
@[local simp] private theorem step_3473c (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x3473c∉exits) :
    X86Routine.run listed exits (n+1) ⟨s,f,0x3473c⟩=
      (X86Routine.execute (.immediate 0 0xffffffff) ⟨s,f,0x34741⟩).bind (X86Routine.run listed exits n) := by
  exact @one_step listed exits n ⟨s,f,0x3473c⟩ (.immediate 0 0xffffffff) 5 h (by rfl)
@[local simp] private theorem stopped (s : X86Memory.State) (f : Option Flags)
    (n pc : Nat) (exits : List Nat) (h : pc∈exits) :
    X86Routine.run listed exits n ⟨s,f,pc⟩=some ⟨s,f,pc⟩ := by
  cases n <;> simp [X86Routine.run,h]

theorem gate_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x3473c,0x3470c] 4 ⟨s,f,0x34700⟩=some (tested s) := by
  have run : X86Routine.run listed [0x3473c,0x3470c] 4 ⟨s,f,0x34700⟩=some (tested s) := by
    by_cases h : (load32 s.memory (0x300e4#32)).toInt≤0
    all_goals simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      X86Block.Address.eval,X86.execute,blockPreservesFlags,tested,count,
      PlayerHeight.logical_le,put,write,h]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

theorem missing_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x34741] 1 ⟨s,f,0x3473c⟩=some (missing s f) := by
  have run : X86Routine.run listed [0x34741] 1 ⟨s,f,0x3473c⟩=some (missing s f) := by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      X86.execute,blockPreservesFlags,missing]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

theorem comparison_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x4198c] 6 ⟨s,f,0x3470c⟩=some (comparison s) := by
  have run : X86Routine.run listed [0x4198c] 6 ⟨s,f,0x3470c⟩=some (comparison s) := by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      X86Block.Address.eval,X86.execute,blockPreservesFlags,comparison,firstTexture,
      logical32,X86Routine.pushWord,put,write]
    funext r
    by_cases h : r=0 <;> simp [write,h]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

theorem comparison_arguments (s : X86Memory.State) :
    (comparison s).core.regs 0=firstTexture s ∧ (comparison s).core.regs 2=s.regs 7 ∧
    (comparison s).core.regs 3=8 ∧ (comparison s).core.regs 6=0 ∧
    (comparison s).core.regs 1=s.regs 1 ∧ (comparison s).core.regs 4=s.regs 4-4 ∧
    load32 (comparison s).core.memory ((comparison s).core.regs 4)=0x34722 := by
  simp [comparison,X86Routine.pushWord,put,write,load_store]

theorem comparison_frame (s : X86Memory.State) (a : Word) (safe : Apart a (s.regs 4-4)) :
    load32 (comparison s).core.memory a=load32 s.memory a := by
  exact load_store_apart _ _ _ _ safe

theorem gate_and_missing_memory (s : X86Memory.State) (f : Option Flags) :
    (tested s).core.memory=s.memory ∧ (missing s f).core.memory=s.memory := by constructor <;> rfl
end Doom.Proofs.OriginalTextureTable
