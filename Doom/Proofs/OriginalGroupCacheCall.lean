import Doom.Proofs.OriginalGroupRestore
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000
namespace Doom.Proofs.OriginalGroupCacheCall
open Verification X86 X86Memory X86Control BlockSummary

def cacheBytes : List UInt8 := [0xa1,0x94,0x4f,0x7,0,0x8b,0x14,0x6,0x89,0xc8,0xe8,0xa0,0xfe,0xff,0xff]
def bytesProgram (bytes : List UInt8) : X86Routine.Program := fun pc =>
  if 0x38d41≤pc ∧ pc<0x38d50 then X86Routine.decodeAt bytes (pc-0x38d41) else none
def program := bytesProgram cacheBytes
def listed : X86Routine.Program
  | 0x38d41 => some (.control (.block (.load 0 ⟨none,none,0,0x74f94⟩)),5)
  | 0x38d46 => some (.control (.block (.load 2 ⟨some 6,some 0,0,0⟩)),3)
  | 0x38d49 => some (.control (.block (.legacy (.mov 0 1))),2)
  | 0x38d4b => some (.call (-352),5)
  | _ => none

theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def cell (s : X86Memory.State) := s.regs 6+load32 s.memory 0x74f94
def payload (s : X86Memory.State) := load32 s.memory (cell s)
def prepared (s : X86Memory.State) := put (put s 2 (payload s)) 0 (s.regs 1)
def result (s : X86Memory.State) (f : Option Flags) : X86Control.State :=
  ⟨X86Routine.pushWord (prepared s) 0x38d50,f,0x38bf0⟩

@[local simp] private theorem step_38d41 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x38bf0] (n+1) ⟨s,f,0x38d41⟩=
      (X86Routine.execute (.control (.block (.load 0 ⟨none,none,0,0x74f94⟩)))
        ⟨s,f,0x38d46⟩).bind (X86Routine.run listed [0x38bf0] n) := by rfl
@[local simp] private theorem step_38d46 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x38bf0] (n+1) ⟨s,f,0x38d46⟩=
      (X86Routine.execute (.control (.block (.load 2 ⟨some 6,some 0,0,0⟩)))
        ⟨s,f,0x38d49⟩).bind (X86Routine.run listed [0x38bf0] n) := by rfl
@[local simp] private theorem step_38d49 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x38bf0] (n+1) ⟨s,f,0x38d49⟩=
      (X86Routine.execute (.control (.block (.legacy (.mov 0 1))))
        ⟨s,f,0x38d4b⟩).bind (X86Routine.run listed [0x38bf0] n) := by rfl
@[local simp] private theorem step_38d4b (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x38bf0] (n+1) ⟨s,f,0x38d4b⟩=
      (X86Routine.execute (.call (-352)) ⟨s,f,0x38d50⟩).bind
        (X86Routine.run listed [0x38bf0] n) := by
  rw [X86Routine.run,if_neg (by change (0x38d4b : Nat)∉[0x38bf0]; decide)]
  rfl
@[local simp] private theorem stopped (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x38bf0] n ⟨s,f,0x38bf0⟩=some ⟨s,f,0x38bf0⟩ := by cases n <;> rfl

theorem execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x38bf0] 4 ⟨s,f,0x38d41⟩=some (result s f) := by
  have run : X86Routine.run listed [0x38bf0] 4 ⟨s,f,0x38d41⟩=some (result s f) := by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      X86Block.Address.eval,blockPreservesFlags,result,prepared,payload,cell,
      X86Routine.pushWord,put,write]
    funext r
    by_cases h : r=0 <;> simp [write,h]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

theorem arguments (s : X86Memory.State) (f : Option Flags) :
    (result s f).core.regs 0=s.regs 1 ∧ (result s f).core.regs 2=payload s ∧
    (result s f).core.regs 4=s.regs 4-4 := by simp [result,prepared,X86Routine.pushWord,put,write]

theorem return_address (s : X86Memory.State) (f : Option Flags) :
    load32 (result s f).core.memory ((result s f).core.regs 4)=0x38d50 := by
  simpa [result,prepared,X86Routine.pushWord,put,write] using
    load_store s.memory (s.regs 4-(4#32)) (0x38d50#32)

theorem frame (s : X86Memory.State) (f : Option Flags) (a : Word)
    (safe : Apart a (s.regs 4-4)) : load32 (result s f).core.memory a=load32 s.memory a := by
  exact load_store_apart s.memory (s.regs 4-4) a 0x38d50 safe
end Doom.Proofs.OriginalGroupCacheCall
