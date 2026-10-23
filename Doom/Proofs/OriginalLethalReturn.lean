import Doom.Proofs.E1M1DeathReturn
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.LethalReturn
open Verification X86 X86Memory X86Control BlockSummary

def jumpBytes : List UInt8 := [0xe9,0x91,0,0,0]
def epilogueBytes : List UInt8 := [0x83,0xc4,0x0c,0x5d,0x5f,0x5e,0xc3]
def bytesProgram (jump epilogue : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2a6b1 ≤ pc ∧ pc < 0x2a6b6 then X86Routine.decodeAt jump (pc-0x2a6b1)
  else if 0x2a747 ≤ pc ∧ pc < 0x2a74e then X86Routine.decodeAt epilogue (pc-0x2a747)
  else none
def program := bytesProgram jumpBytes epilogueBytes

def listed : X86Routine.Program
  | 0x2a6b1 => some (.jump 145,5)
  | 0x2a747 => some (.addImmediate 4 12,3)
  | 0x2a74a => some (.pop 5,1)
  | 0x2a74b => some (.pop 7,1)
  | 0x2a74c => some (.pop 6,1)
  | 0x2a74d => some (.ret,1)
  | _ => none

theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def result (s : X86Memory.State) : X86Control.State :=
  ⟨⟨write (write (write (write s.regs 5 (load32 s.memory (s.regs 4+12)))
    7 (load32 s.memory (s.regs 4+16))) 6 (load32 s.memory (s.regs 4+20)))
    4 (s.regs 4+28),s.memory⟩,none,(load32 s.memory (s.regs 4+24)).toNat⟩

theorem execution (s : X86Memory.State) (f : Option Flags)
    (outside : 0x2a74e ≤ (result s).pc) :
    X86Routine.run listed [(result s).pc] 6 ⟨s,f,0x2a6b1⟩=some (result s) := by
  have neq (pc : Nat) (hi : pc < 0x2a74e) : pc≠(result s).pc := by omega
  have h0 := neq 0x2a6b1 (by decide)
  have h1 := neq 0x2a747 (by decide)
  have h2 := neq 0x2a74a (by decide)
  have h3 := neq 0x2a74b (by decide)
  have h4 := neq 0x2a74c (by decide)
  have h5 := neq 0x2a74d (by decide)
  simp [result] at h0 h1 h2 h3 h4 h5
  simp [X86Routine.run,listed,X86Routine.execute,put,write,result,
    h0,h1,h2,h3,h4,h5,BitVec.add_assoc]
  funext r
  by_cases r4 : r=4 <;> by_cases r5 : r=5 <;> by_cases r6 : r=6 <;>
    by_cases r7 : r=7 <;> simp_all [write]

theorem original_execution (s : X86Memory.State) (f : Option Flags)
    (outside : 0x2a74e ≤ (result s).pc) :
    X86Routine.run program [(result s).pc] 6 ⟨s,f,0x2a6b1⟩=some (result s) := by
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [execution s f outside]; simp)]
  exact execution s f outside

theorem memory_unchanged (s : X86Memory.State) : (result s).core.memory=s.memory := rfl
end Doom.Proofs.LethalReturn
