import Doom.Proofs.E1M1AimOpeningFrame
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalAimDistance
open Verification X86 X86Memory X86Control BlockSummary
attribute [local irreducible] load32 store32
def code : List UInt8 := [0xa1,0xb8,0xb9,0x2,0x0,0x8b,0x1a,0xf7,0xeb,0xf,0xac,0xd0,0x10,0x89,0xc2]
def bytesProgram (bytes : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2b797≤pc ∧ pc<0x2b7a6 then X86Routine.decodeAt bytes (pc-0x2b797) else none
def program := bytesProgram code
def listed : X86Routine.Program
  | 0x2b797 => some (.control (.block (.load 0 ⟨none,none,0,0x2b9b8⟩)),5)
  | 0x2b79c => some (.control (.block (.legacy (.load 3 2 0))),2)
  | 0x2b79e => some (.control (.block (.arithmetic (.imul 3))),2)
  | 0x2b7a0 => some (.control (.block (.arithmetic (.shrd 0 2 16))),4)
  | 0x2b7a4 => some (.control (.block (.legacy (.mov 2 0))),2)
  | _ => none

theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def range (s : X86Memory.State) := load32 s.memory (0x2b9b8#32)
def fraction (s : X86Memory.State) := load32 s.memory (s.regs 2)
def first (s : X86Memory.State) := put s 0 (range s)
def inputs (s : X86Memory.State) := put (first s) 3 (fraction s)
def product (s : X86Memory.State) := X86Block.execute (.arithmetic (.imul 3)) (inputs s)
def shifted (s : X86Memory.State) := multiply (inputs s)
def result (s : X86Memory.State) := put (shifted s) 2 ((shifted s).regs 0)

theorem execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 5 ⟨s,f,0x2b797⟩ ⟨result s,none,0x2b7a6⟩ := by
  have run : X86Routine.Prefix listed [] 5 ⟨s,f,0x2b797⟩ ⟨result s,none,0x2b7a6⟩ := by
    apply X86Routine.Prefix.step (middle := ⟨first s,f,0x2b79c⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,first,range,inputs,fraction,product,result])
    apply X86Routine.Prefix.step (middle := ⟨inputs s,f,0x2b79e⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,first,range,inputs,fraction,product,result])
    apply X86Routine.Prefix.step (middle := ⟨product s,none,0x2b7a0⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,first,range,inputs,fraction,product,result])
    apply X86Routine.Prefix.step (middle := ⟨shifted s,none,0x2b7a4⟩) (by simp) (by rfl) (by
      change some (⟨X86Block.execute (.arithmetic (.shrd 0 2 16)) (product s),none,0x2b7a4⟩ : X86Control.State)=_
      simp only [product,show (0 : Fin 8)=eax from rfl,show (2 : Fin 8)=edx from rfl,multiply_correct]
      rfl)
    apply X86Routine.Prefix.step (middle := ⟨result s,none,0x2b7a6⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,first,range,inputs,fraction,product,result])
    exact .nil _
  exact run.transfer program [] decoded (by simp)

/-- The inlined product is the actual runtime Fixed multiplication, for all
input bit patterns. Memory and all registers except EAX/EDX/EBX are unchanged. -/
theorem arithmetic (s : X86Memory.State) (distance frac : Fixed)
    (r : range s=distance.raw.toBitVec) (f : fraction s=frac.raw.toBitVec) :
    (result s).regs 0=(distance*frac).raw.toBitVec ∧
    (result s).regs 2=(distance*frac).raw.toBitVec ∧
    (result s).memory=s.memory ∧
    (∀ reg, reg≠0 → reg≠2 → reg≠3 → (result s).regs reg=s.regs reg) := by
  simp [result,shifted,multiply,inputs,first,put,write,eax,edx,ebx,mulWord,r,f]
  constructor
  · rfl
  · intro reg h0 h2 h3; simp [h0,h2,h3]
end Doom.Proofs.OriginalAimDistance
