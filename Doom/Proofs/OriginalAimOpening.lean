import Doom.Proofs.E1M1AimStop
import Doom.Proofs.E1M1NoiseOpeningFrame
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalAimOpening
open Verification X86 X86Memory X86Control BlockSummary
attribute [local irreducible] load32 store32
def code : List UInt8 := [0x89,0xc8,0xe8,0xba,0xb,0x0,0x0,0xa1,0x30,0xc0,0x2,0x0,0x3b,0x5,0x34,0xc0,0x2,0x0,0xf,0x8d,0x3b,0x1,0x0,0x0]
def bytesProgram (bytes : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2b77f≤pc ∧ pc<0x2b797 then X86Routine.decodeAt bytes (pc-0x2b77f) else none
def program := bytesProgram code
def listed : X86Routine.Program
  | 0x2b77f => some (.control (.block (.legacy (.mov 0 1))),2)
  | 0x2b781 => some (.call 0xbba,5)
  | 0x2b786 => some (.control (.block (.load 0 ⟨none,none,0,0x2c030⟩)),5)
  | 0x2b78b => some (.control (.cmpMemory 0 ⟨none,none,0,0x2c034⟩),6)
  | 0x2b791 => some (.jumpSigned 0 315,6)
  | _ => none

theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def argument (s : X86Memory.State) := put s 0 (s.regs 1)
def called (s : X86Memory.State) := X86Routine.pushWord (argument s) 0x2b786
def bottom (s : X86Memory.State) := load32 s.memory 0x2c030
def top (s : X86Memory.State) := load32 s.memory 0x2c034
def loaded (s : X86Memory.State) := put s 0 (bottom s)
def gate (s : X86Memory.State) : X86Control.State :=
  ⟨loaded s,some (compare32 (bottom s) (top s)),
    if (top s).toInt≤(bottom s).toInt then 0x2b8d2 else 0x2b797⟩

theorem call_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 2 ⟨s,f,0x2b77f⟩ (⟨called s,f,0x2c340⟩) := by
  have run : X86Routine.Prefix listed [] 2 ⟨s,f,0x2b77f⟩ (⟨called s,f,0x2c340⟩) := by
    apply X86Routine.Prefix.step (middle := ⟨argument s,f,0x2b781⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,X86Routine.pushWord,put,write,argument,called,bottom,top,loaded,gate,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge]
      all_goals split <;> simp_all)
    apply X86Routine.Prefix.step (middle := ⟨called s,f,0x2c340⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,X86Routine.pushWord,put,write,argument,called,bottom,top,loaded,gate,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge]
      all_goals split <;> simp_all)
    exact .nil _
  exact run.transfer program [] decoded (by simp)

theorem gate_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 3 ⟨s,f,0x2b786⟩ (gate s) := by
  have run : X86Routine.Prefix listed [] 3 ⟨s,f,0x2b786⟩ (gate s) := by
    apply X86Routine.Prefix.step (middle := ⟨loaded s,f,0x2b78b⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,X86Routine.pushWord,put,write,argument,called,bottom,top,loaded,gate,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge]
      all_goals split <;> simp_all)
    apply X86Routine.Prefix.step (middle := ⟨loaded s,some (compare32 (bottom s) (top s)),0x2b791⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,X86Routine.pushWord,put,write,argument,called,bottom,top,loaded,gate,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge]
      all_goals split <;> simp_all)
    apply X86Routine.Prefix.step (middle := gate s) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,X86Routine.pushWord,put,write,argument,called,bottom,top,loaded,gate,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge]
      all_goals split <;> simp_all)
    exact .nil _
  exact run.transfer program [] decoded (by simp)
end Doom.Proofs.OriginalAimOpening
