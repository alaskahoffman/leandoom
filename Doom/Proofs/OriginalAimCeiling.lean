import Doom.Proofs.E1M1AimFloorEntry
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalAimCeiling
open Verification X86 X86Memory X86Control BlockSummary
attribute [local irreducible] load32 store32
def code : List UInt8 := [0x8b,0x41,0x2e,0x8b,0x51,0x32,0x8b,0x40,0x4,0x3b,0x42,0x4,0x74,0x21,0xa1,0x34,0xc0,0x2,0x0,0x8b,0x35,0xa8,0xb9,0x2,0x0,0x89,0xda,0x29,0xf0,0xe8,0x8d,0x19,0xff,0xff,0x3b,0x5,0xe8,0xc1,0x2,0x0,0x7d,0x5,0xa3,0xe8,0xc1,0x2,0x0]
def bytesProgram (bytes : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2b7d1≤pc ∧ pc<0x2b800 then X86Routine.decodeAt bytes (pc-0x2b7d1) else none
def program := bytesProgram code
def listed : X86Routine.Program
  | 0x2b7d1 => some (.control (.block (.legacy (.load 0 1 46))),3)
  | 0x2b7d4 => some (.control (.block (.legacy (.load 2 1 50))),3)
  | 0x2b7d7 => some (.control (.block (.legacy (.load 0 0 4))),3)
  | 0x2b7da => some (.control (.cmpMemory 0 ⟨some 2,none,0,4⟩),3)
  | 0x2b7dd => some (.control (.jumpZero true 33),2)
  | 0x2b7df => some (.control (.block (.load 0 ⟨none,none,0,0x2c034⟩)),5)
  | 0x2b7e4 => some (.control (.block (.load 6 ⟨none,none,0,0x2b9a8⟩)),6)
  | 0x2b7ea => some (.control (.block (.legacy (.mov 2 3))),2)
  | 0x2b7ec => some (.control (.block (.arithmetic (.sub 0 6))),2)
  | 0x2b7ee => some (.call (-58995),5)
  | 0x2b7f3 => some (.control (.cmpMemory 0 ⟨none,none,0,0x2c1e8⟩),6)
  | 0x2b7f9 => some (.jumpSigned 0 5,2)
  | 0x2b7fb => some (.control (.storeEax 0x2c1e8),5)
  | _ => none

theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def front (s : X86Memory.State) := load32 s.memory (s.regs 1+(46#32))
def back (s : X86Memory.State) := load32 s.memory (s.regs 1+(50#32))
def fc (s : X86Memory.State) := load32 s.memory (front s+(4#32))
def bc (s : X86Memory.State) := load32 s.memory (back s+(4#32))
def c1 (s : X86Memory.State) := put s 0 (front s)
def c2 (s : X86Memory.State) := put (c1 s) 2 (back s)
def c3 (s : X86Memory.State) := put (c2 s) 0 (fc s)
def gate (s : X86Memory.State) : X86Control.State :=
  ⟨c3 s,some (compare32 (fc s) (bc s)),if fc s=bc s then 0x2b800 else 0x2b7df⟩
def high (s : X86Memory.State) := load32 s.memory (0x2c034#32)
def shootZ (s : X86Memory.State) := load32 s.memory (0x2b9a8#32)
def numerator (s : X86Memory.State) := high s-shootZ s
def loaded (s : X86Memory.State) := put s 0 (high s)
def eye (s : X86Memory.State) := put (loaded s) 6 (shootZ s)
def distance (s : X86Memory.State) := put (eye s) 2 (s.regs 3)
def argument (s : X86Memory.State) := put (distance s) 0 (numerator s)
def called (s : X86Memory.State) := X86Routine.pushWord (argument s) 0x2b7f3
def old (s : X86Memory.State) := load32 s.memory (0x2c1e8#32)
def lowered (s : X86Memory.State) := {s with memory:=store32 s.memory (0x2c1e8#32) (s.regs 0)}
def clipped (s : X86Memory.State) : X86Control.State :=
  ⟨if (old s).toInt≤(s.regs 0).toInt then s else lowered s,
    some (compare32 (s.regs 0) (old s)),0x2b800⟩

theorem gate_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 5 ⟨s,f,0x2b7d1⟩ (gate s) := by
  have run : X86Routine.Prefix listed [] 5 ⟨s,f,0x2b7d1⟩ (gate s) := by
    apply X86Routine.Prefix.step (middle := ⟨c1 s,f,0x2b7d4⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,front,back,fc,bc,c1,c2,c3,gate,high,shootZ,numerator,loaded,eye,distance,argument,called,X86Routine.pushWord,old,lowered,clipped,cmp32_zero,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge]
      all_goals split <;> simp_all)
    apply X86Routine.Prefix.step (middle := ⟨c2 s,f,0x2b7d7⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,front,back,fc,bc,c1,c2,c3,gate,high,shootZ,numerator,loaded,eye,distance,argument,called,X86Routine.pushWord,old,lowered,clipped,cmp32_zero,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge]
      all_goals split <;> simp_all)
    apply X86Routine.Prefix.step (middle := ⟨c3 s,f,0x2b7da⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,front,back,fc,bc,c1,c2,c3,gate,high,shootZ,numerator,loaded,eye,distance,argument,called,X86Routine.pushWord,old,lowered,clipped,cmp32_zero,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge]
      all_goals split <;> simp_all)
    apply X86Routine.Prefix.step (middle := ⟨c3 s,some (compare32 (fc s) (bc s)),0x2b7dd⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,front,back,fc,bc,c1,c2,c3,gate,high,shootZ,numerator,loaded,eye,distance,argument,called,X86Routine.pushWord,old,lowered,clipped,cmp32_zero,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge]
      all_goals split <;> simp_all)
    apply X86Routine.Prefix.step (middle := gate s) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,front,back,fc,bc,c1,c2,c3,gate,high,shootZ,numerator,loaded,eye,distance,argument,called,X86Routine.pushWord,old,lowered,clipped,cmp32_zero,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge]
      all_goals split <;> simp_all)
    exact .nil _
  exact run.transfer program [] decoded (by simp)

theorem call_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 5 ⟨s,f,0x2b7df⟩ (⟨called s,none,0x1d180⟩) := by
  have run : X86Routine.Prefix listed [] 5 ⟨s,f,0x2b7df⟩ (⟨called s,none,0x1d180⟩) := by
    apply X86Routine.Prefix.step (middle := ⟨loaded s,f,0x2b7e4⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,front,back,fc,bc,c1,c2,c3,gate,high,shootZ,numerator,loaded,eye,distance,argument,called,X86Routine.pushWord,old,lowered,clipped,cmp32_zero,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge]
      all_goals split <;> simp_all)
    apply X86Routine.Prefix.step (middle := ⟨eye s,f,0x2b7ea⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,front,back,fc,bc,c1,c2,c3,gate,high,shootZ,numerator,loaded,eye,distance,argument,called,X86Routine.pushWord,old,lowered,clipped,cmp32_zero,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge]
      all_goals split <;> simp_all)
    apply X86Routine.Prefix.step (middle := ⟨distance s,f,0x2b7ec⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,front,back,fc,bc,c1,c2,c3,gate,high,shootZ,numerator,loaded,eye,distance,argument,called,X86Routine.pushWord,old,lowered,clipped,cmp32_zero,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge]
      all_goals split <;> simp_all)
    apply X86Routine.Prefix.step (middle := ⟨argument s,none,0x2b7ee⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,front,back,fc,bc,c1,c2,c3,gate,high,shootZ,numerator,loaded,eye,distance,argument,called,X86Routine.pushWord,old,lowered,clipped,cmp32_zero,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge]
      all_goals split <;> simp_all)
    apply X86Routine.Prefix.step (middle := ⟨called s,none,0x1d180⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,front,back,fc,bc,c1,c2,c3,gate,high,shootZ,numerator,loaded,eye,distance,argument,called,X86Routine.pushWord,old,lowered,clipped,cmp32_zero,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge]
      all_goals split <;> simp_all)
    exact .nil _
  exact run.transfer program [] decoded (by simp)

theorem clip_execution (s : X86Memory.State) (f : Option Flags) :
    ∃ n, n≤3 ∧ X86Routine.Prefix program [] n ⟨s,f,0x2b7f3⟩ (clipped s) := by
  by_cases le : (old s).toInt≤(s.regs 0).toInt
  · simp only [old] at le
    have run : X86Routine.Prefix listed [] 2 ⟨s,f,0x2b7f3⟩ (clipped s) := by
      apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (s.regs 0) (old s)),0x2b7f9⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,front,back,fc,bc,c1,c2,c3,gate,high,shootZ,numerator,loaded,eye,distance,argument,called,X86Routine.pushWord,old,lowered,clipped,cmp32_zero,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge,le])
      apply X86Routine.Prefix.step (middle := clipped s) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,front,back,fc,bc,c1,c2,c3,gate,high,shootZ,numerator,loaded,eye,distance,argument,called,X86Routine.pushWord,old,lowered,clipped,cmp32_zero,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge,le])
      exact .nil _
    exact ⟨2,by omega,run.transfer program [] decoded (by simp)⟩
  · simp only [old] at le
    have run : X86Routine.Prefix listed [] 3 ⟨s,f,0x2b7f3⟩ (clipped s) := by
      apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (s.regs 0) (old s)),0x2b7f9⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,front,back,fc,bc,c1,c2,c3,gate,high,shootZ,numerator,loaded,eye,distance,argument,called,X86Routine.pushWord,old,lowered,clipped,cmp32_zero,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge,le])
      apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (s.regs 0) (old s)),0x2b7fb⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,front,back,fc,bc,c1,c2,c3,gate,high,shootZ,numerator,loaded,eye,distance,argument,called,X86Routine.pushWord,old,lowered,clipped,cmp32_zero,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge,le])
      apply X86Routine.Prefix.step (middle := clipped s) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,front,back,fc,bc,c1,c2,c3,gate,high,shootZ,numerator,loaded,eye,distance,argument,called,X86Routine.pushWord,old,lowered,clipped,cmp32_zero,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge,le])
      exact .nil _
    exact ⟨3,by omega,run.transfer program [] decoded (by simp)⟩
end Doom.Proofs.OriginalAimCeiling
