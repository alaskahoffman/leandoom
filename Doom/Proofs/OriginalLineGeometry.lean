import Doom.Proofs.E1M1LineLoad
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalLineGeometry
open Verification X86 X86Memory X86Control BlockSummary
def verticesBytes : List UInt8 := [0xf,0xbf,0x1,0x8d,0x14,0xc5,0x0,0x0,0x0,0x0,0xa1,0x38,0xc1,0x2,0x0,0x8d,0x34,0x10,0x89,0x33,0xf,0xbf,0x51,0x2,0x8d,0x14,0xd5,0x0,0x0,0x0,0x0,0x1,0xd0,0x89,0x43,0x4]
def deltaBytes : List UInt8 := [0x89,0xc7,0x8b,0x0,0x8b,0x16,0x29,0xd0,0x89,0x43,0x8,0x8b,0x47,0x4,0x8b,0x56,0x4,0x29,0xd0,0x89,0x43,0xc]
def horizontalBytes : List UInt8 := [0x8b,0x6,0x8b,0x17,0x39,0xd0,0x7d,0x7,0x89,0x43,0x22,0x8b,0x7,0xeb,0x5,0x89,0x53,0x22,0x8b,0x6,0x89,0x43,0x26]
def verticalBytes : List UInt8 := [0x8b,0x46,0x4,0x8b,0x57,0x4,0x39,0xd0,0x7d,0x8,0x89,0x43,0x1e,0x8b,0x47,0x4,0xeb,0x6,0x89,0x53,0x1e,0x8b,0x46,0x4,0x89,0x43,0x1a]
def bytesProgram (vertices delta horizontal vertical : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2e2b2≤pc ∧ pc<0x2e2d6 then X86Routine.decodeAt vertices (pc-0x2e2b2)
  else if 0x2e2d6≤pc ∧ pc<0x2e2ec then X86Routine.decodeAt delta (pc-0x2e2d6)
  else if 0x2e326≤pc ∧ pc<0x2e33d then X86Routine.decodeAt horizontal (pc-0x2e326)
  else if 0x2e33d≤pc ∧ pc<0x2e358 then X86Routine.decodeAt vertical (pc-0x2e33d)
  else none
def program := bytesProgram verticesBytes deltaBytes horizontalBytes verticalBytes
def listed : X86Routine.Program
  | 0x2e2b2 => some (.control (.block (.legacy (.movsx16 0 1 0))),3)
  | 0x2e2b5 => some (.control (.block (.lea 2 ⟨none,some 0,3,0⟩)),7)
  | 0x2e2bc => some (.control (.block (.load 0 ⟨none,none,0,0x2c138⟩)),5)
  | 0x2e2c1 => some (.control (.block (.lea 6 ⟨some 0,some 2,0,0⟩)),3)
  | 0x2e2c4 => some (.control (.block (.store ⟨some 3,none,0,0⟩ 6)),2)
  | 0x2e2c6 => some (.control (.block (.legacy (.movsx16 2 1 2))),4)
  | 0x2e2ca => some (.control (.block (.lea 2 ⟨none,some 2,3,0⟩)),7)
  | 0x2e2d1 => some (.control (.block (.arithmetic (.add 0 2))),2)
  | 0x2e2d3 => some (.control (.block (.store ⟨some 3,none,0,4⟩ 0)),3)
  | 0x2e2d6 => some (.control (.block (.legacy (.mov 7 0))),2)
  | 0x2e2d8 => some (.control (.block (.legacy (.load 0 0 0))),2)
  | 0x2e2da => some (.control (.block (.legacy (.load 2 6 0))),2)
  | 0x2e2dc => some (.control (.block (.arithmetic (.sub 0 2))),2)
  | 0x2e2de => some (.control (.block (.store ⟨some 3,none,0,8⟩ 0)),3)
  | 0x2e2e1 => some (.control (.block (.legacy (.load 0 7 4))),3)
  | 0x2e2e4 => some (.control (.block (.legacy (.load 2 6 4))),3)
  | 0x2e2e7 => some (.control (.block (.arithmetic (.sub 0 2))),2)
  | 0x2e2e9 => some (.control (.block (.store ⟨some 3,none,0,12⟩ 0)),3)
  | 0x2e326 => some (.control (.block (.legacy (.load 0 6 0))),2)
  | 0x2e328 => some (.control (.block (.legacy (.load 2 7 0))),2)
  | 0x2e32a => some (.compareRegisters 0 2,2)
  | 0x2e32c => some (.jumpSigned 0 7,2)
  | 0x2e32e => some (.control (.block (.store ⟨some 3,none,0,34⟩ 0)),3)
  | 0x2e331 => some (.control (.block (.legacy (.load 0 7 0))),2)
  | 0x2e333 => some (.jump 5,2)
  | 0x2e335 => some (.control (.block (.store ⟨some 3,none,0,34⟩ 2)),3)
  | 0x2e338 => some (.control (.block (.legacy (.load 0 6 0))),2)
  | 0x2e33a => some (.control (.block (.store ⟨some 3,none,0,38⟩ 0)),3)
  | 0x2e33d => some (.control (.block (.legacy (.load 0 6 4))),3)
  | 0x2e340 => some (.control (.block (.legacy (.load 2 7 4))),3)
  | 0x2e343 => some (.compareRegisters 0 2,2)
  | 0x2e345 => some (.jumpSigned 0 8,2)
  | 0x2e347 => some (.control (.block (.store ⟨some 3,none,0,30⟩ 0)),3)
  | 0x2e34a => some (.control (.block (.legacy (.load 0 7 4))),3)
  | 0x2e34d => some (.jump 6,2)
  | 0x2e34f => some (.control (.block (.store ⟨some 3,none,0,30⟩ 2)),3)
  | 0x2e352 => some (.control (.block (.legacy (.load 0 6 4))),3)
  | 0x2e355 => some (.control (.block (.store ⟨some 3,none,0,26⟩ 0)),3)
  | _ => none
theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def base (s : X86Memory.State) : Word := load32 s.memory 0x2c138
def v1 (s : X86Memory.State) : Word := base s + ((load16 s.memory (s.regs 1)).signExtend 32 <<< 3)
def firstMemory (s : X86Memory.State) : Memory := store32 s.memory (s.regs 3) (v1 s)
/-- The base is retained in EAX, but the second index observes the first store. -/
def offset2 (s : X86Memory.State) : Word := (load16 (firstMemory s) (s.regs 1+2)).signExtend 32 <<< 3
def v2 (s : X86Memory.State) : Word := base s+offset2 s
def vertices (s : X86Memory.State) : X86Control.State :=
  ⟨{put (put (put s 6 (v1 s)) 2 (offset2 s)) 0 (v2 s) with
    memory := store32 (firstMemory s) (s.regs 3+4) (v2 s)},none,0x2e2d6⟩
def dx (s : X86Memory.State) : Word := load32 s.memory (s.regs 0)-load32 s.memory (s.regs 6)
def xMemory (s : X86Memory.State) : Memory := store32 s.memory (s.regs 3+8) (dx s)
def dy (s : X86Memory.State) : Word := load32 (xMemory s) (s.regs 0+4)-load32 (xMemory s) (s.regs 6+4)
def delta (s : X86Memory.State) : X86Control.State :=
  ⟨{put (put (put s 7 (s.regs 0)) 2 (load32 (xMemory s) (s.regs 6+4))) 0 (dy s) with
    memory := store32 (xMemory s) (s.regs 3+12) (dy s)},none,0x2e2ec⟩

/-- Signed endpoint selection. The maximum coordinate is reloaded AFTER the
minimum store, faithfully retaining aliasing rather than assuming min/max. -/
def axis (s : X86Memory.State) (off low high : Word) (pc : Nat) : X86Control.State :=
  let a := load32 s.memory (s.regs 6+off)
  let b := load32 s.memory (s.regs 7+off)
  let ge := b.toInt≤a.toInt
  let m := store32 s.memory (s.regs 3+low) (if ge then b else a)
  let hi := load32 m ((if ge then s.regs 6 else s.regs 7)+off)
  ⟨{put (put s 2 b) 0 hi with memory := store32 m (s.regs 3+high) hi},some (compare32 a b),pc⟩
def horizontal (s : X86Memory.State) := axis s 0 34 38 0x2e33d
def bounds (s : X86Memory.State) := axis (horizontal s).core 4 30 26 0x2e358
@[local simp] private theorem step_2e2b2 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e2d6] (n+1) ⟨s,f,0x2e2b2⟩ =
      (X86Routine.execute (.control (.block (.legacy (.movsx16 0 1 0)))) ⟨s,f,0x2e2b5⟩).bind (X86Routine.run listed [0x2e2d6] n) := by rfl
@[local simp] private theorem step_2e2b5 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e2d6] (n+1) ⟨s,f,0x2e2b5⟩ =
      (X86Routine.execute (.control (.block (.lea 2 ⟨none,some 0,3,0⟩))) ⟨s,f,0x2e2bc⟩).bind (X86Routine.run listed [0x2e2d6] n) := by rfl
@[local simp] private theorem step_2e2bc (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e2d6] (n+1) ⟨s,f,0x2e2bc⟩ =
      (X86Routine.execute (.control (.block (.load 0 ⟨none,none,0,0x2c138⟩))) ⟨s,f,0x2e2c1⟩).bind (X86Routine.run listed [0x2e2d6] n) := by rfl
@[local simp] private theorem step_2e2c1 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e2d6] (n+1) ⟨s,f,0x2e2c1⟩ =
      (X86Routine.execute (.control (.block (.lea 6 ⟨some 0,some 2,0,0⟩))) ⟨s,f,0x2e2c4⟩).bind (X86Routine.run listed [0x2e2d6] n) := by rfl
@[local simp] private theorem step_2e2c4 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e2d6] (n+1) ⟨s,f,0x2e2c4⟩ =
      (X86Routine.execute (.control (.block (.store ⟨some 3,none,0,0⟩ 6))) ⟨s,f,0x2e2c6⟩).bind (X86Routine.run listed [0x2e2d6] n) := by rfl
@[local simp] private theorem step_2e2c6 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e2d6] (n+1) ⟨s,f,0x2e2c6⟩ =
      (X86Routine.execute (.control (.block (.legacy (.movsx16 2 1 2)))) ⟨s,f,0x2e2ca⟩).bind (X86Routine.run listed [0x2e2d6] n) := by rfl
@[local simp] private theorem step_2e2ca (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e2d6] (n+1) ⟨s,f,0x2e2ca⟩ =
      (X86Routine.execute (.control (.block (.lea 2 ⟨none,some 2,3,0⟩))) ⟨s,f,0x2e2d1⟩).bind (X86Routine.run listed [0x2e2d6] n) := by rfl
@[local simp] private theorem step_2e2d1 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e2d6] (n+1) ⟨s,f,0x2e2d1⟩ =
      (X86Routine.execute (.control (.block (.arithmetic (.add 0 2)))) ⟨s,f,0x2e2d3⟩).bind (X86Routine.run listed [0x2e2d6] n) := by rfl
@[local simp] private theorem step_2e2d3 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e2d6] (n+1) ⟨s,f,0x2e2d3⟩ =
      (X86Routine.execute (.control (.block (.store ⟨some 3,none,0,4⟩ 0))) ⟨s,f,0x2e2d6⟩).bind (X86Routine.run listed [0x2e2d6] n) := by rfl
@[local simp] private theorem stop_2e2d6 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e2d6] n ⟨s,f,0x2e2d6⟩=some ⟨s,f,0x2e2d6⟩ := by cases n <;> rfl
theorem vertices_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x2e2d6] 9 ⟨s,f,0x2e2b2⟩=some (vertices s) := by
  have run : X86Routine.run listed [0x2e2d6] 9 ⟨s,f,0x2e2b2⟩=some (vertices s) := by
    all_goals simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      X86Block.Address.eval,X86.execute,blockPreservesFlags,vertices,v1,v2,base,firstMemory,offset2,
      delta,dx,dy,xMemory,axis,put,write,BitVec.add_assoc,PlayerHeight.cmp_ge_prop,
      -BitVec.toInt_add]
    all_goals
      funext r
      by_cases h0 : r=0 <;> by_cases h2 : r=2 <;> by_cases h6 : r=6 <;> by_cases h7 : r=7 <;>
        simp [write,h0,h2,h6,h7]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]
@[local simp] private theorem step_2e2d6 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e2ec] (n+1) ⟨s,f,0x2e2d6⟩ =
      (X86Routine.execute (.control (.block (.legacy (.mov 7 0)))) ⟨s,f,0x2e2d8⟩).bind (X86Routine.run listed [0x2e2ec] n) := by rfl
@[local simp] private theorem step_2e2d8 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e2ec] (n+1) ⟨s,f,0x2e2d8⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 0 0 0)))) ⟨s,f,0x2e2da⟩).bind (X86Routine.run listed [0x2e2ec] n) := by rfl
@[local simp] private theorem step_2e2da (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e2ec] (n+1) ⟨s,f,0x2e2da⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 2 6 0)))) ⟨s,f,0x2e2dc⟩).bind (X86Routine.run listed [0x2e2ec] n) := by rfl
@[local simp] private theorem step_2e2dc (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e2ec] (n+1) ⟨s,f,0x2e2dc⟩ =
      (X86Routine.execute (.control (.block (.arithmetic (.sub 0 2)))) ⟨s,f,0x2e2de⟩).bind (X86Routine.run listed [0x2e2ec] n) := by rfl
@[local simp] private theorem step_2e2de (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e2ec] (n+1) ⟨s,f,0x2e2de⟩ =
      (X86Routine.execute (.control (.block (.store ⟨some 3,none,0,8⟩ 0))) ⟨s,f,0x2e2e1⟩).bind (X86Routine.run listed [0x2e2ec] n) := by rfl
@[local simp] private theorem step_2e2e1 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e2ec] (n+1) ⟨s,f,0x2e2e1⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 0 7 4)))) ⟨s,f,0x2e2e4⟩).bind (X86Routine.run listed [0x2e2ec] n) := by rfl
@[local simp] private theorem step_2e2e4 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e2ec] (n+1) ⟨s,f,0x2e2e4⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 2 6 4)))) ⟨s,f,0x2e2e7⟩).bind (X86Routine.run listed [0x2e2ec] n) := by rfl
@[local simp] private theorem step_2e2e7 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e2ec] (n+1) ⟨s,f,0x2e2e7⟩ =
      (X86Routine.execute (.control (.block (.arithmetic (.sub 0 2)))) ⟨s,f,0x2e2e9⟩).bind (X86Routine.run listed [0x2e2ec] n) := by rfl
@[local simp] private theorem step_2e2e9 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e2ec] (n+1) ⟨s,f,0x2e2e9⟩ =
      (X86Routine.execute (.control (.block (.store ⟨some 3,none,0,12⟩ 0))) ⟨s,f,0x2e2ec⟩).bind (X86Routine.run listed [0x2e2ec] n) := by rfl
@[local simp] private theorem stop_2e2ec (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e2ec] n ⟨s,f,0x2e2ec⟩=some ⟨s,f,0x2e2ec⟩ := by cases n <;> rfl
theorem delta_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x2e2ec] 9 ⟨s,f,0x2e2d6⟩=some (delta s) := by
  have run : X86Routine.run listed [0x2e2ec] 9 ⟨s,f,0x2e2d6⟩=some (delta s) := by
    all_goals simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      X86Block.Address.eval,X86.execute,blockPreservesFlags,vertices,v1,v2,base,firstMemory,offset2,
      delta,dx,dy,xMemory,axis,put,write,BitVec.add_assoc,PlayerHeight.cmp_ge_prop,
      -BitVec.toInt_add]
    all_goals
      funext r
      by_cases h0 : r=0 <;> by_cases h2 : r=2 <;> by_cases h6 : r=6 <;> by_cases h7 : r=7 <;>
        simp [write,h0,h2,h6,h7]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]
@[local simp] private theorem step_2e326 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e33d] (n+1) ⟨s,f,0x2e326⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 0 6 0)))) ⟨s,f,0x2e328⟩).bind (X86Routine.run listed [0x2e33d] n) := by rfl
@[local simp] private theorem step_2e328 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e33d] (n+1) ⟨s,f,0x2e328⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 2 7 0)))) ⟨s,f,0x2e32a⟩).bind (X86Routine.run listed [0x2e33d] n) := by rfl
@[local simp] private theorem step_2e32a (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e33d] (n+1) ⟨s,f,0x2e32a⟩ =
      (X86Routine.execute (.compareRegisters 0 2) ⟨s,f,0x2e32c⟩).bind (X86Routine.run listed [0x2e33d] n) := by rfl
@[local simp] private theorem step_2e32c (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e33d] (n+1) ⟨s,f,0x2e32c⟩ =
      (X86Routine.execute (.jumpSigned 0 7) ⟨s,f,0x2e32e⟩).bind (X86Routine.run listed [0x2e33d] n) := by rfl
@[local simp] private theorem step_2e32e (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e33d] (n+1) ⟨s,f,0x2e32e⟩ =
      (X86Routine.execute (.control (.block (.store ⟨some 3,none,0,34⟩ 0))) ⟨s,f,0x2e331⟩).bind (X86Routine.run listed [0x2e33d] n) := by rfl
@[local simp] private theorem step_2e331 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e33d] (n+1) ⟨s,f,0x2e331⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 0 7 0)))) ⟨s,f,0x2e333⟩).bind (X86Routine.run listed [0x2e33d] n) := by rfl
@[local simp] private theorem step_2e333 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e33d] (n+1) ⟨s,f,0x2e333⟩ =
      (X86Routine.execute (.jump 5) ⟨s,f,0x2e335⟩).bind (X86Routine.run listed [0x2e33d] n) := by rfl
@[local simp] private theorem step_2e335 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e33d] (n+1) ⟨s,f,0x2e335⟩ =
      (X86Routine.execute (.control (.block (.store ⟨some 3,none,0,34⟩ 2))) ⟨s,f,0x2e338⟩).bind (X86Routine.run listed [0x2e33d] n) := by rfl
@[local simp] private theorem step_2e338 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e33d] (n+1) ⟨s,f,0x2e338⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 0 6 0)))) ⟨s,f,0x2e33a⟩).bind (X86Routine.run listed [0x2e33d] n) := by rfl
@[local simp] private theorem step_2e33a (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e33d] (n+1) ⟨s,f,0x2e33a⟩ =
      (X86Routine.execute (.control (.block (.store ⟨some 3,none,0,38⟩ 0))) ⟨s,f,0x2e33d⟩).bind (X86Routine.run listed [0x2e33d] n) := by rfl
@[local simp] private theorem stop_2e33d (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e33d] n ⟨s,f,0x2e33d⟩=some ⟨s,f,0x2e33d⟩ := by cases n <;> rfl
theorem horizontal_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x2e33d] 8 ⟨s,f,0x2e326⟩=some (axis s 0 34 38 0x2e33d) := by
  have run : X86Routine.run listed [0x2e33d] 8 ⟨s,f,0x2e326⟩=some (axis s 0 34 38 0x2e33d) := by
    by_cases ge : (load32 s.memory (s.regs 7+(0#32))).toInt≤(load32 s.memory (s.regs 6+(0#32))).toInt
    all_goals try simp only [BitVec.add_zero] at ge
    all_goals simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      X86Block.Address.eval,X86.execute,blockPreservesFlags,vertices,v1,v2,base,firstMemory,offset2,
      delta,dx,dy,xMemory,axis,put,write,BitVec.add_assoc,PlayerHeight.cmp_ge_prop,
      ge,
      -BitVec.toInt_add]
    all_goals
      funext r
      by_cases h0 : r=0 <;> by_cases h2 : r=2 <;> by_cases h6 : r=6 <;> by_cases h7 : r=7 <;>
        simp [write,h0,h2,h6,h7]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]
@[local simp] private theorem step_2e33d (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e358] (n+1) ⟨s,f,0x2e33d⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 0 6 4)))) ⟨s,f,0x2e340⟩).bind (X86Routine.run listed [0x2e358] n) := by rfl
@[local simp] private theorem step_2e340 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e358] (n+1) ⟨s,f,0x2e340⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 2 7 4)))) ⟨s,f,0x2e343⟩).bind (X86Routine.run listed [0x2e358] n) := by rfl
@[local simp] private theorem step_2e343 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e358] (n+1) ⟨s,f,0x2e343⟩ =
      (X86Routine.execute (.compareRegisters 0 2) ⟨s,f,0x2e345⟩).bind (X86Routine.run listed [0x2e358] n) := by rfl
@[local simp] private theorem step_2e345 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e358] (n+1) ⟨s,f,0x2e345⟩ =
      (X86Routine.execute (.jumpSigned 0 8) ⟨s,f,0x2e347⟩).bind (X86Routine.run listed [0x2e358] n) := by rfl
@[local simp] private theorem step_2e347 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e358] (n+1) ⟨s,f,0x2e347⟩ =
      (X86Routine.execute (.control (.block (.store ⟨some 3,none,0,30⟩ 0))) ⟨s,f,0x2e34a⟩).bind (X86Routine.run listed [0x2e358] n) := by rfl
@[local simp] private theorem step_2e34a (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e358] (n+1) ⟨s,f,0x2e34a⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 0 7 4)))) ⟨s,f,0x2e34d⟩).bind (X86Routine.run listed [0x2e358] n) := by rfl
@[local simp] private theorem step_2e34d (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e358] (n+1) ⟨s,f,0x2e34d⟩ =
      (X86Routine.execute (.jump 6) ⟨s,f,0x2e34f⟩).bind (X86Routine.run listed [0x2e358] n) := by rfl
@[local simp] private theorem step_2e34f (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e358] (n+1) ⟨s,f,0x2e34f⟩ =
      (X86Routine.execute (.control (.block (.store ⟨some 3,none,0,30⟩ 2))) ⟨s,f,0x2e352⟩).bind (X86Routine.run listed [0x2e358] n) := by rfl
@[local simp] private theorem step_2e352 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e358] (n+1) ⟨s,f,0x2e352⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 0 6 4)))) ⟨s,f,0x2e355⟩).bind (X86Routine.run listed [0x2e358] n) := by rfl
@[local simp] private theorem step_2e355 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e358] (n+1) ⟨s,f,0x2e355⟩ =
      (X86Routine.execute (.control (.block (.store ⟨some 3,none,0,26⟩ 0))) ⟨s,f,0x2e358⟩).bind (X86Routine.run listed [0x2e358] n) := by rfl
@[local simp] private theorem stop_2e358 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e358] n ⟨s,f,0x2e358⟩=some ⟨s,f,0x2e358⟩ := by cases n <;> rfl
theorem vertical_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x2e358] 8 ⟨s,f,0x2e33d⟩=some (axis s 4 30 26 0x2e358) := by
  have run : X86Routine.run listed [0x2e358] 8 ⟨s,f,0x2e33d⟩=some (axis s 4 30 26 0x2e358) := by
    by_cases ge : (load32 s.memory (s.regs 7+(4#32))).toInt≤(load32 s.memory (s.regs 6+(4#32))).toInt
    all_goals try simp only [BitVec.add_zero] at ge
    all_goals simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      X86Block.Address.eval,X86.execute,blockPreservesFlags,vertices,v1,v2,base,firstMemory,offset2,
      delta,dx,dy,xMemory,axis,put,write,BitVec.add_assoc,PlayerHeight.cmp_ge_prop,
      ge,
      -BitVec.toInt_add]
    all_goals
      funext r
      by_cases h0 : r=0 <;> by_cases h2 : r=2 <;> by_cases h6 : r=6 <;> by_cases h7 : r=7 <;>
        simp [write,h0,h2,h6,h7]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

def prepared (s : X86Memory.State) := delta (vertices s).core

theorem prefix_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x2e2ec] 18 ⟨s,f,0x2e2b2⟩=some (prepared s) := by
  obtain ⟨n,hn,p,_⟩ := X86Routine.run_path (vertices_execution s f)
  have p := p.transfer program [0x2e2ec] (fun _ _ => rfl) (by
    intro pc h member
    simp only [List.mem_singleton] at member
    subst pc; exact h (by decide))
  exact p.finish (delta_execution (vertices s).core (vertices s).flags) 18 (by omega)

theorem bounds_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x2e358] 16 ⟨s,f,0x2e326⟩=some (bounds s) := by
  obtain ⟨n,hn,p,_⟩ := X86Routine.run_path (horizontal_execution s f)
  have p := p.transfer program [0x2e358] (fun _ _ => rfl) (by
    intro pc h member
    simp only [List.mem_singleton] at member
    subst pc; exact h (by decide))
  exact p.finish (vertical_execution (horizontal s).core (horizontal s).flags) 16 (by omega)

theorem vertices_readback (s : X86Memory.State) :
    load32 (vertices s).core.memory (s.regs 3)=v1 s ∧
    load32 (vertices s).core.memory (s.regs 3+4)=v2 s := by
  have apart : Apart (s.regs 3) (s.regs 3+4) := by
    have h := PlayerHeight.slots_apart (s.regs 3) 0 1 (by decide)
    simpa using h
  change load32 (store32 (firstMemory s) (s.regs 3+4) (v2 s)) _=_ ∧ _
  rw [load_store_apart _ _ _ _ apart]
  exact ⟨load_store _ _ _,load_store _ _ _⟩

theorem delta_readback (s : X86Memory.State) :
    load32 (delta s).core.memory (s.regs 3+8)=dx s ∧
    load32 (delta s).core.memory (s.regs 3+12)=dy s := by
  have apart : Apart (s.regs 3+8) (s.regs 3+12) := by
    have h := PlayerHeight.slots_apart (s.regs 3) 2 3 (by decide)
    exact h
  change load32 (store32 (xMemory s) (s.regs 3+12) (dy s)) _=_ ∧ _
  rw [load_store_apart _ _ _ _ apart]
  exact ⟨load_store _ _ _,load_store _ _ _⟩

/-- No unsigned reinterpretation of a malformed negative vertex index. -/
theorem vertex_addresses (s : X86Memory.State) (i j : BitVec 16) (b : Word)
    (a : load16 s.memory (s.regs 1)=i) (c : load16 s.memory (s.regs 1+2)=j)
    (g : base s=b) (safe : Apart (s.regs 1+2) (s.regs 3)) :
    v1 s=b+(i.signExtend 32 <<< 3) ∧ v2 s=b+(j.signExtend 32 <<< 3) := by
  have read := congrArg (fun w : Word => w.extractLsb' 0 16)
    (load_store_apart s.memory (s.regs 3) (s.regs 1+2) (v1 s) safe)
  have read : load16 (firstMemory s) (s.regs 1+2)=load16 s.memory (s.regs 1+2) := by
    simpa only [load32,BitVec.extractLsb'_append_eq_right,load16,firstMemory] using read
  simp only [v1,v2,offset2,a,g,read,c,and_self]

@[simp] theorem axis_reg (s : X86Memory.State) (off low high : Word) (pc : Nat) (r : Reg)
    (h0 : r≠0) (h2 : r≠2) : (axis s off low high pc).core.regs r=s.regs r := by
  simp [axis,put,write,h0,h2]

theorem axis_frame (s : X86Memory.State) (off low high a : Word) (pc : Nat)
    (lo : Apart a (s.regs 3+low)) (hi : Apart a (s.regs 3+high)) :
    load32 (axis s off low high pc).core.memory a=load32 s.memory a := by
  change load32 (store32 (store32 s.memory _ _) _ _) a=_
  rw [load_store_apart _ _ _ _ hi,load_store_apart _ _ _ _ lo]

/-- When the minimum store is separate from the endpoint reads, the emitted
pair is precisely the signed minimum and maximum of the incoming coordinates. -/
theorem axis_minmax (s : X86Memory.State) (off low high : Word) (pc : Nat)
    (a : Apart (s.regs 6+off) (s.regs 3+low))
    (b : Apart (s.regs 7+off) (s.regs 3+low))
    (dest : Apart (s.regs 3+low) (s.regs 3+high)) :
    let x := load32 s.memory (s.regs 6+off)
    let y := load32 s.memory (s.regs 7+off)
    load32 (axis s off low high pc).core.memory (s.regs 3+low)=(if y.toInt≤x.toInt then y else x) ∧
    load32 (axis s off low high pc).core.memory (s.regs 3+high)=(if y.toInt≤x.toInt then x else y) := by
  dsimp only
  by_cases ge : (load32 s.memory (s.regs 7+off)).toInt≤(load32 s.memory (s.regs 6+off)).toInt
  all_goals simp only [axis,ge,if_true,if_false]
  all_goals rw [load_store_apart _ _ _ _ dest,load_store,load_store]
  · exact ⟨rfl,load_store_apart _ _ _ _ a⟩
  · exact ⟨rfl,load_store_apart _ _ _ _ b⟩

theorem bounds_frame (s : X86Memory.State) (a : Word)
    (safe : ∀ off∈[(34#32),38,30,26], Apart a (s.regs 3+off)) :
    load32 (bounds s).core.memory a=load32 s.memory a := by
  have line : (horizontal s).core.regs 3=s.regs 3 := axis_reg _ _ _ _ _ _ (by decide) (by decide)
  unfold bounds
  rw [axis_frame _ _ _ _ _ _ (by rw [line]; exact safe 30 (by simp))
    (by rw [line]; exact safe 26 (by simp))]
  exact axis_frame s 0 34 38 a 0x2e33d (safe 34 (by simp)) (safe 38 (by simp))

theorem delta_frame (s : X86Memory.State) (a : Word)
    (x : Apart a (s.regs 3+8)) (y : Apart a (s.regs 3+12)) :
    load32 (delta s).core.memory a=load32 s.memory a := by
  change load32 (store32 (xMemory s) (s.regs 3+12) (dy s)) a=_
  rw [load_store_apart _ _ _ _ y]
  exact load_store_apart _ _ _ _ x

/-- Both vertex pointers and both deltas survive the entire 18-instruction
prefix, without assuming that the raw record and runtime line are disjoint. -/
theorem prepared_fields (s : X86Memory.State) :
    load32 (prepared s).core.memory (s.regs 3)=v1 s ∧
    load32 (prepared s).core.memory (s.regs 3+4)=v2 s ∧
    load32 (prepared s).core.memory (s.regs 3+8)=dx (vertices s).core ∧
    load32 (prepared s).core.memory (s.regs 3+12)=dy (vertices s).core := by
  have reg3 : (vertices s).core.regs 3=s.regs 3 := by simp [vertices,put,write]
  have a02 : Apart (s.regs 3) (s.regs 3+8) := by
    simpa using PlayerHeight.slots_apart (s.regs 3) 0 2 (by decide)
  have a03 : Apart (s.regs 3) (s.regs 3+12) := by
    have h := PlayerHeight.slots_apart (s.regs 3) 0 3 (by decide)
    change Apart (s.regs 3+(0#32)) (s.regs 3+(12#32)) at h
    simpa using h
  have a12 : Apart (s.regs 3+4) (s.regs 3+8) := PlayerHeight.slots_apart (s.regs 3) 1 2 (by decide)
  have a13 : Apart (s.regs 3+4) (s.regs 3+12) := PlayerHeight.slots_apart (s.regs 3) 1 3 (by decide)
  have first := delta_frame (vertices s).core (s.regs 3) (by rwa [reg3]) (by rwa [reg3])
  have second := delta_frame (vertices s).core (s.regs 3+4) (by rwa [reg3]) (by rwa [reg3])
  refine ⟨first.trans (vertices_readback s).1,second.trans (vertices_readback s).2,?_⟩
  simpa only [prepared,reg3] using delta_readback (vertices s).core

end Doom.Proofs.OriginalLineGeometry
