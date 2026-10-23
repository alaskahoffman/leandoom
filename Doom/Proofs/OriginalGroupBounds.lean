import Doom.Proofs.OriginalPlayerHeight
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalGroupBounds
open Verification X86 X86Memory X86Control BlockSummary
def boxBytes : List UInt8 := [0x3b,0x50,0x8,0x7d,0x5,0x89,0x50,0x8,0xeb,0x8,0x3b,0x50,0xc,0x7e,0x3,0x89,0x50,0xc,0x3b,0x58,0x4,0x7d,0x4,0x89,0x58,0x4,0xc3,0x3b,0x18,0x7e,0x2,0x89,0x18,0xc3]
def firstBytes : List UInt8 := [0x8b,0x11,0x89,0xe0,0x8b,0x5a,0x4,0x8b,0x12,0xe8,0x50,0x5b,0xff,0xff]
def secondBytes : List UInt8 := [0x8b,0x41,0x4,0x8b,0x58,0x4,0x8b,0x10,0x89,0xe0,0x83,0xc6,0x4,0xe8,0x3e,0x5b,0xff,0xff]
def advanceBytes : List UInt8 := [0xa1,0x34,0xc1,0x2,0x0,0x47,0x83,0xc1,0x3e,0x39,0xc7,0x7c,0xc7]
def bytesProgram (box first second advance : List UInt8) : X86Routine.Program := fun pc =>
  if 0x241e0≤pc ∧ pc<0x24202 then X86Routine.decodeAt box (pc-0x241e0)
  else if 0x2e682≤pc ∧ pc<0x2e690 then X86Routine.decodeAt first (pc-0x2e682)
  else if 0x2e690≤pc ∧ pc<0x2e6a2 then X86Routine.decodeAt second (pc-0x2e690)
  else if 0x2e6a2≤pc ∧ pc<0x2e6af then X86Routine.decodeAt advance (pc-0x2e6a2)
  else none
def program := bytesProgram boxBytes firstBytes secondBytes advanceBytes
def listed : X86Routine.Program
  | 0x241e0 => some (.control (.cmpMemory 2 ⟨some 0,none,0,8⟩),3)
  | 0x241e3 => some (.jumpSigned 0 5,2)
  | 0x241e5 => some (.control (.block (.store ⟨some 0,none,0,8⟩ 2)),3)
  | 0x241e8 => some (.jump 8,2)
  | 0x241ea => some (.control (.cmpMemory 2 ⟨some 0,none,0,12⟩),3)
  | 0x241ed => some (.jumpSigned 1 3,2)
  | 0x241ef => some (.control (.block (.store ⟨some 0,none,0,12⟩ 2)),3)
  | 0x241f2 => some (.control (.cmpMemory 3 ⟨some 0,none,0,4⟩),3)
  | 0x241f5 => some (.jumpSigned 0 4,2)
  | 0x241f7 => some (.control (.block (.store ⟨some 0,none,0,4⟩ 3)),3)
  | 0x241fa => some (.ret,1)
  | 0x241fb => some (.control (.cmpMemory 3 ⟨some 0,none,0,0⟩),2)
  | 0x241fd => some (.jumpSigned 1 2,2)
  | 0x241ff => some (.control (.block (.store ⟨some 0,none,0,0⟩ 3)),2)
  | 0x24201 => some (.ret,1)
  | 0x2e682 => some (.control (.block (.legacy (.load 2 1 0))),2)
  | 0x2e684 => some (.control (.block (.legacy (.mov 0 4))),2)
  | 0x2e686 => some (.control (.block (.legacy (.load 3 2 4))),3)
  | 0x2e689 => some (.control (.block (.legacy (.load 2 2 0))),2)
  | 0x2e68b => some (.call (-42160),5)
  | 0x2e690 => some (.control (.block (.legacy (.load 0 1 4))),3)
  | 0x2e693 => some (.control (.block (.legacy (.load 3 0 4))),3)
  | 0x2e696 => some (.control (.block (.legacy (.load 2 0 0))),2)
  | 0x2e698 => some (.control (.block (.legacy (.mov 0 4))),2)
  | 0x2e69a => some (.addImmediate 6 4,3)
  | 0x2e69d => some (.call (-42178),5)
  | 0x2e6a2 => some (.control (.block (.load 0 ⟨none,none,0,0x2c134⟩)),5)
  | 0x2e6a7 => some (.addImmediate 7 1,1)
  | 0x2e6a8 => some (.addImmediate 1 62,3)
  | 0x2e6ab => some (.compareRegisters 7 0,2)
  | 0x2e6ad => some (.jumpSigned 3 (-57),2)
  | _ => none
theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def horizontal (s : X86Memory.State) : X86Control.State :=
  let lo := load32 s.memory (s.regs 0+8)
  let hi := load32 s.memory (s.regs 0+12)
  if lo.toInt≤(s.regs 2).toInt then
    ⟨{s with memory := if (s.regs 2).toInt≤hi.toInt then s.memory else store32 s.memory (s.regs 0+12) (s.regs 2)},
      some (compare32 (s.regs 2) hi),0x241f2⟩
  else ⟨{s with memory := store32 s.memory (s.regs 0+8) (s.regs 2)},some (compare32 (s.regs 2) lo),0x241f2⟩
def vertical (s : X86Memory.State) : X86Control.State :=
  let lo := load32 s.memory (s.regs 0+4)
  let hi := load32 s.memory (s.regs 0)
  if lo.toInt≤(s.regs 3).toInt then
    ⟨{s with memory := if (s.regs 3).toInt≤hi.toInt then s.memory else store32 s.memory (s.regs 0) (s.regs 3)},
      some (compare32 (s.regs 3) hi),0x24201⟩
  else ⟨{s with memory := store32 s.memory (s.regs 0+4) (s.regs 3)},some (compare32 (s.regs 3) lo),0x241fa⟩
def returned (s : X86Control.State) : X86Control.State :=
  ⟨put s.core 4 (s.core.regs 4+4),s.flags,(load32 s.core.memory (s.core.regs 4)).toNat⟩
def boxResult (s : X86Memory.State) := returned (vertical (horizontal s).core)
def firstInput (s : X86Memory.State) : X86Memory.State :=
  let t := put s 2 (load32 s.memory (s.regs 1))
  let t := put t 0 (t.regs 4)
  let t := put t 3 (load32 t.memory (t.regs 2+4))
  put t 2 (load32 t.memory (t.regs 2))
def firstCall (s : X86Memory.State) (f : Option Flags) : X86Control.State :=
  ⟨X86Routine.pushWord (firstInput s) 0x2e690,f,0x241e0⟩
def secondInput (s : X86Memory.State) : X86Memory.State :=
  let t := put s 0 (load32 s.memory (s.regs 1+4))
  let t := put t 3 (load32 t.memory (t.regs 0+4))
  let t := put t 2 (load32 t.memory (t.regs 0))
  let t := put t 0 (t.regs 4)
  put t 6 (t.regs 6+4)
def secondCall (s : X86Memory.State) : X86Control.State :=
  ⟨X86Routine.pushWord (secondInput s) 0x2e6a2,none,0x241e0⟩
def advanced (s : X86Memory.State) : X86Control.State :=
  let t := put s 0 (load32 s.memory 0x2c134)
  let t := put t 7 (s.regs 7+1)
  let t := put t 1 (s.regs 1+62)
  ⟨t,some (compare32 (t.regs 7) (t.regs 0)),if (t.regs 7).toInt<(t.regs 0).toInt then 0x2e676 else 0x2e6af⟩
private theorem run_step {p es op len} (s : X86Control.State) (n : Nat)
    (active : s.pc ∉ es) (dec : p s.pc=some (op,len)) :
    X86Routine.run p es (n+1) s =
      (X86Routine.execute op {s with pc:=s.pc+len}).bind (X86Routine.run p es n) := by
  rw [X86Routine.run,if_neg active,dec]
  rfl
@[local simp] private theorem step_241e0 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x241f2] (n+1) ⟨s,f,0x241e0⟩ =
      (X86Routine.execute (.control (.cmpMemory 2 ⟨some 0,none,0,8⟩)) ⟨s,f,0x241e3⟩).bind (X86Routine.run listed [0x241f2] n) := by rfl
@[local simp] private theorem step_241e3 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x241f2] (n+1) ⟨s,f,0x241e3⟩ =
      (X86Routine.execute (.jumpSigned 0 5) ⟨s,f,0x241e5⟩).bind (X86Routine.run listed [0x241f2] n) := by rfl
@[local simp] private theorem step_241e5 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x241f2] (n+1) ⟨s,f,0x241e5⟩ =
      (X86Routine.execute (.control (.block (.store ⟨some 0,none,0,8⟩ 2))) ⟨s,f,0x241e8⟩).bind (X86Routine.run listed [0x241f2] n) := by rfl
@[local simp] private theorem step_241e8 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x241f2] (n+1) ⟨s,f,0x241e8⟩ =
      (X86Routine.execute (.jump 8) ⟨s,f,0x241ea⟩).bind (X86Routine.run listed [0x241f2] n) := by rfl
@[local simp] private theorem step_241ea (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x241f2] (n+1) ⟨s,f,0x241ea⟩ =
      (X86Routine.execute (.control (.cmpMemory 2 ⟨some 0,none,0,12⟩)) ⟨s,f,0x241ed⟩).bind (X86Routine.run listed [0x241f2] n) := by rfl
@[local simp] private theorem step_241ed (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x241f2] (n+1) ⟨s,f,0x241ed⟩ =
      (X86Routine.execute (.jumpSigned 1 3) ⟨s,f,0x241ef⟩).bind (X86Routine.run listed [0x241f2] n) := by rfl
@[local simp] private theorem step_241ef (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x241f2] (n+1) ⟨s,f,0x241ef⟩ =
      (X86Routine.execute (.control (.block (.store ⟨some 0,none,0,12⟩ 2))) ⟨s,f,0x241f2⟩).bind (X86Routine.run listed [0x241f2] n) := by rfl
@[local simp] private theorem stop_horizontal_241f2 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x241f2] n ⟨s,f,0x241f2⟩=some ⟨s,f,0x241f2⟩ := by cases n <;> rfl
theorem horizontal_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x241f2] 5 ⟨s,f,0x241e0⟩=some (horizontal s) := by
  have run : X86Routine.run listed [0x241f2] 5 ⟨s,f,0x241e0⟩=some (horizontal s) := by
    by_cases lo : (load32 s.memory (s.regs 0+(8#32))).toInt≤(s.regs 2).toInt <;>
      by_cases hi : (s.regs 2).toInt≤(load32 s.memory (s.regs 0+(12#32))).toInt
    all_goals simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      X86Block.Address.eval,X86.execute,blockPreservesFlags,horizontal,vertical,firstCall,firstInput,secondCall,secondInput,advanced,
      PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge,cmp32_signed_le,put,write,BitVec.add_assoc,lo,hi,-BitVec.toInt_add]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]
@[local simp] private theorem step_241f2 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x241fa,0x24201] (n+1) ⟨s,f,0x241f2⟩ =
      (X86Routine.execute (.control (.cmpMemory 3 ⟨some 0,none,0,4⟩)) ⟨s,f,0x241f5⟩).bind (X86Routine.run listed [0x241fa,0x24201] n) := by rfl
@[local simp] private theorem step_241f5 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x241fa,0x24201] (n+1) ⟨s,f,0x241f5⟩ =
      (X86Routine.execute (.jumpSigned 0 4) ⟨s,f,0x241f7⟩).bind (X86Routine.run listed [0x241fa,0x24201] n) := by rfl
@[local simp] private theorem step_241f7 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x241fa,0x24201] (n+1) ⟨s,f,0x241f7⟩ =
      (X86Routine.execute (.control (.block (.store ⟨some 0,none,0,4⟩ 3))) ⟨s,f,0x241fa⟩).bind (X86Routine.run listed [0x241fa,0x24201] n) := by rfl
@[local simp] private theorem step_241fb (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x241fa,0x24201] (n+1) ⟨s,f,0x241fb⟩ =
      (X86Routine.execute (.control (.cmpMemory 3 ⟨some 0,none,0,0⟩)) ⟨s,f,0x241fd⟩).bind (X86Routine.run listed [0x241fa,0x24201] n) := by rfl
@[local simp] private theorem step_241fd (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x241fa,0x24201] (n+1) ⟨s,f,0x241fd⟩ =
      (X86Routine.execute (.jumpSigned 1 2) ⟨s,f,0x241ff⟩).bind (X86Routine.run listed [0x241fa,0x24201] n) := by rfl
@[local simp] private theorem step_241ff (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x241fa,0x24201] (n+1) ⟨s,f,0x241ff⟩ =
      (X86Routine.execute (.control (.block (.store ⟨some 0,none,0,0⟩ 3))) ⟨s,f,0x24201⟩).bind (X86Routine.run listed [0x241fa,0x24201] n) := by rfl
@[local simp] private theorem stop_vertical_241fa (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x241fa,0x24201] n ⟨s,f,0x241fa⟩=some ⟨s,f,0x241fa⟩ := by cases n <;> rfl
@[local simp] private theorem stop_vertical_24201 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x241fa,0x24201] n ⟨s,f,0x24201⟩=some ⟨s,f,0x24201⟩ := by cases n <;> rfl
theorem vertical_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x241fa,0x24201] 5 ⟨s,f,0x241f2⟩=some (vertical s) := by
  have run : X86Routine.run listed [0x241fa,0x24201] 5 ⟨s,f,0x241f2⟩=some (vertical s) := by
    by_cases lo : (load32 s.memory (s.regs 0+(4#32))).toInt≤(s.regs 3).toInt <;>
      by_cases hi : (s.regs 3).toInt≤(load32 s.memory (s.regs 0)).toInt
    all_goals simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      X86Block.Address.eval,X86.execute,blockPreservesFlags,horizontal,vertical,firstCall,firstInput,secondCall,secondInput,advanced,
      PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge,cmp32_signed_le,put,write,BitVec.add_assoc,lo,hi,-BitVec.toInt_add]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]
@[local simp] private theorem step_2e682 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x241e0] (n+1) ⟨s,f,0x2e682⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 2 1 0)))) ⟨s,f,0x2e684⟩).bind (X86Routine.run listed [0x241e0] n) := by rfl
@[local simp] private theorem step_2e684 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x241e0] (n+1) ⟨s,f,0x2e684⟩ =
      (X86Routine.execute (.control (.block (.legacy (.mov 0 4)))) ⟨s,f,0x2e686⟩).bind (X86Routine.run listed [0x241e0] n) := by rfl
@[local simp] private theorem step_2e686 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x241e0] (n+1) ⟨s,f,0x2e686⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 3 2 4)))) ⟨s,f,0x2e689⟩).bind (X86Routine.run listed [0x241e0] n) := by rfl
@[local simp] private theorem step_2e689 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x241e0] (n+1) ⟨s,f,0x2e689⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 2 2 0)))) ⟨s,f,0x2e68b⟩).bind (X86Routine.run listed [0x241e0] n) := by rfl
@[local simp] private theorem step_2e68b (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x241e0] (n+1) ⟨s,f,0x2e68b⟩ =
      (X86Routine.execute (.call (-42160)) ⟨s,f,0x2e690⟩).bind (X86Routine.run listed [0x241e0] n) := by
        exact @run_step listed [0x241e0] (.call (-42160)) 5 ⟨s,f,0x2e68b⟩ n
          (by change ¬((0x2e68b : Nat) ∈ [0x241e0]); decide)
          (show listed 0x2e68b=some (.call (-42160),5) from by decide)
@[local simp] private theorem stop_first_241e0 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x241e0] n ⟨s,f,0x241e0⟩=some ⟨s,f,0x241e0⟩ := by cases n <;> rfl
theorem first_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x241e0] 5 ⟨s,f,0x2e682⟩=some (firstCall s f) := by
  have run : X86Routine.run listed [0x241e0] 5 ⟨s,f,0x2e682⟩=some (firstCall s f) := by
    all_goals simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      X86Block.Address.eval,X86.execute,blockPreservesFlags,horizontal,vertical,firstCall,firstInput,secondCall,secondInput,advanced,
      PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge,cmp32_signed_le,put,write,BitVec.add_assoc,-BitVec.toInt_add]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]
@[local simp] private theorem step_2e690 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x241e0] (n+1) ⟨s,f,0x2e690⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 0 1 4)))) ⟨s,f,0x2e693⟩).bind (X86Routine.run listed [0x241e0] n) := by rfl
@[local simp] private theorem step_2e693 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x241e0] (n+1) ⟨s,f,0x2e693⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 3 0 4)))) ⟨s,f,0x2e696⟩).bind (X86Routine.run listed [0x241e0] n) := by rfl
@[local simp] private theorem step_2e696 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x241e0] (n+1) ⟨s,f,0x2e696⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 2 0 0)))) ⟨s,f,0x2e698⟩).bind (X86Routine.run listed [0x241e0] n) := by rfl
@[local simp] private theorem step_2e698 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x241e0] (n+1) ⟨s,f,0x2e698⟩ =
      (X86Routine.execute (.control (.block (.legacy (.mov 0 4)))) ⟨s,f,0x2e69a⟩).bind (X86Routine.run listed [0x241e0] n) := by rfl
@[local simp] private theorem step_2e69a (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x241e0] (n+1) ⟨s,f,0x2e69a⟩ =
      (X86Routine.execute (.addImmediate 6 4) ⟨s,f,0x2e69d⟩).bind (X86Routine.run listed [0x241e0] n) := by rfl
@[local simp] private theorem step_2e69d (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x241e0] (n+1) ⟨s,f,0x2e69d⟩ =
      (X86Routine.execute (.call (-42178)) ⟨s,f,0x2e6a2⟩).bind (X86Routine.run listed [0x241e0] n) := by
        exact @run_step listed [0x241e0] (.call (-42178)) 5 ⟨s,f,0x2e69d⟩ n
          (by change ¬((0x2e69d : Nat) ∈ [0x241e0]); decide)
          (show listed 0x2e69d=some (.call (-42178),5) from by decide)
@[local simp] private theorem stop_second_241e0 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x241e0] n ⟨s,f,0x241e0⟩=some ⟨s,f,0x241e0⟩ := by cases n <;> rfl
theorem second_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x241e0] 6 ⟨s,f,0x2e690⟩=some (secondCall s) := by
  have run : X86Routine.run listed [0x241e0] 6 ⟨s,f,0x2e690⟩=some (secondCall s) := by
    all_goals simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      X86Block.Address.eval,X86.execute,blockPreservesFlags,horizontal,vertical,firstCall,firstInput,secondCall,secondInput,advanced,
      PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge,cmp32_signed_le,put,write,BitVec.add_assoc,-BitVec.toInt_add]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]
@[local simp] private theorem step_2e6a2 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e676,0x2e6af] (n+1) ⟨s,f,0x2e6a2⟩ =
      (X86Routine.execute (.control (.block (.load 0 ⟨none,none,0,0x2c134⟩))) ⟨s,f,0x2e6a7⟩).bind (X86Routine.run listed [0x2e676,0x2e6af] n) := by rfl
@[local simp] private theorem step_2e6a7 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e676,0x2e6af] (n+1) ⟨s,f,0x2e6a7⟩ =
      (X86Routine.execute (.addImmediate 7 1) ⟨s,f,0x2e6a8⟩).bind (X86Routine.run listed [0x2e676,0x2e6af] n) := by rfl
@[local simp] private theorem step_2e6a8 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e676,0x2e6af] (n+1) ⟨s,f,0x2e6a8⟩ =
      (X86Routine.execute (.addImmediate 1 62) ⟨s,f,0x2e6ab⟩).bind (X86Routine.run listed [0x2e676,0x2e6af] n) := by rfl
@[local simp] private theorem step_2e6ab (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e676,0x2e6af] (n+1) ⟨s,f,0x2e6ab⟩ =
      (X86Routine.execute (.compareRegisters 7 0) ⟨s,f,0x2e6ad⟩).bind (X86Routine.run listed [0x2e676,0x2e6af] n) := by rfl
@[local simp] private theorem step_2e6ad (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e676,0x2e6af] (n+1) ⟨s,f,0x2e6ad⟩ =
      (X86Routine.execute (.jumpSigned 3 (-57)) ⟨s,f,0x2e6af⟩).bind (X86Routine.run listed [0x2e676,0x2e6af] n) := by rfl
@[local simp] private theorem stop_advance_2e676 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e676,0x2e6af] n ⟨s,f,0x2e676⟩=some ⟨s,f,0x2e676⟩ := by cases n <;> rfl
@[local simp] private theorem stop_advance_2e6af (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e676,0x2e6af] n ⟨s,f,0x2e6af⟩=some ⟨s,f,0x2e6af⟩ := by cases n <;> rfl
theorem advance_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x2e676,0x2e6af] 5 ⟨s,f,0x2e6a2⟩=some (advanced s) := by
  have run : X86Routine.run listed [0x2e676,0x2e6af] 5 ⟨s,f,0x2e6a2⟩=some (advanced s) := by
    have opposite : (load32 s.memory (0x2c134#32)).toInt≤(s.regs 7+(1#32)).toInt ↔
        ¬(s.regs 7+(1#32)).toInt<(load32 s.memory (0x2c134#32)).toInt := by omega
    by_cases less : (s.regs 7+(1#32)).toInt<(load32 s.memory (0x2c134#32)).toInt
    all_goals simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      X86Block.Address.eval,X86.execute,blockPreservesFlags,horizontal,vertical,firstCall,firstInput,secondCall,secondInput,advanced,
      PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge,cmp32_signed_le,put,write,BitVec.add_assoc,opposite,less,-BitVec.toInt_add]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

/-- Concatenate instruction paths without resetting any part of machine state. -/
theorem prefix_join {p exits n m s t u}
    (a : X86Routine.Prefix p exits n s t) (b : X86Routine.Prefix p exits m t u) :
    X86Routine.Prefix p exits (n+m) s u := by
  induction a with
  | nil => simpa using b
  | step active dec exec rest ih =>
    simpa only [Nat.succ_add] using X86Routine.Prefix.step active dec exec (ih b)

def exits : List Nat := [0x2e676,0x2e6af]
private theorem outside (pc : Nat) (h : program pc ≠ none) : pc ∉ exits := by
  simp only [exits,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false,not_or]
  constructor <;> intro eq <;> subst pc <;> exact h (by decide)
private theorem lift {old n s t} (path : X86Routine.Prefix program old n s t) :
    X86Routine.Prefix program exits n s t :=
  path.transfer program exits (by intros; rfl) outside

@[simp] theorem horizontal_pc (s : X86Memory.State) : (horizontal s).pc=0x241f2 := by
  simp only [horizontal]; split <;> rfl
@[simp] theorem horizontal_regs (s : X86Memory.State) : (horizontal s).core.regs=s.regs := by
  simp only [horizontal]; split <;> rfl
@[simp] theorem vertical_regs (s : X86Memory.State) : (vertical s).core.regs=s.regs := by
  simp only [vertical]; split <;> rfl

/-- The complete helper, including RET, with a uniform instruction bound.
No assumption is made about incoming bounds, coordinate signs or memory aliasing. -/
theorem box_path (s : X86Memory.State) (f : Option Flags) :
    ∃ n, n≤11 ∧ X86Routine.Prefix program exits n ⟨s,f,0x241e0⟩ (boxResult s) := by
  obtain ⟨a,ha,pa,_⟩ := X86Routine.run_path (horizontal_execution s f)
  obtain ⟨b,hb,pb,done⟩ := X86Routine.run_path
    (vertical_execution (horizontal s).core (horizontal s).flags)
  have eta : (⟨(horizontal s).core,(horizontal s).flags,0x241f2⟩ : X86Control.State)=horizontal s := by
    rw [←horizontal_pc s]
  rw [eta] at pb
  have ret : X86Routine.Prefix program exits 1 (vertical (horizontal s).core) (boxResult s) := by
    unfold boxResult
    generalize vertical (horizontal s).core = t at done ⊢
    change X86Routine.Prefix program exits 1 t (returned t)
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at done
    rcases done with h | h
    all_goals
      apply X86Routine.Prefix.step (op:=.ret) (length:=1) (by simp [exits,h])
      · rw [h,decoded _ (by decide)]; rfl
      · rfl
      · exact .nil _
  exact ⟨a+(b+1),by omega,prefix_join (lift pa) (prefix_join (lift pb) ret)⟩

/-- An unrelated word survives the horizontal stores. -/
theorem horizontal_frame (s : X86Memory.State) (a : Word)
    (lo : Apart a (s.regs 0+8)) (hi : Apart a (s.regs 0+12)) :
    load32 (horizontal s).core.memory a=load32 s.memory a := by
  simp only [horizontal]
  split
  · split <;> simp_all [load_store_apart]
  · exact load_store_apart _ _ _ _ lo

theorem vertical_frame (s : X86Memory.State) (a : Word)
    (lo : Apart a (s.regs 0+4)) (hi : Apart a (s.regs 0)) :
    load32 (vertical s).core.memory a=load32 s.memory a := by
  simp only [vertical]
  split
  · split <;> simp_all [load_store_apart]
  · exact load_store_apart _ _ _ _ lo

/-- The four bounding-box words never overlap the CALL return word, even at
unaligned or wrapping stack addresses. -/
theorem stack_apart (sp : Word) :
    Apart (sp-4) sp ∧ Apart (sp-4) (sp+4) ∧
    Apart (sp-4) (sp+8) ∧ Apart (sp-4) (sp+12) := by
  have a := PlayerHeight.slots_apart (sp-4) 0 1 (by decide)
  have b := PlayerHeight.slots_apart (sp-4) 0 2 (by decide)
  have c := PlayerHeight.slots_apart (sp-4) 0 3 (by decide)
  have d := PlayerHeight.slots_apart (sp-4) 0 4 (by decide)
  change Apart (sp-4+(0#32)) (sp-4+(4#32)) at a
  change Apart (sp-4+(0#32)) (sp-4+(8#32)) at b
  change Apart (sp-4+(0#32)) (sp-4+(12#32)) at c
  change Apart (sp-4+(0#32)) (sp-4+(16#32)) at d
  have eq4 : sp-4+(4#32)=sp := BitVec.sub_add_cancel _ _
  have eq8 : sp-4+(8#32)=sp+4 := by
    calc _ = sp-4+((4#32)+4) := rfl
         _ = sp+4 := by rw [←BitVec.add_assoc,eq4]
  have eq12 : sp-4+(12#32)=sp+8 := by
    calc _ = sp-4+((4#32)+8) := rfl
         _ = sp+8 := by rw [←BitVec.add_assoc,eq4]
  have eq16 : sp-4+(16#32)=sp+12 := by
    calc _ = sp-4+((4#32)+12) := rfl
         _ = sp+12 := by rw [←BitVec.add_assoc,eq4]
  simp only [BitVec.add_zero,eq4,eq8,eq12,eq16] at a b c d
  exact ⟨a,b,c,d⟩

/-- A call whose box starts at the caller's ESP returns to its pushed address. -/
theorem call_return (s : X86Memory.State) (ret : Word) (box : s.regs 0=s.regs 4) :
    (boxResult (X86Routine.pushWord s ret)).pc=ret.toNat ∧
    (boxResult (X86Routine.pushWord s ret)).core.regs 4=s.regs 4 := by
  let t := X86Routine.pushWord s ret
  have reg0 : t.regs 0=s.regs 4 := by simp [t,X86Routine.pushWord,put,write,box]
  have reg4 : t.regs 4=s.regs 4-4 := by simp [t,X86Routine.pushWord,put,write]
  obtain ⟨a,b,c,d⟩ := stack_apart (s.regs 4)
  have hf := horizontal_frame t (s.regs 4-4) (by simpa [reg0] using c) (by simpa [reg0] using d)
  have vf := vertical_frame (horizontal t).core (s.regs 4-4)
    (by simpa [reg0] using b) (by simpa [reg0] using a)
  constructor
  · change (load32 (vertical (horizontal t).core).core.memory _).toNat=ret.toNat
    rw [vertical_regs,horizontal_regs,reg4,vf,hf]
    simp [t,X86Routine.pushWord,load_store]
  · change (put (vertical (horizontal t).core).core 4
      ((vertical (horizontal t).core).core.regs 4+4)).regs 4=s.regs 4
    simp [put,write,reg4,BitVec.sub_add_cancel]

def firstDone (s : X86Memory.State) := boxResult (X86Routine.pushWord (firstInput s) 0x2e690)
def secondDone (s : X86Memory.State) := boxResult (X86Routine.pushWord (secondInput s) 0x2e6a2)
def result (s : X86Memory.State) := advanced (secondDone (firstDone s).core).core

theorem first_return (s : X86Memory.State) : (firstDone s).pc=0x2e690 ∧
    (firstDone s).core.regs 4=s.regs 4 := by
  simpa [firstDone,firstInput,put,write] using
    call_return (firstInput s) 0x2e690 (by simp [firstInput,put,write])
theorem second_return (s : X86Memory.State) : (secondDone s).pc=0x2e6a2 ∧
    (secondDone s).core.regs 4=s.regs 4 := by
  simpa [secondDone,secondInput,put,write] using
    call_return (secondInput s) 0x2e6a2 (by simp [secondInput,put,write])

/-- Both original vertex CALLs, both helper RETs, and the original scan advance,
with all reads occurring after preceding writes. The initial line pointer store
is supplied by the preceding selection block, not repeated here. -/
theorem joined_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program exits 38 ⟨s,f,0x2e682⟩=some (result s) := by
  obtain ⟨a,ha,pa,_⟩ := X86Routine.run_path (first_execution s f)
  obtain ⟨b,hb,pb⟩ := box_path (firstCall s f).core (firstCall s f).flags
  have p1 := prefix_join (lift pa) pb
  change X86Routine.Prefix program exits (a+b) ⟨s,f,0x2e682⟩ (firstDone s) at p1
  obtain ⟨c,hc,pc,_⟩ := X86Routine.run_path
    (second_execution (firstDone s).core (firstDone s).flags)
  have eta1 : (⟨(firstDone s).core,(firstDone s).flags,0x2e690⟩ : X86Control.State)=firstDone s := by
    rw [←(first_return s).1]
  rw [eta1] at pc
  obtain ⟨d,hd,pd⟩ := box_path (secondCall (firstDone s).core).core (secondCall (firstDone s).core).flags
  have p2 := prefix_join (lift pc) pd
  change X86Routine.Prefix program exits (c+d) (firstDone s) (secondDone (firstDone s).core) at p2
  have tail := advance_execution (secondDone (firstDone s).core).core (secondDone (firstDone s).core).flags
  have eta2 : (⟨(secondDone (firstDone s).core).core,(secondDone (firstDone s).core).flags,0x2e6a2⟩ : X86Control.State)=secondDone (firstDone s).core := by
    rw [←(second_return (firstDone s).core).1]
  rw [eta2] at tail
  exact (prefix_join p1 p2).finish tail 38 (by omega)

end Doom.Proofs.OriginalGroupBounds
