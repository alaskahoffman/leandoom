import Doom.Proofs.E1M1NoiseAlert
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.NoiseTraversal
open Verification X86 X86Memory X86Control BlockSummary
def code : List UInt8 := [0x31,0xed,0x8b,0x53,0x52,0x8b,0x14,0x2a,0xf6,0x42,0x10,0x4,0x74,0x52,0x89,0xd0,0xe8,0x85,0x53,0x0,0x0,0x83,0x3d,0x38,0xc0,0x2,0x0,0x0,0x7e,0x42,0xf,0xbf,0x42,0x16,0x6b,0xc0,0x12,0x8b,0x3d,0x18,0xc1,0x2,0x0,0x1,0xf8,0x89,0x3c,0x24,0x8b,0x78,0xe,0x39,0xfb,0x75,0xf,0xf,0xbf,0x42,0x18,0x6b,0xc0,0x12,0x3,0x4,0x24,0x8b,0x40,0xe,0xeb,0x2,0x89,0xf8,0xf6,0x42,0x10,0x40,0x74,0xb,0x85,0xc9,0x75,0xe,0xba,0x1,0x0,0x0,0x0,0xeb,0x2,0x89,0xca,0xe8,0x5a,0xff,0xff,0xff,0x46,0x8b,0x43,0x4e,0x83,0xc5,0x4,0x39,0xc6,0x7c,0x97,0x83,0xc4,0x4,0x5d,0x5f,0x5e,0x59,0x5b,0xc3]
def bytesProgram (bytes : List UInt8) : X86Routine.Program := fun pc =>
  if 0x26fa6≤pc ∧ pc<0x2701a then X86Routine.decodeAt bytes (pc-0x26fa6) else none
def program := bytesProgram code
def listed : X86Routine.Program
  | 0x26fa6 => some (.xorRegister 5 5,2)
  | 0x26fa8 => some (.control (.block (.legacy (.load 2 3 82))),3)
  | 0x26fab => some (.control (.block (.load 2 ⟨some 2,some 5,0,0⟩)),3)
  | 0x26fae => some (.testMemoryByte ⟨some 2,none,0,16⟩ 4,4)
  | 0x26fb2 => some (.control (.jumpZero true 82),2)
  | 0x26fb4 => some (.control (.block (.legacy (.mov 0 2))),2)
  | 0x26fb6 => some (.call 21381,5)
  | 0x26fbb => some (.control (.cmpImmediate ⟨none,none,0,0x2c038⟩ 0),7)
  | 0x26fc2 => some (.jumpSigned 1 66,2)
  | 0x26fee => some (.testMemoryByte ⟨some 2,none,0,16⟩ 64,4)
  | 0x26ff2 => some (.control (.jumpZero true 11),2)
  | 0x26ff4 => some (.control (.testWord 1 1),2)
  | 0x26ff6 => some (.control (.jumpZero false 14),2)
  | 0x26ff8 => some (.immediate 2 1,5)
  | 0x26ffd => some (.jump 2,2)
  | 0x26fff => some (.control (.block (.legacy (.mov 2 1))),2)
  | 0x27001 => some (.call (-166),5)
  | 0x27006 => some (.addImmediate 6 1,1)
  | 0x27007 => some (.control (.block (.legacy (.load 0 3 78))),3)
  | 0x2700a => some (.addImmediate 5 4,3)
  | 0x2700d => some (.compareRegisters 6 0,2)
  | 0x2700f => some (.jumpSigned 3 (-105),2)
  | 0x27011 => some (.addImmediate 4 4,3)
  | 0x27014 => some (.pop 5,1)
  | 0x27015 => some (.pop 7,1)
  | 0x27016 => some (.pop 6,1)
  | 0x27017 => some (.pop 1,1)
  | 0x27018 => some (.pop 3,1)
  | 0x27019 => some (.ret,1)
  | _ => none

theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def initialized (s : X86Memory.State) : X86Control.State := ⟨put s 5 0,some (logical32 0),0x26fa8⟩
theorem initialize_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 1 ⟨s,f,0x26fa6⟩ (initialized s) := by
  have p : X86Routine.Prefix listed [] 1 ⟨s,f,0x26fa6⟩ (initialized s) := by
    apply X86Routine.Prefix.step (middle := initialized s) (by simp) rfl (by
      simp [X86Routine.execute,initialized,logical32])
    exact X86Routine.Prefix.nil _
  exact p.transfer program [] decoded (by simp)

def selected (s : X86Memory.State) :=
  let t := put s 2 (load32 s.memory (s.regs 3+(82#32)))
  put t 2 (load32 t.memory (t.regs 2+s.regs 5))
def lineFlags (s : X86Memory.State) (mask : BitVec 8) := s.memory (s.regs 2+(16#32)) &&& mask
def lineGate (s : X86Memory.State) : X86Control.State :=
  let t := selected s
  ⟨t,some (logical8 (lineFlags t (4#8))),if lineFlags t (4#8)=(0#8) then 0x27006 else 0x26fb4⟩
def openingCall (s : X86Memory.State) (f : Option Flags) : X86Control.State :=
  ⟨X86Routine.pushWord (put s 0 (s.regs 2)) 0x26fbb,f,0x2c340⟩
def openingGate (s : X86Memory.State) : X86Control.State :=
  let gap := load32 s.memory (0x2c038#32)
  ⟨s,some (compare32 gap 0),if gap.toInt≤0 then 0x27006 else 0x26fc4⟩

def recursiveCall (s : X86Memory.State) (f : Option Flags) : X86Control.State :=
  ⟨X86Routine.pushWord s 0x27006,f,0x26f60⟩
def blockResult (s : X86Memory.State) : X86Control.State :=
  if lineFlags s (64#8)=(0#8) then recursiveCall (put s 2 (s.regs 1)) (some (logical8 0))
  else if s.regs 1=(0#32) then recursiveCall (put s 2 1) (some (logical32 0))
  else ⟨s,some (logical32 (s.regs 1)),0x27006⟩

def advanced (s : X86Memory.State) : X86Control.State :=
  let t := put (put (put s 6 (s.regs 6+(1#32))) 0 (load32 s.memory (s.regs 3+(78#32)))) 5 (s.regs 5+(4#32))
  ⟨t,some (compare32 (t.regs 6) (t.regs 0)),if (t.regs 6).toInt<(t.regs 0).toInt then 0x26fa8 else 0x27011⟩
def restored (s : X86Memory.State) :=
  PspriteLoop.popped (PspriteLoop.popped (PspriteLoop.popped (PspriteLoop.popped (PspriteLoop.popped s 5) 7) 6) 1) 3
def returned (s : X86Memory.State) : X86Control.State :=
  let t := restored (put s 4 (s.regs 4+(4#32)))
  ⟨put t 4 (t.regs 4+4),none,(load32 t.memory (t.regs 4)).toNat⟩

@[local simp] private theorem step_line_26fa8 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x27006,0x26fb4] (n+1) ⟨s,f,0x26fa8⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 2 3 82)))) ⟨s,f,0x26fab⟩).bind (X86Routine.run listed [0x27006,0x26fb4] n) := by rfl

@[local simp] private theorem step_line_26fab (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x27006,0x26fb4] (n+1) ⟨s,f,0x26fab⟩ =
      (X86Routine.execute (.control (.block (.load 2 ⟨some 2,some 5,0,0⟩))) ⟨s,f,0x26fae⟩).bind (X86Routine.run listed [0x27006,0x26fb4] n) := by rfl

@[local simp] private theorem step_line_26fae (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x27006,0x26fb4] (n+1) ⟨s,f,0x26fae⟩ =
      (X86Routine.execute (.testMemoryByte ⟨some 2,none,0,16⟩ 4) ⟨s,f,0x26fb2⟩).bind (X86Routine.run listed [0x27006,0x26fb4] n) := by rfl

@[local simp] private theorem step_line_26fb2 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x27006,0x26fb4] (n+1) ⟨s,f,0x26fb2⟩ =
      (X86Routine.execute (.control (.jumpZero true 82)) ⟨s,f,0x26fb4⟩).bind (X86Routine.run listed [0x27006,0x26fb4] n) := by rfl
@[local simp] private theorem stop_line_27006 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x27006,0x26fb4] n ⟨s,f,0x27006⟩=some ⟨s,f,0x27006⟩ := by cases n <;> rfl
@[local simp] private theorem stop_line_26fb4 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x27006,0x26fb4] n ⟨s,f,0x26fb4⟩=some ⟨s,f,0x26fb4⟩ := by cases n <;> rfl

@[local simp] private theorem step_opening_call_26fb4 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2c340] (n+1) ⟨s,f,0x26fb4⟩ =
      (X86Routine.execute (.control (.block (.legacy (.mov 0 2)))) ⟨s,f,0x26fb6⟩).bind (X86Routine.run listed [0x2c340] n) := by rfl

@[local simp] private theorem step_opening_call_26fb6 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2c340] (n+1) ⟨s,f,0x26fb6⟩ =
      (X86Routine.execute (.call 21381) ⟨s,f,0x26fbb⟩).bind (X86Routine.run listed [0x2c340] n) := by
  simp [X86Routine.run,listed]
@[local simp] private theorem stop_opening_call_2c340 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2c340] n ⟨s,f,0x2c340⟩=some ⟨s,f,0x2c340⟩ := by cases n <;> rfl

@[local simp] private theorem step_opening_gate_26fbb (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x27006,0x26fc4] (n+1) ⟨s,f,0x26fbb⟩ =
      (X86Routine.execute (.control (.cmpImmediate ⟨none,none,0,0x2c038⟩ 0)) ⟨s,f,0x26fc2⟩).bind (X86Routine.run listed [0x27006,0x26fc4] n) := by rfl

@[local simp] private theorem step_opening_gate_26fc2 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x27006,0x26fc4] (n+1) ⟨s,f,0x26fc2⟩ =
      (X86Routine.execute (.jumpSigned 1 66) ⟨s,f,0x26fc4⟩).bind (X86Routine.run listed [0x27006,0x26fc4] n) := by rfl
@[local simp] private theorem stop_opening_gate_27006 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x27006,0x26fc4] n ⟨s,f,0x27006⟩=some ⟨s,f,0x27006⟩ := by cases n <;> rfl
@[local simp] private theorem stop_opening_gate_26fc4 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x27006,0x26fc4] n ⟨s,f,0x26fc4⟩=some ⟨s,f,0x26fc4⟩ := by cases n <;> rfl

@[local simp] private theorem step_block_26fee (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x26f60,0x27006] (n+1) ⟨s,f,0x26fee⟩ =
      (X86Routine.execute (.testMemoryByte ⟨some 2,none,0,16⟩ 64) ⟨s,f,0x26ff2⟩).bind (X86Routine.run listed [0x26f60,0x27006] n) := by rfl

@[local simp] private theorem step_block_26ff2 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x26f60,0x27006] (n+1) ⟨s,f,0x26ff2⟩ =
      (X86Routine.execute (.control (.jumpZero true 11)) ⟨s,f,0x26ff4⟩).bind (X86Routine.run listed [0x26f60,0x27006] n) := by rfl

@[local simp] private theorem step_block_26ff4 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x26f60,0x27006] (n+1) ⟨s,f,0x26ff4⟩ =
      (X86Routine.execute (.control (.testWord 1 1)) ⟨s,f,0x26ff6⟩).bind (X86Routine.run listed [0x26f60,0x27006] n) := by rfl

@[local simp] private theorem step_block_26ff6 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x26f60,0x27006] (n+1) ⟨s,f,0x26ff6⟩ =
      (X86Routine.execute (.control (.jumpZero false 14)) ⟨s,f,0x26ff8⟩).bind (X86Routine.run listed [0x26f60,0x27006] n) := by rfl

@[local simp] private theorem step_block_26ff8 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x26f60,0x27006] (n+1) ⟨s,f,0x26ff8⟩ =
      (X86Routine.execute (.immediate 2 1) ⟨s,f,0x26ffd⟩).bind (X86Routine.run listed [0x26f60,0x27006] n) := by rfl

@[local simp] private theorem step_block_26ffd (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x26f60,0x27006] (n+1) ⟨s,f,0x26ffd⟩ =
      (X86Routine.execute (.jump 2) ⟨s,f,0x26fff⟩).bind (X86Routine.run listed [0x26f60,0x27006] n) := by rfl

@[local simp] private theorem step_block_26fff (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x26f60,0x27006] (n+1) ⟨s,f,0x26fff⟩ =
      (X86Routine.execute (.control (.block (.legacy (.mov 2 1)))) ⟨s,f,0x27001⟩).bind (X86Routine.run listed [0x26f60,0x27006] n) := by rfl

@[local simp] private theorem step_block_27001 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x26f60,0x27006] (n+1) ⟨s,f,0x27001⟩ =
      (X86Routine.execute (.call (-166)) ⟨s,f,0x27006⟩).bind (X86Routine.run listed [0x26f60,0x27006] n) := by rfl
@[local simp] private theorem stop_block_26f60 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x26f60,0x27006] n ⟨s,f,0x26f60⟩=some ⟨s,f,0x26f60⟩ := by cases n <;> rfl
@[local simp] private theorem stop_block_27006 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x26f60,0x27006] n ⟨s,f,0x27006⟩=some ⟨s,f,0x27006⟩ := by cases n <;> rfl

@[local simp] private theorem step_advance_27006 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x26fa8,0x27011] (n+1) ⟨s,f,0x27006⟩ =
      (X86Routine.execute (.addImmediate 6 1) ⟨s,f,0x27007⟩).bind (X86Routine.run listed [0x26fa8,0x27011] n) := by rfl

@[local simp] private theorem step_advance_27007 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x26fa8,0x27011] (n+1) ⟨s,f,0x27007⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 0 3 78)))) ⟨s,f,0x2700a⟩).bind (X86Routine.run listed [0x26fa8,0x27011] n) := by rfl

@[local simp] private theorem step_advance_2700a (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x26fa8,0x27011] (n+1) ⟨s,f,0x2700a⟩ =
      (X86Routine.execute (.addImmediate 5 4) ⟨s,f,0x2700d⟩).bind (X86Routine.run listed [0x26fa8,0x27011] n) := by rfl

@[local simp] private theorem step_advance_2700d (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x26fa8,0x27011] (n+1) ⟨s,f,0x2700d⟩ =
      (X86Routine.execute (.compareRegisters 6 0) ⟨s,f,0x2700f⟩).bind (X86Routine.run listed [0x26fa8,0x27011] n) := by rfl

@[local simp] private theorem step_advance_2700f (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x26fa8,0x27011] (n+1) ⟨s,f,0x2700f⟩ =
      (X86Routine.execute (.jumpSigned 3 (-105)) ⟨s,f,0x27011⟩).bind (X86Routine.run listed [0x26fa8,0x27011] n) := by rfl
@[local simp] private theorem stop_advance_26fa8 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x26fa8,0x27011] n ⟨s,f,0x26fa8⟩=some ⟨s,f,0x26fa8⟩ := by cases n <;> rfl
@[local simp] private theorem stop_advance_27011 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x26fa8,0x27011] n ⟨s,f,0x27011⟩=some ⟨s,f,0x27011⟩ := by cases n <;> rfl

theorem line_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x27006,0x26fb4] 4 ⟨s,f,0x26fa8⟩=some (lineGate s) := by
  have run : X86Routine.run listed [0x27006,0x26fb4] 4 ⟨s,f,0x26fa8⟩=some (lineGate s) := by
    by_cases single : lineFlags (selected s) (4#8)=(0#8)
    all_goals
      simp [lineFlags,selected,put,write] at single
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
        X86Block.Address.eval,blockPreservesFlags,lineGate,selected,lineFlags,put,write,logical8,single]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

theorem opening_call_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x2c340] 2 ⟨s,f,0x26fb4⟩=some (openingCall s f) := by
  have run : X86Routine.run listed [0x2c340] 2 ⟨s,f,0x26fb4⟩=some (openingCall s f) := by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      blockPreservesFlags,openingCall]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

theorem opening_gate_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x27006,0x26fc4] 2 ⟨s,f,0x26fbb⟩=some (openingGate s) := by
  have run : X86Routine.run listed [0x27006,0x26fc4] 2 ⟨s,f,0x26fbb⟩=some (openingGate s) := by
    by_cases closed : (load32 s.memory (0x2c038#32)).toInt≤0 <;>
      simp [X86Routine.execute,X86Control.execute,X86Block.Address.eval,
        openingGate,cmp32_signed_le,closed]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

/-- Preserve the incoming count for an ordinary line; crossing a sound block
requires zero incoming blocks and passes one. The actual CALL saves 0x27006. -/
theorem block_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x26f60,0x27006] 7 ⟨s,f,0x26fee⟩=some (blockResult s) := by
  have run : X86Routine.run listed [0x26f60,0x27006] 7 ⟨s,f,0x26fee⟩=some (blockResult s) := by
    by_cases blocked : lineFlags s (64#8)=(0#8)
    all_goals
      by_cases zero : s.regs 1=(0#32)
      all_goals
        simp only [lineFlags] at blocked
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
          X86Block.Address.eval,blockPreservesFlags,blockResult,lineFlags,recursiveCall,
          logical8,logical32,put,write,blocked,zero]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

theorem advance_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x26fa8,0x27011] 5 ⟨s,f,0x27006⟩=some (advanced s) := by
  have run : X86Routine.run listed [0x26fa8,0x27011] 5 ⟨s,f,0x27006⟩=some (advanced s) := by
    by_cases more : (s.regs 6+(1#32)).toInt<(load32 s.memory (s.regs 3+(78#32))).toInt <;>
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
        blockPreservesFlags,advanced,put,write,PlayerArmor.cmp_lt,PlayerHeight.cmp_ge_prop,←Int.not_lt,more,-BitVec.toInt_add]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

/-- Discard the real local stack word, restore all five saves, and RET through
current memory. ADD's flags are conservatively invalidated and never consumed. -/
theorem return_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 7 ⟨s,f,0x27011⟩ (returned s) := by
  let a := put s 4 (s.regs 4+(4#32))
  let b := PspriteLoop.popped a 5
  let c := PspriteLoop.popped b 7
  let d := PspriteLoop.popped c 6
  let e := PspriteLoop.popped d 1
  let g := restored a
  have p : X86Routine.Prefix listed [] 7 ⟨s,f,0x27011⟩ (returned s) := by
    apply X86Routine.Prefix.step (middle := ⟨a,none,0x27014⟩) (by simp) rfl rfl
    apply X86Routine.Prefix.step (middle := ⟨b,none,0x27015⟩) (by simp) rfl rfl
    apply X86Routine.Prefix.step (middle := ⟨c,none,0x27016⟩) (by simp) rfl rfl
    apply X86Routine.Prefix.step (middle := ⟨d,none,0x27017⟩) (by simp) rfl rfl
    apply X86Routine.Prefix.step (middle := ⟨e,none,0x27018⟩) (by simp) rfl rfl
    apply X86Routine.Prefix.step (middle := ⟨g,none,0x27019⟩) (by simp) rfl rfl
    apply X86Routine.Prefix.step (middle := returned s) (by simp) rfl rfl
    exact X86Routine.Prefix.nil _
  exact p.transfer program [] decoded (by simp)
end Doom.Proofs.NoiseTraversal
