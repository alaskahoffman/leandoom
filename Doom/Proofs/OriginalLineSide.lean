import Doom.Proofs.OriginalLineInterceptEntry
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalLineSide
open Verification X86 X86Memory X86Control BlockSummary
def code : List UInt8 := [0x51,0x56,0x57,0x55,0x89,0xd9,0x83,0x7b,0x8,0x0,0x75,0x28,0x8b,0x11,0x3b,0x2,0x7f,0x11,0x83,0x79,0xc,0x0,0xf,0x9f,0xc0,0x25,0xff,0x0,0x0,0x0,0x5d,0x5f,0x5e,0x59,0xc3,0x83,0x79,0xc,0x0,0xf,0x9c,0xc0,0x25,0xff,0x0,0x0,0x0,0x5d,0x5f,0x5e,0x59,0xc3,0x83,0x79,0xc,0x0,0x75,0x29,0x8b,0x1,0x3b,0x50,0x4,0x7f,0x11,0x83,0x79,0x8,0x0,0xf,0x9c,0xc0,0x25,0xff,0x0,0x0,0x0,0x5d,0x5f,0x5e,0x59,0xc3,0x83,0x79,0x8,0x0,0xf,0x9f,0xc0,0x25,0xff,0x0,0x0,0x0,0x5d,0x5f,0x5e,0x59,0xc3,0x8b,0x31,0x89,0xc3,0x8b,0x3e,0x8b,0x41,0xc,0x8b,0x6e,0x4,0xc1,0xf8,0x10,0x29,0xfb,0x89,0xd6,0xf7,0xeb,0xf,0xac,0xd0,0x10,0x89,0xc7,0x8b,0x59,0x8,0x29,0xee,0xc1,0xfb,0x10,0x89,0xf0,0xf7,0xeb,0xf,0xac,0xd0,0x10,0x39,0xf8,0x7d,0x7,0x31,0xc0,0x5d,0x5f,0x5e,0x59,0xc3,0xb8,0x1,0x0,0x0,0x0,0x5d,0x5f,0x5e,0x59,0xc3]
def bytesProgram (bytes : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2c010≤pc ∧ pc<0x2c0b3 then X86Routine.decodeAt bytes (pc-0x2c010) else none
def program := bytesProgram code
def listed : X86Routine.Program
  | 0x2c010 => some (.push 1,1)
  | 0x2c011 => some (.push 6,1)
  | 0x2c012 => some (.push 7,1)
  | 0x2c013 => some (.push 5,1)
  | 0x2c014 => some (.control (.block (.legacy (.mov 1 3))),2)
  | 0x2c016 => some (.control (.cmpImmediate ⟨some 3,none,0,8⟩ 0),4)
  | 0x2c01a => some (.control (.jumpZero false 40),2)
  | 0x2c01c => some (.control (.block (.legacy (.load 2 1 0))),2)
  | 0x2c01e => some (.control (.cmpMemory 0 ⟨some 2,none,0,0⟩),2)
  | 0x2c020 => some (.jumpSigned 2 17,2)
  | 0x2c022 => some (.control (.cmpImmediate ⟨some 1,none,0,12⟩ 0),4)
  | 0x2c026 => some (.setGreater 0,3)
  | 0x2c029 => some (.control (.andEax 255),5)
  | 0x2c02e => some (.pop 5,1)
  | 0x2c02f => some (.pop 7,1)
  | 0x2c030 => some (.pop 6,1)
  | 0x2c031 => some (.pop 1,1)
  | 0x2c032 => some (.ret,1)
  | 0x2c033 => some (.control (.cmpImmediate ⟨some 1,none,0,12⟩ 0),4)
  | 0x2c037 => some (.setLess 0,3)
  | 0x2c03a => some (.control (.andEax 255),5)
  | 0x2c03f => some (.pop 5,1)
  | 0x2c040 => some (.pop 7,1)
  | 0x2c041 => some (.pop 6,1)
  | 0x2c042 => some (.pop 1,1)
  | 0x2c043 => some (.ret,1)
  | 0x2c044 => some (.control (.cmpImmediate ⟨some 1,none,0,12⟩ 0),4)
  | 0x2c048 => some (.control (.jumpZero false 41),2)
  | 0x2c04a => some (.control (.block (.legacy (.load 0 1 0))),2)
  | 0x2c04c => some (.control (.cmpMemory 2 ⟨some 0,none,0,4⟩),3)
  | 0x2c04f => some (.jumpSigned 2 17,2)
  | 0x2c051 => some (.control (.cmpImmediate ⟨some 1,none,0,8⟩ 0),4)
  | 0x2c055 => some (.setLess 0,3)
  | 0x2c058 => some (.control (.andEax 255),5)
  | 0x2c05d => some (.pop 5,1)
  | 0x2c05e => some (.pop 7,1)
  | 0x2c05f => some (.pop 6,1)
  | 0x2c060 => some (.pop 1,1)
  | 0x2c061 => some (.ret,1)
  | 0x2c062 => some (.control (.cmpImmediate ⟨some 1,none,0,8⟩ 0),4)
  | 0x2c066 => some (.setGreater 0,3)
  | 0x2c069 => some (.control (.andEax 255),5)
  | 0x2c06e => some (.pop 5,1)
  | 0x2c06f => some (.pop 7,1)
  | 0x2c070 => some (.pop 6,1)
  | 0x2c071 => some (.pop 1,1)
  | 0x2c072 => some (.ret,1)
  | 0x2c073 => some (.control (.block (.legacy (.load 6 1 0))),2)
  | 0x2c075 => some (.control (.block (.legacy (.mov 3 0))),2)
  | 0x2c077 => some (.control (.block (.legacy (.load 7 6 0))),2)
  | 0x2c079 => some (.control (.block (.legacy (.load 0 1 12))),3)
  | 0x2c07c => some (.control (.block (.legacy (.load 5 6 4))),3)
  | 0x2c07f => some (.sar 0 16,3)
  | 0x2c082 => some (.control (.block (.arithmetic (.sub 3 7))),2)
  | 0x2c084 => some (.control (.block (.legacy (.mov 6 2))),2)
  | 0x2c086 => some (.control (.block (.arithmetic (.imul 3))),2)
  | 0x2c088 => some (.control (.block (.arithmetic (.shrd 0 2 16))),4)
  | 0x2c08c => some (.control (.block (.legacy (.mov 7 0))),2)
  | 0x2c08e => some (.control (.block (.legacy (.load 3 1 8))),3)
  | 0x2c091 => some (.control (.block (.arithmetic (.sub 6 5))),2)
  | 0x2c093 => some (.sar 3 16,3)
  | 0x2c096 => some (.control (.block (.legacy (.mov 0 6))),2)
  | 0x2c098 => some (.control (.block (.arithmetic (.imul 3))),2)
  | 0x2c09a => some (.control (.block (.arithmetic (.shrd 0 2 16))),4)
  | 0x2c09e => some (.compareRegisters 0 7,2)
  | 0x2c0a0 => some (.jumpSigned 0 7,2)
  | 0x2c0a2 => some (.xorRegister 0 0,2)
  | 0x2c0a4 => some (.pop 5,1)
  | 0x2c0a5 => some (.pop 7,1)
  | 0x2c0a6 => some (.pop 6,1)
  | 0x2c0a7 => some (.pop 1,1)
  | 0x2c0a8 => some (.ret,1)
  | 0x2c0a9 => some (.immediate 0 1,5)
  | 0x2c0ae => some (.pop 5,1)
  | 0x2c0af => some (.pop 7,1)
  | 0x2c0b0 => some (.pop 6,1)
  | 0x2c0b1 => some (.pop 1,1)
  | 0x2c0b2 => some (.ret,1)
  | _ => none
theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def prepare1 (s : X86Memory.State) := X86Routine.pushWord (s) ((s).regs 1)
def prepare2 (s : X86Memory.State) := X86Routine.pushWord (prepare1 s) ((prepare1 s).regs 6)
def prepare3 (s : X86Memory.State) := X86Routine.pushWord (prepare2 s) ((prepare2 s).regs 7)
def prepare4 (s : X86Memory.State) := X86Routine.pushWord (prepare3 s) ((prepare3 s).regs 5)
def prepare5 (s : X86Memory.State) := put (prepare4 s) 1 ((prepare4 s).regs 3)
def prepare := prepare5
theorem prepare_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 5 ⟨s,f,0x2c010⟩ ⟨prepare s,f,0x2c016⟩ := by
  have path : X86Routine.Prefix listed [] 5 ⟨s,f,0x2c010⟩ ⟨prepare s,f,0x2c016⟩ := by
    apply X86Routine.Prefix.step (middle := ⟨prepare1 s,f,0x2c011⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,prepare1,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := ⟨prepare2 s,f,0x2c012⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,prepare1,prepare2,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := ⟨prepare3 s,f,0x2c013⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,prepare1,prepare2,prepare3,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := ⟨prepare4 s,f,0x2c014⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,prepare1,prepare2,prepare3,prepare4,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := ⟨prepare5 s,f,0x2c016⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,prepare1,prepare2,prepare3,prepare4,prepare5,X86Routine.pushWord])
    exact .nil _
  exact path.transfer program [] decoded (by simp)

def diagonal1 (s : X86Memory.State) := put (s) 6 (load32 (s).memory ((s).regs 1+0))
def diagonal2 (s : X86Memory.State) := put (diagonal1 s) 3 ((diagonal1 s).regs 0)
def diagonal3 (s : X86Memory.State) := put (diagonal2 s) 7 (load32 (diagonal2 s).memory ((diagonal2 s).regs 6+0))
def diagonal4 (s : X86Memory.State) := put (diagonal3 s) 0 (load32 (diagonal3 s).memory ((diagonal3 s).regs 1+12))
def diagonal5 (s : X86Memory.State) := put (diagonal4 s) 5 (load32 (diagonal4 s).memory ((diagonal4 s).regs 6+4))
def diagonal6 (s : X86Memory.State) := put (diagonal5 s) 0 (((diagonal5 s).regs 0).sshiftRight 16)
def diagonal7 (s : X86Memory.State) := put (diagonal6 s) 3 ((diagonal6 s).regs 3-(diagonal6 s).regs 7)
def diagonal8 (s : X86Memory.State) := put (diagonal7 s) 6 ((diagonal7 s).regs 2)
def diagonal9 (s : X86Memory.State) := X86Block.execute (.arithmetic (.imul 3)) (diagonal8 s)
def diagonal10 (s : X86Memory.State) := multiply (diagonal8 s)
def diagonal11 (s : X86Memory.State) := put (diagonal10 s) 7 ((diagonal10 s).regs 0)
def diagonal12 (s : X86Memory.State) := put (diagonal11 s) 3 (load32 (diagonal11 s).memory ((diagonal11 s).regs 1+8))
def diagonal13 (s : X86Memory.State) := put (diagonal12 s) 6 ((diagonal12 s).regs 6-(diagonal12 s).regs 5)
def diagonal14 (s : X86Memory.State) := put (diagonal13 s) 3 (((diagonal13 s).regs 3).sshiftRight 16)
def diagonal15 (s : X86Memory.State) := put (diagonal14 s) 0 ((diagonal14 s).regs 6)
def diagonal16 (s : X86Memory.State) := X86Block.execute (.arithmetic (.imul 3)) (diagonal15 s)
def diagonal17 (s : X86Memory.State) := multiply (diagonal15 s)
def diagonal := diagonal17
theorem diagonal_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 17 ⟨s,f,0x2c073⟩ ⟨diagonal s,none,0x2c09e⟩ := by
  have path : X86Routine.Prefix listed [] 17 ⟨s,f,0x2c073⟩ ⟨diagonal s,none,0x2c09e⟩ := by
    apply X86Routine.Prefix.step (middle := ⟨diagonal1 s,f,0x2c075⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,diagonal1,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := ⟨diagonal2 s,f,0x2c077⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,diagonal1,diagonal2,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := ⟨diagonal3 s,f,0x2c079⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,diagonal1,diagonal2,diagonal3,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := ⟨diagonal4 s,f,0x2c07c⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,diagonal1,diagonal2,diagonal3,diagonal4,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := ⟨diagonal5 s,f,0x2c07f⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,diagonal1,diagonal2,diagonal3,diagonal4,diagonal5,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := ⟨diagonal6 s,none,0x2c082⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,diagonal1,diagonal2,diagonal3,diagonal4,diagonal5,diagonal6,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := ⟨diagonal7 s,none,0x2c084⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,diagonal1,diagonal2,diagonal3,diagonal4,diagonal5,diagonal6,diagonal7,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := ⟨diagonal8 s,none,0x2c086⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,diagonal1,diagonal2,diagonal3,diagonal4,diagonal5,diagonal6,diagonal7,diagonal8,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := ⟨diagonal9 s,none,0x2c088⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,diagonal1,diagonal2,diagonal3,diagonal4,diagonal5,diagonal6,diagonal7,diagonal8,diagonal9,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := ⟨diagonal10 s,none,0x2c08c⟩) (by simp) (by rfl) (by simpa [X86Routine.execute,X86Control.execute,diagonal10,diagonal9,blockPreservesFlags] using congrArg (fun c => some (X86Control.State.mk c none 0x2c08c)) (multiply_correct (diagonal8 s)))
    apply X86Routine.Prefix.step (middle := ⟨diagonal11 s,none,0x2c08e⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,diagonal1,diagonal2,diagonal3,diagonal4,diagonal5,diagonal6,diagonal7,diagonal8,diagonal9,diagonal10,diagonal11,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := ⟨diagonal12 s,none,0x2c091⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,diagonal1,diagonal2,diagonal3,diagonal4,diagonal5,diagonal6,diagonal7,diagonal8,diagonal9,diagonal10,diagonal11,diagonal12,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := ⟨diagonal13 s,none,0x2c093⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,diagonal1,diagonal2,diagonal3,diagonal4,diagonal5,diagonal6,diagonal7,diagonal8,diagonal9,diagonal10,diagonal11,diagonal12,diagonal13,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := ⟨diagonal14 s,none,0x2c096⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,diagonal1,diagonal2,diagonal3,diagonal4,diagonal5,diagonal6,diagonal7,diagonal8,diagonal9,diagonal10,diagonal11,diagonal12,diagonal13,diagonal14,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := ⟨diagonal15 s,none,0x2c098⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,diagonal1,diagonal2,diagonal3,diagonal4,diagonal5,diagonal6,diagonal7,diagonal8,diagonal9,diagonal10,diagonal11,diagonal12,diagonal13,diagonal14,diagonal15,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := ⟨diagonal16 s,none,0x2c09a⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,diagonal1,diagonal2,diagonal3,diagonal4,diagonal5,diagonal6,diagonal7,diagonal8,diagonal9,diagonal10,diagonal11,diagonal12,diagonal13,diagonal14,diagonal15,diagonal16,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := ⟨diagonal17 s,none,0x2c09e⟩) (by simp) (by rfl) (by simpa [X86Routine.execute,X86Control.execute,diagonal17,diagonal16,blockPreservesFlags] using congrArg (fun c => some (X86Control.State.mk c none 0x2c09e)) (multiply_correct (diagonal15 s)))
    exact .nil _
  exact path.transfer program [] decoded (by simp)

def vertex (s : X86Memory.State) := load32 s.memory (s.regs 1)
def vx (s : X86Memory.State) := load32 s.memory (vertex s)
def vy (s : X86Memory.State) := load32 s.memory (vertex s+4)
def dx (s : X86Memory.State) := load32 s.memory (s.regs 1+8)
def dy (s : X86Memory.State) := load32 s.memory (s.regs 1+12)
def bit (b : Bool) : Word := if b then 1 else 0

def pop1 (s : X86Memory.State) := put (put s 4 (s.regs 4+4)) 5 (load32 s.memory (s.regs 4))
def pop2 (s : X86Memory.State) := put (put (pop1 s) 4 (s.regs 4+8)) 7 (load32 s.memory (s.regs 4+4))
def pop3 (s : X86Memory.State) := put (put (pop2 s) 4 (s.regs 4+12)) 6 (load32 s.memory (s.regs 4+8))
def pop4 (s : X86Memory.State) := put (put (pop3 s) 4 (s.regs 4+16)) 1 (load32 s.memory (s.regs 4+12))
def finish (s : X86Memory.State) (f : Option Flags) : X86Control.State :=
  ⟨put (pop4 s) 4 (s.regs 4+20),f,(load32 s.memory (s.regs 4+16)).toNat⟩
theorem finish_execution (s : X86Memory.State) (f : Option Flags) (pc : Nat)
    (atReturn : pc∈[0x2c02e,0x2c03f,0x2c05d,0x2c06e,0x2c0a4,0x2c0ae]) :
    X86Routine.Prefix program [] 5 ⟨s,f,pc⟩ (finish s f) := by
  have path : X86Routine.Prefix listed [] 5 ⟨s,f,pc⟩ (finish s f) := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at atReturn
    rcases atReturn with rfl|rfl|rfl|rfl|rfl|rfl
    · apply X86Routine.Prefix.step (middle := ⟨pop1 s,f,0x2c02f⟩) (by simp) (by rfl) (by simp [X86Routine.execute,pop1,pop2,pop3,pop4,finish,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle := ⟨pop2 s,f,0x2c030⟩) (by simp) (by rfl) (by simp [X86Routine.execute,pop1,pop2,pop3,pop4,finish,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle := ⟨pop3 s,f,0x2c031⟩) (by simp) (by rfl) (by simp [X86Routine.execute,pop1,pop2,pop3,pop4,finish,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle := ⟨pop4 s,f,0x2c032⟩) (by simp) (by rfl) (by simp [X86Routine.execute,pop1,pop2,pop3,pop4,finish,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle := finish s f) (by simp) (by rfl) (by simp [X86Routine.execute,pop1,pop2,pop3,pop4,finish,put,write,BitVec.add_assoc])
      exact .nil _
    · apply X86Routine.Prefix.step (middle := ⟨pop1 s,f,0x2c040⟩) (by simp) (by rfl) (by simp [X86Routine.execute,pop1,pop2,pop3,pop4,finish,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle := ⟨pop2 s,f,0x2c041⟩) (by simp) (by rfl) (by simp [X86Routine.execute,pop1,pop2,pop3,pop4,finish,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle := ⟨pop3 s,f,0x2c042⟩) (by simp) (by rfl) (by simp [X86Routine.execute,pop1,pop2,pop3,pop4,finish,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle := ⟨pop4 s,f,0x2c043⟩) (by simp) (by rfl) (by simp [X86Routine.execute,pop1,pop2,pop3,pop4,finish,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle := finish s f) (by simp) (by rfl) (by simp [X86Routine.execute,pop1,pop2,pop3,pop4,finish,put,write,BitVec.add_assoc])
      exact .nil _
    · apply X86Routine.Prefix.step (middle := ⟨pop1 s,f,0x2c05e⟩) (by simp) (by rfl) (by simp [X86Routine.execute,pop1,pop2,pop3,pop4,finish,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle := ⟨pop2 s,f,0x2c05f⟩) (by simp) (by rfl) (by simp [X86Routine.execute,pop1,pop2,pop3,pop4,finish,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle := ⟨pop3 s,f,0x2c060⟩) (by simp) (by rfl) (by simp [X86Routine.execute,pop1,pop2,pop3,pop4,finish,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle := ⟨pop4 s,f,0x2c061⟩) (by simp) (by rfl) (by simp [X86Routine.execute,pop1,pop2,pop3,pop4,finish,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle := finish s f) (by simp) (by rfl) (by simp [X86Routine.execute,pop1,pop2,pop3,pop4,finish,put,write,BitVec.add_assoc])
      exact .nil _
    · apply X86Routine.Prefix.step (middle := ⟨pop1 s,f,0x2c06f⟩) (by simp) (by rfl) (by simp [X86Routine.execute,pop1,pop2,pop3,pop4,finish,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle := ⟨pop2 s,f,0x2c070⟩) (by simp) (by rfl) (by simp [X86Routine.execute,pop1,pop2,pop3,pop4,finish,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle := ⟨pop3 s,f,0x2c071⟩) (by simp) (by rfl) (by simp [X86Routine.execute,pop1,pop2,pop3,pop4,finish,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle := ⟨pop4 s,f,0x2c072⟩) (by simp) (by rfl) (by simp [X86Routine.execute,pop1,pop2,pop3,pop4,finish,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle := finish s f) (by simp) (by rfl) (by simp [X86Routine.execute,pop1,pop2,pop3,pop4,finish,put,write,BitVec.add_assoc])
      exact .nil _
    · apply X86Routine.Prefix.step (middle := ⟨pop1 s,f,0x2c0a5⟩) (by simp) (by rfl) (by simp [X86Routine.execute,pop1,pop2,pop3,pop4,finish,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle := ⟨pop2 s,f,0x2c0a6⟩) (by simp) (by rfl) (by simp [X86Routine.execute,pop1,pop2,pop3,pop4,finish,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle := ⟨pop3 s,f,0x2c0a7⟩) (by simp) (by rfl) (by simp [X86Routine.execute,pop1,pop2,pop3,pop4,finish,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle := ⟨pop4 s,f,0x2c0a8⟩) (by simp) (by rfl) (by simp [X86Routine.execute,pop1,pop2,pop3,pop4,finish,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle := finish s f) (by simp) (by rfl) (by simp [X86Routine.execute,pop1,pop2,pop3,pop4,finish,put,write,BitVec.add_assoc])
      exact .nil _
    · apply X86Routine.Prefix.step (middle := ⟨pop1 s,f,0x2c0af⟩) (by simp) (by rfl) (by simp [X86Routine.execute,pop1,pop2,pop3,pop4,finish,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle := ⟨pop2 s,f,0x2c0b0⟩) (by simp) (by rfl) (by simp [X86Routine.execute,pop1,pop2,pop3,pop4,finish,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle := ⟨pop3 s,f,0x2c0b1⟩) (by simp) (by rfl) (by simp [X86Routine.execute,pop1,pop2,pop3,pop4,finish,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle := ⟨pop4 s,f,0x2c0b2⟩) (by simp) (by rfl) (by simp [X86Routine.execute,pop1,pop2,pop3,pop4,finish,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle := finish s f) (by simp) (by rfl) (by simp [X86Routine.execute,pop1,pop2,pop3,pop4,finish,put,write,BitVec.add_assoc])
      exact .nil _
  exact path.transfer program [] decoded (by simp)

theorem mask_byte (old : Word) (b : BitVec 8) :
    ((old &&& (0xffffff00#32)) ||| b.zeroExtend 32) &&& (255#32) = b.zeroExtend 32 := by
  change ((old &&& (4294967040#32)) ||| b.zeroExtend 32) &&& (255#32) = b.zeroExtend 32
  dsimp only [Word] at *
  simp only [BitVec.and_or_distrib_right, BitVec.and_assoc]
  simp only [show (4294967040#32) &&& (255#32) = (0#32) from by decide,BitVec.and_zero,BitVec.zero_or]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and,BitVec.toNat_setWidth,BitVec.toNat_ofNat]
  change (b.toNat % 4294967296) &&& (2^8-1) = b.toNat % 4294967296
  rw [Nat.and_two_pow_sub_one_eq_mod]
  have := b.isLt
  omega

@[simp] theorem write_overwrite (rs : Registers) (r : Reg) (v w : Word) :
    write (write rs r v) r w=write rs r w := by
  funext q; by_cases h : q=r <;> simp [write,h]

def axisValue (s : X86Memory.State) (off : Word) (gt : Bool) : Word :=
  bit (if gt then decide (0<(load32 s.memory (s.regs 1+off)).toInt)
       else decide ((load32 s.memory (s.regs 1+off)).toInt<0))
def axisEnd (s : X86Memory.State) (off : Word) (gt : Bool) (pc : Nat) : X86Control.State :=
  ⟨put s 0 (axisValue s off gt),some (logical32 (axisValue s off gt)),pc+12⟩
theorem vle_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 3 ⟨s,f,0x2c022⟩ (axisEnd s 12 true 0x2c022) := by
  have path : X86Routine.Prefix listed [] 3 ⟨s,f,0x2c022⟩ (axisEnd s 12 true 0x2c022) := by
    apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (load32 s.memory (s.regs 1+12)) 0),0x2c026⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.Address.eval])
    apply X86Routine.Prefix.step (middle := ⟨putByte s 0 (if 0<(load32 s.memory (s.regs 1+12)).toInt then 1 else 0),some (compare32 (load32 s.memory (s.regs 1+12)) 0),0x2c029⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,cmp32_signed_le,PlayerArmor.cmp_lt,PlayerHeight.cmp_ge_prop] <;> split <;> split <;> (try simp_all) <;> omega)
    apply X86Routine.Prefix.step (middle := axisEnd s 12 true 0x2c022) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,axisEnd,axisValue,bit,putByte,byteReg,put,write,eax,mask_byte] <;> split <;> simp_all [write_overwrite])
    exact .nil _
  exact path.transfer program [] decoded (by simp)
theorem vgt_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 3 ⟨s,f,0x2c033⟩ (axisEnd s 12 false 0x2c033) := by
  have path : X86Routine.Prefix listed [] 3 ⟨s,f,0x2c033⟩ (axisEnd s 12 false 0x2c033) := by
    apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (load32 s.memory (s.regs 1+12)) 0),0x2c037⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.Address.eval])
    apply X86Routine.Prefix.step (middle := ⟨putByte s 0 (if (load32 s.memory (s.regs 1+12)).toInt<0 then 1 else 0),some (compare32 (load32 s.memory (s.regs 1+12)) 0),0x2c03a⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,cmp32_signed_le,PlayerArmor.cmp_lt,PlayerHeight.cmp_ge_prop] <;> split <;> split <;> (try simp_all) <;> omega)
    apply X86Routine.Prefix.step (middle := axisEnd s 12 false 0x2c033) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,axisEnd,axisValue,bit,putByte,byteReg,put,write,eax,mask_byte] <;> split <;> simp_all [write_overwrite])
    exact .nil _
  exact path.transfer program [] decoded (by simp)
theorem hle_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 3 ⟨s,f,0x2c051⟩ (axisEnd s 8 false 0x2c051) := by
  have path : X86Routine.Prefix listed [] 3 ⟨s,f,0x2c051⟩ (axisEnd s 8 false 0x2c051) := by
    apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (load32 s.memory (s.regs 1+8)) 0),0x2c055⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.Address.eval])
    apply X86Routine.Prefix.step (middle := ⟨putByte s 0 (if (load32 s.memory (s.regs 1+8)).toInt<0 then 1 else 0),some (compare32 (load32 s.memory (s.regs 1+8)) 0),0x2c058⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,cmp32_signed_le,PlayerArmor.cmp_lt,PlayerHeight.cmp_ge_prop] <;> split <;> split <;> (try simp_all) <;> omega)
    apply X86Routine.Prefix.step (middle := axisEnd s 8 false 0x2c051) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,axisEnd,axisValue,bit,putByte,byteReg,put,write,eax,mask_byte] <;> split <;> simp_all [write_overwrite])
    exact .nil _
  exact path.transfer program [] decoded (by simp)
theorem hgt_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 3 ⟨s,f,0x2c062⟩ (axisEnd s 8 true 0x2c062) := by
  have path : X86Routine.Prefix listed [] 3 ⟨s,f,0x2c062⟩ (axisEnd s 8 true 0x2c062) := by
    apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (load32 s.memory (s.regs 1+8)) 0),0x2c066⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.Address.eval])
    apply X86Routine.Prefix.step (middle := ⟨putByte s 0 (if 0<(load32 s.memory (s.regs 1+8)).toInt then 1 else 0),some (compare32 (load32 s.memory (s.regs 1+8)) 0),0x2c069⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,cmp32_signed_le,PlayerArmor.cmp_lt,PlayerHeight.cmp_ge_prop] <;> split <;> split <;> (try simp_all) <;> omega)
    apply X86Routine.Prefix.step (middle := axisEnd s 8 true 0x2c062) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,axisEnd,axisValue,bit,putByte,byteReg,put,write,eax,mask_byte] <;> split <;> simp_all [write_overwrite])
    exact .nil _
  exact path.transfer program [] decoded (by simp)

def compared (s : X86Memory.State) : X86Control.State :=
  if (s.regs 0).toInt<(s.regs 7).toInt then
    ⟨put s 0 0,some (logical32 0),0x2c0a4⟩
  else ⟨put s 0 1,some (compare32 (s.regs 0) (s.regs 7)),0x2c0ae⟩
theorem compare_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 3 ⟨s,f,0x2c09e⟩ (compared s) := by
  have path : X86Routine.Prefix listed [] 3 ⟨s,f,0x2c09e⟩ (compared s) := by
    apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (s.regs 0) (s.regs 7)),0x2c0a0⟩) (by simp) (by rfl) (by rfl)
    by_cases h : (s.regs 0).toInt<(s.regs 7).toInt
    · apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (s.regs 0) (s.regs 7)),0x2c0a2⟩) (by simp) (by rfl) (by simp [X86Routine.execute,PlayerHeight.cmp_ge,PlayerHeight.cmp_ge_prop,show ¬(s.regs 7).toInt≤(s.regs 0).toInt by omega])
      apply X86Routine.Prefix.step (middle := compared s) (by simp) (by rfl) (by simp [X86Routine.execute,compared,h,logical32])
      exact .nil _
    · apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (s.regs 0) (s.regs 7)),0x2c0a9⟩) (by simp) (by rfl) (by simp [X86Routine.execute,PlayerHeight.cmp_ge,PlayerHeight.cmp_ge_prop,show (s.regs 7).toInt≤(s.regs 0).toInt by omega])
      apply X86Routine.Prefix.step (middle := compared s) (by simp) (by rfl) (by simp [X86Routine.execute,compared,h,logical32])
      exact .nil _
  exact path.transfer program [] decoded (by simp)


def vertical (s : X86Memory.State) := put s 2 (vertex s)
def horizontal (s : X86Memory.State) := put s 0 (vertex s)
def body (s : X86Memory.State) : X86Control.State :=
  if dx s=0 then
    if (s.regs 0).toInt≤(vx s).toInt then
      finish (axisEnd (vertical s) 12 true 0x2c022).core (axisEnd (vertical s) 12 true 0x2c022).flags
    else finish (axisEnd (vertical s) 12 false 0x2c033).core (axisEnd (vertical s) 12 false 0x2c033).flags
  else if dy s=0 then
    if (s.regs 2).toInt≤(vy s).toInt then
      finish (axisEnd (horizontal s) 8 false 0x2c051).core (axisEnd (horizontal s) 8 false 0x2c051).flags
    else finish (axisEnd (horizontal s) 8 true 0x2c062).core (axisEnd (horizontal s) 8 true 0x2c062).flags
  else finish (compared (diagonal s)).core (compared (diagonal s)).flags

@[simp] theorem compare_zero (w : Word) : (compare32 w (0#32)).zero=(w==0) := by simp [compare32]
theorem body_execution (s : X86Memory.State) (f : Option Flags) (same : s.regs 3=s.regs 1) :
    ∃ n, n≤29 ∧ X86Routine.Prefix program [] n ⟨s,f,0x2c016⟩ (body s) := by
  by_cases hx : dx s=0
  · by_cases hv : (s.regs 0).toInt≤(vx s).toInt
    · let t := axisEnd (vertical s) 12 true 0x2c022
      have head : X86Routine.Prefix listed [] 5 ⟨s,f,0x2c016⟩ ⟨vertical s,some (compare32 (s.regs 0) (vx s)),0x2c022⟩ := by
        apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (dx s) 0),0x2c01a⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,blockPreservesFlags,cmp32_signed_le,PlayerHeight.cmp_ge,compare_zero,vertical,horizontal,vertex,vx,vy,dx,dy,put,write,hx,hv,same])
        apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (dx s) 0),0x2c01c⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,blockPreservesFlags,cmp32_signed_le,PlayerHeight.cmp_ge,compare_zero,vertical,horizontal,vertex,vx,vy,dx,dy,put,write,hx,hv,same])
        apply X86Routine.Prefix.step (middle := ⟨vertical s,some (compare32 (dx s) 0),0x2c01e⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,blockPreservesFlags,cmp32_signed_le,PlayerHeight.cmp_ge,compare_zero,vertical,horizontal,vertex,vx,vy,dx,dy,put,write,hx,hv,same])
        apply X86Routine.Prefix.step (middle := ⟨vertical s,some (compare32 (s.regs 0) (vx s)),0x2c020⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,blockPreservesFlags,cmp32_signed_le,PlayerHeight.cmp_ge,compare_zero,vertical,horizontal,vertex,vx,vy,dx,dy,put,write,hx,hv,same])
        apply X86Routine.Prefix.step (middle := ⟨vertical s,some (compare32 (s.regs 0) (vx s)),0x2c022⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,blockPreservesFlags,cmp32_signed_le,PlayerHeight.cmp_ge,compare_zero,vertical,horizontal,vertex,vx,vy,dx,dy,put,write,hx,hv,same])
        exact .nil _
      have head := head.transfer program [] decoded (by simp)
      have tail := vle_execution (vertical s) (some (compare32 (s.regs 0) (vx s)))
      have done := finish_execution t.core t.flags t.pc (by simp [t,axisEnd])
      refine ⟨13,by omega,?_⟩
      simpa only [body,if_pos hx,if_pos hv] using OriginalGroupBounds.prefix_join (OriginalGroupBounds.prefix_join head tail) done
    · let t := axisEnd (vertical s) 12 false 0x2c033
      have head : X86Routine.Prefix listed [] 5 ⟨s,f,0x2c016⟩ ⟨vertical s,some (compare32 (s.regs 0) (vx s)),0x2c033⟩ := by
        apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (dx s) 0),0x2c01a⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,blockPreservesFlags,cmp32_signed_le,PlayerHeight.cmp_ge,compare_zero,vertical,horizontal,vertex,vx,vy,dx,dy,put,write,hx,hv,same])
        apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (dx s) 0),0x2c01c⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,blockPreservesFlags,cmp32_signed_le,PlayerHeight.cmp_ge,compare_zero,vertical,horizontal,vertex,vx,vy,dx,dy,put,write,hx,hv,same])
        apply X86Routine.Prefix.step (middle := ⟨vertical s,some (compare32 (dx s) 0),0x2c01e⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,blockPreservesFlags,cmp32_signed_le,PlayerHeight.cmp_ge,compare_zero,vertical,horizontal,vertex,vx,vy,dx,dy,put,write,hx,hv,same])
        apply X86Routine.Prefix.step (middle := ⟨vertical s,some (compare32 (s.regs 0) (vx s)),0x2c020⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,blockPreservesFlags,cmp32_signed_le,PlayerHeight.cmp_ge,compare_zero,vertical,horizontal,vertex,vx,vy,dx,dy,put,write,hx,hv,same])
        apply X86Routine.Prefix.step (middle := ⟨vertical s,some (compare32 (s.regs 0) (vx s)),0x2c033⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,blockPreservesFlags,cmp32_signed_le,PlayerHeight.cmp_ge,compare_zero,vertical,horizontal,vertex,vx,vy,dx,dy,put,write,hx,hv,same])
        exact .nil _
      have head := head.transfer program [] decoded (by simp)
      have tail := vgt_execution (vertical s) (some (compare32 (s.regs 0) (vx s)))
      have done := finish_execution t.core t.flags t.pc (by simp [t,axisEnd])
      refine ⟨13,by omega,?_⟩
      simpa only [body,if_pos hx,if_neg hv] using OriginalGroupBounds.prefix_join (OriginalGroupBounds.prefix_join head tail) done
  · by_cases hy : dy s=0
    · by_cases hv : (s.regs 2).toInt≤(vy s).toInt
      · let t := axisEnd (horizontal s) 8 false 0x2c051
        have head : X86Routine.Prefix listed [] 7 ⟨s,f,0x2c016⟩ ⟨horizontal s,some (compare32 (s.regs 2) (vy s)),0x2c051⟩ := by
          apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (dx s) 0),0x2c01a⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,blockPreservesFlags,cmp32_signed_le,PlayerHeight.cmp_ge,compare_zero,vertical,horizontal,vertex,vx,vy,dx,dy,put,write,hx,hy,hv,same])
          apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (dx s) 0),0x2c044⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,blockPreservesFlags,cmp32_signed_le,PlayerHeight.cmp_ge,compare_zero,vertical,horizontal,vertex,vx,vy,dx,dy,put,write,hx,hy,hv,same])
          apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (dy s) 0),0x2c048⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,blockPreservesFlags,cmp32_signed_le,PlayerHeight.cmp_ge,compare_zero,vertical,horizontal,vertex,vx,vy,dx,dy,put,write,hx,hy,hv,same])
          apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (dy s) 0),0x2c04a⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,blockPreservesFlags,cmp32_signed_le,PlayerHeight.cmp_ge,compare_zero,vertical,horizontal,vertex,vx,vy,dx,dy,put,write,hx,hy,hv,same])
          apply X86Routine.Prefix.step (middle := ⟨horizontal s,some (compare32 (dy s) 0),0x2c04c⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,blockPreservesFlags,cmp32_signed_le,PlayerHeight.cmp_ge,compare_zero,vertical,horizontal,vertex,vx,vy,dx,dy,put,write,hx,hy,hv,same])
          apply X86Routine.Prefix.step (middle := ⟨horizontal s,some (compare32 (s.regs 2) (vy s)),0x2c04f⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,blockPreservesFlags,cmp32_signed_le,PlayerHeight.cmp_ge,compare_zero,vertical,horizontal,vertex,vx,vy,dx,dy,put,write,hx,hy,hv,same])
          apply X86Routine.Prefix.step (middle := ⟨horizontal s,some (compare32 (s.regs 2) (vy s)),0x2c051⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,blockPreservesFlags,cmp32_signed_le,PlayerHeight.cmp_ge,compare_zero,vertical,horizontal,vertex,vx,vy,dx,dy,put,write,hx,hy,hv,same])
          exact .nil _
        have head := head.transfer program [] decoded (by simp)
        have tail := hle_execution (horizontal s) (some (compare32 (s.regs 2) (vy s)))
        have done := finish_execution t.core t.flags t.pc (by simp [t,axisEnd])
        refine ⟨15,by omega,?_⟩
        simpa only [body,if_neg hx,if_pos hy,if_pos hv] using OriginalGroupBounds.prefix_join (OriginalGroupBounds.prefix_join head tail) done
      · let t := axisEnd (horizontal s) 8 true 0x2c062
        have head : X86Routine.Prefix listed [] 7 ⟨s,f,0x2c016⟩ ⟨horizontal s,some (compare32 (s.regs 2) (vy s)),0x2c062⟩ := by
          apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (dx s) 0),0x2c01a⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,blockPreservesFlags,cmp32_signed_le,PlayerHeight.cmp_ge,compare_zero,vertical,horizontal,vertex,vx,vy,dx,dy,put,write,hx,hy,hv,same])
          apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (dx s) 0),0x2c044⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,blockPreservesFlags,cmp32_signed_le,PlayerHeight.cmp_ge,compare_zero,vertical,horizontal,vertex,vx,vy,dx,dy,put,write,hx,hy,hv,same])
          apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (dy s) 0),0x2c048⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,blockPreservesFlags,cmp32_signed_le,PlayerHeight.cmp_ge,compare_zero,vertical,horizontal,vertex,vx,vy,dx,dy,put,write,hx,hy,hv,same])
          apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (dy s) 0),0x2c04a⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,blockPreservesFlags,cmp32_signed_le,PlayerHeight.cmp_ge,compare_zero,vertical,horizontal,vertex,vx,vy,dx,dy,put,write,hx,hy,hv,same])
          apply X86Routine.Prefix.step (middle := ⟨horizontal s,some (compare32 (dy s) 0),0x2c04c⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,blockPreservesFlags,cmp32_signed_le,PlayerHeight.cmp_ge,compare_zero,vertical,horizontal,vertex,vx,vy,dx,dy,put,write,hx,hy,hv,same])
          apply X86Routine.Prefix.step (middle := ⟨horizontal s,some (compare32 (s.regs 2) (vy s)),0x2c04f⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,blockPreservesFlags,cmp32_signed_le,PlayerHeight.cmp_ge,compare_zero,vertical,horizontal,vertex,vx,vy,dx,dy,put,write,hx,hy,hv,same])
          apply X86Routine.Prefix.step (middle := ⟨horizontal s,some (compare32 (s.regs 2) (vy s)),0x2c062⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,blockPreservesFlags,cmp32_signed_le,PlayerHeight.cmp_ge,compare_zero,vertical,horizontal,vertex,vx,vy,dx,dy,put,write,hx,hy,hv,same])
          exact .nil _
        have head := head.transfer program [] decoded (by simp)
        have tail := hgt_execution (horizontal s) (some (compare32 (s.regs 2) (vy s)))
        have done := finish_execution t.core t.flags t.pc (by simp [t,axisEnd])
        refine ⟨15,by omega,?_⟩
        simpa only [body,if_neg hx,if_pos hy,if_neg hv] using OriginalGroupBounds.prefix_join (OriginalGroupBounds.prefix_join head tail) done
    · have head : X86Routine.Prefix listed [] 4 ⟨s,f,0x2c016⟩ ⟨s,some (compare32 (dy s) 0),0x2c073⟩ := by
        apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (dx s) 0),0x2c01a⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,blockPreservesFlags,cmp32_signed_le,PlayerHeight.cmp_ge,compare_zero,vertical,horizontal,vertex,vx,vy,dx,dy,put,write,hx,hy,same])
        apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (dx s) 0),0x2c044⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,blockPreservesFlags,cmp32_signed_le,PlayerHeight.cmp_ge,compare_zero,vertical,horizontal,vertex,vx,vy,dx,dy,put,write,hx,hy,same])
        apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (dy s) 0),0x2c048⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,blockPreservesFlags,cmp32_signed_le,PlayerHeight.cmp_ge,compare_zero,vertical,horizontal,vertex,vx,vy,dx,dy,put,write,hx,hy,same])
        apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (dy s) 0),0x2c073⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,blockPreservesFlags,cmp32_signed_le,PlayerHeight.cmp_ge,compare_zero,vertical,horizontal,vertex,vx,vy,dx,dy,put,write,hx,hy,same])
        exact .nil _
      have head := head.transfer program [] decoded (by simp)
      have arith := diagonal_execution s (some (compare32 (dy s) 0))
      have cmp := compare_execution (diagonal s) none
      have done := finish_execution (compared (diagonal s)).core (compared (diagonal s)).flags
        (compared (diagonal s)).pc (by unfold compared; split <;> simp)
      refine ⟨29,by omega,?_⟩
      simpa only [body,if_neg hx,if_neg hy] using
        OriginalGroupBounds.prefix_join (OriginalGroupBounds.prefix_join (OriginalGroupBounds.prefix_join head arith) cmp) done

def result (s : X86Memory.State) := body (prepare s)
theorem execution (s : X86Memory.State) (f : Option Flags) :
    ∃ n, n≤34 ∧ X86Routine.Prefix program [] n ⟨s,f,0x2c010⟩ (result s) := by
  have first := prepare_execution s f
  have same : (prepare s).regs 3=(prepare s).regs 1 := by
    simp [prepare,prepare1,prepare2,prepare3,prepare4,prepare5,X86Routine.pushWord,put,write]
  obtain ⟨n,hn,rest⟩ := body_execution (prepare s) f same
  exact ⟨5+n,by omega,OriginalGroupBounds.prefix_join first rest⟩

def left (s : X86Memory.State) := mulWord ((dy s).sshiftRight 16) (s.regs 0-vx s)
def right (s : X86Memory.State) := mulWord (s.regs 2-vy s) ((dx s).sshiftRight 16)
@[simp] theorem diagonal_value (s : X86Memory.State) : (diagonal s).regs 0=right s ∧ (diagonal s).regs 7=left s := by
  simp [diagonal,diagonal1,diagonal2,diagonal3,diagonal4,diagonal5,diagonal6,diagonal7,diagonal8,diagonal9,diagonal10,diagonal11,diagonal12,diagonal13,diagonal14,diagonal15,diagonal16,diagonal17,multiply,left,right,dx,dy,vx,vy,vertex,put,write,eax,ebx,edx]
@[simp] theorem diagonal_memory (s : X86Memory.State) : (diagonal s).memory=s.memory := by
  simp [diagonal,diagonal1,diagonal2,diagonal3,diagonal4,diagonal5,diagonal6,diagonal7,diagonal8,diagonal9,diagonal10,diagonal11,diagonal12,diagonal13,diagonal14,diagonal15,diagonal16,diagonal17,multiply,left,right,dx,dy,vx,vy,vertex,put,write,eax,ebx,edx]
@[simp] theorem diagonal_stack (s : X86Memory.State) : (diagonal s).regs 4=s.regs 4 := by
  simp [diagonal,diagonal1,diagonal2,diagonal3,diagonal4,diagonal5,diagonal6,diagonal7,diagonal8,diagonal9,diagonal10,diagonal11,diagonal12,diagonal13,diagonal14,diagonal15,diagonal16,diagonal17,multiply,left,right,dx,dy,vx,vy,vertex,put,write,eax,ebx,edx]
def side (s : X86Memory.State) : Bool :=
  if dx s=0 then
    if (s.regs 0).toInt≤(vx s).toInt then decide (0<(dy s).toInt) else decide ((dy s).toInt<0)
  else if dy s=0 then
    if (s.regs 2).toInt≤(vy s).toInt then decide ((dx s).toInt<0) else decide (0<(dx s).toInt)
  else decide ((left s).toInt≤(right s).toInt)

@[simp] theorem finish_value (s : X86Memory.State) (f : Option Flags) :
    (finish s f).core.regs 0=s.regs 0 := by
  simp [finish,pop1,pop2,pop3,pop4,put,write]
theorem body_value (s : X86Memory.State) : (body s).core.regs 0=bit (side s) := by
  unfold body side
  split <;> (try split) <;> (try split)
  all_goals simp [finish_value,axisEnd,axisValue,vertical,horizontal,dx,dy,put,write]
  unfold compared
  split <;> simp_all [bit,put,write,(diagonal_value s).1,(diagonal_value s).2]

theorem body_frame (s : X86Memory.State) :
    (body s).core.memory=s.memory ∧ (body s).core.regs 4=s.regs 4+20 ∧
    (body s).core.regs 5=load32 s.memory (s.regs 4) ∧
    (body s).core.regs 7=load32 s.memory (s.regs 4+4) ∧
    (body s).core.regs 6=load32 s.memory (s.regs 4+8) ∧
    (body s).core.regs 1=load32 s.memory (s.regs 4+12) ∧
    (body s).pc=(load32 s.memory (s.regs 4+16)).toNat := by
  unfold body
  split <;> (try split) <;> (try split)
  all_goals try (simp [axisEnd,vertical,horizontal,finish,pop1,pop2,pop3,pop4,put,write])
  unfold compared
  split <;> simp [finish,pop1,pop2,pop3,pop4,put,write]

def saved (s : X86Memory.State) : Memory :=
  store32 (store32 (store32 (store32 s.memory (s.regs 4-(4#32)) (s.regs 1))
    (s.regs 4-(8#32)) (s.regs 6)) (s.regs 4-(12#32)) (s.regs 7)) (s.regs 4-(16#32)) (s.regs 5)
theorem prepared_memory (s : X86Memory.State) : (prepare s).memory=saved s := by
  simp [prepare,prepare1,prepare2,prepare3,prepare4,prepare5,X86Routine.pushWord,put,write,saved,BitVec.sub_eq_add_neg,BitVec.add_assoc]
theorem prepared_regs (s : X86Memory.State) :
    (prepare s).regs 0=s.regs 0 ∧ (prepare s).regs 2=s.regs 2 ∧
    (prepare s).regs 1=s.regs 3 ∧ (prepare s).regs 4=s.regs 4-(16#32) := by
  simp [prepare,prepare1,prepare2,prepare3,prepare4,prepare5,X86Routine.pushWord,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc]
theorem frame (s : X86Memory.State) (a : Word)
    (safe : ∀ off∈[(4#32),8,12,16], Apart a (s.regs 4-off)) :
    load32 (result s).core.memory a=load32 s.memory a := by
  unfold result
  rw [(body_frame (prepare s)).1,prepared_memory]
  unfold saved
  repeat rw [load_store_apart _ _ _ _ (safe _ (by simp))]
theorem prepare_frame (s : X86Memory.State) (a : Word)
    (safe : ∀ off∈[(4#32),8,12,16], Apart a (s.regs 4-off)) :
    load32 (prepare s).memory a=load32 s.memory a := by
  rw [←(body_frame (prepare s)).1]
  exact frame s a safe

theorem slots_apart (sp a b : Word) (h : Apart (-a) (-b)) : Apart (sp-a) (sp-b) := by
  simpa only [BitVec.sub_eq_add_neg] using OriginalPathXStep.apart_translate sp (-a) (-b) h
theorem saved_0 (s : X86Memory.State) : load32 (saved s) (s.regs 4-(0#32))=load32 s.memory (s.regs 4) := by
  unfold saved
  rw [load_store_apart _ _ _ _ (slots_apart (s.regs 4) (0#32) (16#32) (by unfold Apart; decide))]
  rw [load_store_apart _ _ _ _ (slots_apart (s.regs 4) (0#32) (12#32) (by unfold Apart; decide))]
  rw [load_store_apart _ _ _ _ (slots_apart (s.regs 4) (0#32) (8#32) (by unfold Apart; decide))]
  rw [load_store_apart _ _ _ _ (slots_apart (s.regs 4) (0#32) (4#32) (by unfold Apart; decide))]
  simp
theorem saved_4 (s : X86Memory.State) : load32 (saved s) (s.regs 4-(4#32))=s.regs 1 := by
  unfold saved
  rw [load_store_apart _ _ _ _ (slots_apart (s.regs 4) (4#32) (16#32) (by unfold Apart; decide))]
  rw [load_store_apart _ _ _ _ (slots_apart (s.regs 4) (4#32) (12#32) (by unfold Apart; decide))]
  rw [load_store_apart _ _ _ _ (slots_apart (s.regs 4) (4#32) (8#32) (by unfold Apart; decide))]
  rw [load_store]
theorem saved_8 (s : X86Memory.State) : load32 (saved s) (s.regs 4-(8#32))=s.regs 6 := by
  unfold saved
  rw [load_store_apart _ _ _ _ (slots_apart (s.regs 4) (8#32) (16#32) (by unfold Apart; decide))]
  rw [load_store_apart _ _ _ _ (slots_apart (s.regs 4) (8#32) (12#32) (by unfold Apart; decide))]
  rw [load_store]
theorem saved_12 (s : X86Memory.State) : load32 (saved s) (s.regs 4-(12#32))=s.regs 7 := by
  unfold saved
  rw [load_store_apart _ _ _ _ (slots_apart (s.regs 4) (12#32) (16#32) (by unfold Apart; decide))]
  rw [load_store]
theorem saved_16 (s : X86Memory.State) : load32 (saved s) (s.regs 4-(16#32))=s.regs 5 := by
  unfold saved
  rw [load_store]
theorem returned (s : X86Memory.State) :
    (result s).core.regs 4=s.regs 4+4 ∧ (result s).core.regs 1=s.regs 1 ∧
    (result s).core.regs 6=s.regs 6 ∧ (result s).core.regs 7=s.regs 7 ∧
    (result s).core.regs 5=s.regs 5 ∧ (result s).pc=(load32 s.memory (s.regs 4)).toNat := by
  have h := body_frame (prepare s)
  rw [prepared_memory,(prepared_regs s).2.2.2] at h
  have a4 : s.regs 4-(16#32)+(4#32)=s.regs 4-(12#32) := by simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  have a8 : s.regs 4-(16#32)+(8#32)=s.regs 4-(8#32) := by simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  have a12 : s.regs 4-(16#32)+(12#32)=s.regs 4-(4#32) := by simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  have a16 : s.regs 4-(16#32)+(16#32)=s.regs 4-(0#32) := by simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  have a20 : s.regs 4-(16#32)+(20#32)=s.regs 4+(4#32) := by simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  change _ ∧ (body (prepare s)).core.regs 4=s.regs 4-(16#32)+(20#32) ∧
    (body (prepare s)).core.regs 5=load32 (saved s) (s.regs 4-(16#32)) ∧
    (body (prepare s)).core.regs 7=load32 (saved s) (s.regs 4-(16#32)+(4#32)) ∧
    (body (prepare s)).core.regs 6=load32 (saved s) (s.regs 4-(16#32)+(8#32)) ∧
    (body (prepare s)).core.regs 1=load32 (saved s) (s.regs 4-(16#32)+(12#32)) ∧
    (body (prepare s)).pc=(load32 (saved s) (s.regs 4-(16#32)+(16#32))).toNat at h
  rw [a4,a8,a12,a16,a20,saved_0,saved_4,saved_8,saved_12,saved_16] at h
  exact ⟨h.2.1,h.2.2.2.2.2.1,h.2.2.2.2.1,h.2.2.2.1,h.2.2.1,h.2.2.2.2.2.2⟩

structure Inputs (s : X86Memory.State) (line : Collision.Line) (x y : Fixed)
    (linePtr vertexPtr : Word) : Prop where
  pointX : s.regs 0=x.raw.toBitVec
  pointY : s.regs 2=y.raw.toBitVec
  pointer : s.regs 3=linePtr
  vertex : load32 s.memory linePtr=vertexPtr
  vertexX : load32 s.memory vertexPtr=line.x.raw.toBitVec
  vertexY : load32 s.memory (vertexPtr+4)=line.y.raw.toBitVec
  deltaX : load32 s.memory (linePtr+8)=line.dx.raw.toBitVec
  deltaY : load32 s.memory (linePtr+12)=line.dy.raw.toBitVec
  safe : ∀ a∈[linePtr,vertexPtr,vertexPtr+4,linePtr+8,linePtr+12],
    ∀ off∈[(4#32),8,12,16], Apart a (s.regs 4-off)

theorem live (s : X86Memory.State) (line : Collision.Line) (x y : Fixed)
    (linePtr vertexPtr : Word) (h : Inputs s line x y linePtr vertexPtr) :
    (result s).core.regs 0=bit (line.pointSide x y) := by
  have keep (a : Word) (ha : a∈[linePtr,vertexPtr,vertexPtr+4,linePtr+8,linePtr+12]) := prepare_frame s a (h.safe a ha)
  have r := prepared_regs s
  have ptr := r.2.2.1.trans h.pointer
  have v : vertex (prepare s)=vertexPtr := by
    unfold vertex
    rw [ptr,keep _ (by simp),h.vertex]
  have vx' : vx (prepare s)=line.x.raw.toBitVec := by
    unfold vx; rw [v,keep _ (by simp),h.vertexX]
  have vy' : vy (prepare s)=line.y.raw.toBitVec := by
    unfold vy; rw [v,keep _ (by simp),h.vertexY]
  have dx' : dx (prepare s)=line.dx.raw.toBitVec := by
    unfold dx; rw [ptr,keep _ (by simp),h.deltaX]
  have dy' : dy (prepare s)=line.dy.raw.toBitVec := by
    unfold dy; rw [ptr,keep _ (by simp),h.deltaY]
  unfold result
  rw [body_value]
  unfold side left right
  rw [vx',vy',dx',dy',r.1,r.2.1,h.pointX,h.pointY]
  congr 1
  simp [Collision.Line.pointSide,mulWord,Fixed.sub,Int32.le_iff_toInt_le,Int32.lt_iff_toInt_lt,
    Int32.toInt_toBitVec,Int32.toBitVec_inj,Int32.toBitVec_ofBitVec]
  have zero (a : Int32) : a.toBitVec=(0#32) ↔ a=0 := by
    change a.toBitVec=(0 : Int32).toBitVec ↔ a=0
    exact Int32.toBitVec_inj
  simp only [zero]
  rfl

end Doom.Proofs.OriginalLineSide
