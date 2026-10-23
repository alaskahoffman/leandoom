import Doom.Proofs.OriginalLineSide
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalDivlineSide
open Verification X86 X86Memory X86Control BlockSummary
def code : List UInt8 := [0x51,0x56,0x57,0x55,0x89,0xc6,0x89,0xd9,0x89,0xd0,0x83,0x7b,0x8,0x0,0x75,0x26,0x3b,0x33,0x7f,0x11,0x83,0x79,0xc,0x0,0xf,0x9f,0xc0,0x25,0xff,0x0,0x0,0x0,0x5d,0x5f,0x5e,0x59,0xc3,0x83,0x79,0xc,0x0,0xf,0x9c,0xc0,0x25,0xff,0x0,0x0,0x0,0x5d,0x5f,0x5e,0x59,0xc3,0x83,0x7b,0xc,0x0,0x75,0x27,0x3b,0x41,0x4,0x7f,0x11,0x83,0x79,0x8,0x0,0xf,0x9c,0xc0,0x25,0xff,0x0,0x0,0x0,0x5d,0x5f,0x5e,0x59,0xc3,0x83,0x79,0x8,0x0,0xf,0x9f,0xc0,0x25,0xff,0x0,0x0,0x0,0x5d,0x5f,0x5e,0x59,0xc3,0x89,0xf3,0x8b,0x39,0x8b,0x51,0x8,0x29,0xfb,0x89,0xc7,0x8b,0x41,0xc,0x8b,0x69,0x4,0x31,0xd0,0x29,0xef,0x31,0xd8,0x31,0xf8,0xa9,0x0,0x0,0x0,0x80,0x74,0xd,0x33,0x59,0xc,0xf7,0xc3,0x0,0x0,0x0,0x80,0x74,0x28,0xeb,0x2d,0x8b,0x41,0xc,0xc1,0xfb,0x8,0xc1,0xf8,0x8,0xf7,0xeb,0xf,0xac,0xd0,0x10,0x89,0xc6,0x8b,0x59,0x8,0x89,0xf8,0xc1,0xfb,0x8,0xc1,0xf8,0x8,0xf7,0xeb,0xf,0xac,0xd0,0x10,0x39,0xf0,0x7d,0x7,0x31,0xc0,0x5d,0x5f,0x5e,0x59,0xc3,0xb8,0x1,0x0,0x0,0x0,0x5d,0x5f,0x5e,0x59,0xc3]
def bytesProgram (bytes : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2c1e0≤pc ∧ pc<0x2c2a7 then X86Routine.decodeAt bytes (pc-0x2c1e0) else none
def program := bytesProgram code
def listed : X86Routine.Program
  | 0x2c1e0 => some (.push 1,1)
  | 0x2c1e1 => some (.push 6,1)
  | 0x2c1e2 => some (.push 7,1)
  | 0x2c1e3 => some (.push 5,1)
  | 0x2c1e4 => some (.control (.block (.legacy (.mov 6 0))),2)
  | 0x2c1e6 => some (.control (.block (.legacy (.mov 1 3))),2)
  | 0x2c1e8 => some (.control (.block (.legacy (.mov 0 2))),2)
  | 0x2c1ea => some (.control (.cmpImmediate ⟨some 3,none,0,8⟩ 0),4)
  | 0x2c1ee => some (.control (.jumpZero false 38),2)
  | 0x2c1f0 => some (.control (.cmpMemory 6 ⟨some 3,none,0,0⟩),2)
  | 0x2c1f2 => some (.jumpSigned 2 17,2)
  | 0x2c1f4 => some (.control (.cmpImmediate ⟨some 1,none,0,12⟩ 0),4)
  | 0x2c1f8 => some (.setGreater 0,3)
  | 0x2c1fb => some (.control (.andEax 255),5)
  | 0x2c200 => some (.pop 5,1)
  | 0x2c201 => some (.pop 7,1)
  | 0x2c202 => some (.pop 6,1)
  | 0x2c203 => some (.pop 1,1)
  | 0x2c204 => some (.ret,1)
  | 0x2c205 => some (.control (.cmpImmediate ⟨some 1,none,0,12⟩ 0),4)
  | 0x2c209 => some (.setLess 0,3)
  | 0x2c20c => some (.control (.andEax 255),5)
  | 0x2c211 => some (.pop 5,1)
  | 0x2c212 => some (.pop 7,1)
  | 0x2c213 => some (.pop 6,1)
  | 0x2c214 => some (.pop 1,1)
  | 0x2c215 => some (.ret,1)
  | 0x2c216 => some (.control (.cmpImmediate ⟨some 3,none,0,12⟩ 0),4)
  | 0x2c21a => some (.control (.jumpZero false 39),2)
  | 0x2c21c => some (.control (.cmpMemory 0 ⟨some 1,none,0,4⟩),3)
  | 0x2c21f => some (.jumpSigned 2 17,2)
  | 0x2c221 => some (.control (.cmpImmediate ⟨some 1,none,0,8⟩ 0),4)
  | 0x2c225 => some (.setLess 0,3)
  | 0x2c228 => some (.control (.andEax 255),5)
  | 0x2c22d => some (.pop 5,1)
  | 0x2c22e => some (.pop 7,1)
  | 0x2c22f => some (.pop 6,1)
  | 0x2c230 => some (.pop 1,1)
  | 0x2c231 => some (.ret,1)
  | 0x2c232 => some (.control (.cmpImmediate ⟨some 1,none,0,8⟩ 0),4)
  | 0x2c236 => some (.setGreater 0,3)
  | 0x2c239 => some (.control (.andEax 255),5)
  | 0x2c23e => some (.pop 5,1)
  | 0x2c23f => some (.pop 7,1)
  | 0x2c240 => some (.pop 6,1)
  | 0x2c241 => some (.pop 1,1)
  | 0x2c242 => some (.ret,1)
  | 0x2c243 => some (.control (.block (.legacy (.mov 3 6))),2)
  | 0x2c245 => some (.control (.block (.legacy (.load 7 1 0))),2)
  | 0x2c247 => some (.control (.block (.legacy (.load 2 1 8))),3)
  | 0x2c24a => some (.control (.block (.arithmetic (.sub 3 7))),2)
  | 0x2c24c => some (.control (.block (.legacy (.mov 7 0))),2)
  | 0x2c24e => some (.control (.block (.legacy (.load 0 1 12))),3)
  | 0x2c251 => some (.control (.block (.legacy (.load 5 1 4))),3)
  | 0x2c254 => some (.xorRegister 0 2,2)
  | 0x2c256 => some (.control (.block (.arithmetic (.sub 7 5))),2)
  | 0x2c258 => some (.xorRegister 0 3,2)
  | 0x2c25a => some (.xorRegister 0 7,2)
  | 0x2c25c => some (.testRegisterImmediate 0 2147483648,5)
  | 0x2c261 => some (.control (.jumpZero true 13),2)
  | 0x2c263 => some (.xorMemory 3 ⟨some 1,none,0,12⟩,3)
  | 0x2c266 => some (.testRegisterImmediate 3 2147483648,6)
  | 0x2c26c => some (.control (.jumpZero true 40),2)
  | 0x2c26e => some (.jump 45,2)
  | 0x2c270 => some (.control (.block (.legacy (.load 0 1 12))),3)
  | 0x2c273 => some (.sar 3 8,3)
  | 0x2c276 => some (.sar 0 8,3)
  | 0x2c279 => some (.control (.block (.arithmetic (.imul 3))),2)
  | 0x2c27b => some (.control (.block (.arithmetic (.shrd 0 2 16))),4)
  | 0x2c27f => some (.control (.block (.legacy (.mov 6 0))),2)
  | 0x2c281 => some (.control (.block (.legacy (.load 3 1 8))),3)
  | 0x2c284 => some (.control (.block (.legacy (.mov 0 7))),2)
  | 0x2c286 => some (.sar 3 8,3)
  | 0x2c289 => some (.sar 0 8,3)
  | 0x2c28c => some (.control (.block (.arithmetic (.imul 3))),2)
  | 0x2c28e => some (.control (.block (.arithmetic (.shrd 0 2 16))),4)
  | 0x2c292 => some (.compareRegisters 0 6,2)
  | 0x2c294 => some (.jumpSigned 0 7,2)
  | 0x2c296 => some (.xorRegister 0 0,2)
  | 0x2c298 => some (.pop 5,1)
  | 0x2c299 => some (.pop 7,1)
  | 0x2c29a => some (.pop 6,1)
  | 0x2c29b => some (.pop 1,1)
  | 0x2c29c => some (.ret,1)
  | 0x2c29d => some (.immediate 0 1,5)
  | 0x2c2a2 => some (.pop 5,1)
  | 0x2c2a3 => some (.pop 7,1)
  | 0x2c2a4 => some (.pop 6,1)
  | 0x2c2a5 => some (.pop 1,1)
  | 0x2c2a6 => some (.ret,1)
  | _ => none
theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def prepare1 (s : X86Memory.State) := X86Routine.pushWord (s) ((s).regs 1)
def prepare2 (s : X86Memory.State) := X86Routine.pushWord (prepare1 s) ((prepare1 s).regs 6)
def prepare3 (s : X86Memory.State) := X86Routine.pushWord (prepare2 s) ((prepare2 s).regs 7)
def prepare4 (s : X86Memory.State) := X86Routine.pushWord (prepare3 s) ((prepare3 s).regs 5)
def prepare5 (s : X86Memory.State) := put (prepare4 s) 6 ((prepare4 s).regs 0)
def prepare6 (s : X86Memory.State) := put (prepare5 s) 1 ((prepare5 s).regs 3)
def prepare7 (s : X86Memory.State) := put (prepare6 s) 0 ((prepare6 s).regs 2)
def prepare := prepare7
theorem prepare_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 7 ⟨s,f,0x2c1e0⟩ ⟨prepare s,f,0x2c1ea⟩ := by
  have path : X86Routine.Prefix listed [] 7 ⟨s,f,0x2c1e0⟩ ⟨prepare s,f,0x2c1ea⟩ := by
    apply X86Routine.Prefix.step (middle := ⟨prepare1 s,f,0x2c1e1⟩) (by simp) (by rfl) (by simp [logical32,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,prepare1,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := ⟨prepare2 s,f,0x2c1e2⟩) (by simp) (by rfl) (by simp [logical32,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,prepare1,prepare2,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := ⟨prepare3 s,f,0x2c1e3⟩) (by simp) (by rfl) (by simp [logical32,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,prepare1,prepare2,prepare3,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := ⟨prepare4 s,f,0x2c1e4⟩) (by simp) (by rfl) (by simp [logical32,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,prepare1,prepare2,prepare3,prepare4,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := ⟨prepare5 s,f,0x2c1e6⟩) (by simp) (by rfl) (by simp [logical32,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,prepare1,prepare2,prepare3,prepare4,prepare5,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := ⟨prepare6 s,f,0x2c1e8⟩) (by simp) (by rfl) (by simp [logical32,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,prepare1,prepare2,prepare3,prepare4,prepare5,prepare6,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := ⟨prepare7 s,f,0x2c1ea⟩) (by simp) (by rfl) (by simp [logical32,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,prepare1,prepare2,prepare3,prepare4,prepare5,prepare6,prepare7,X86Routine.pushWord])
    exact .nil _
  exact path.transfer program [] decoded (by simp)

def delta1 (s : X86Memory.State) := put (s) 3 ((s).regs 6)
def delta2 (s : X86Memory.State) := put (delta1 s) 7 (load32 (delta1 s).memory ((delta1 s).regs 1+0))
def delta3 (s : X86Memory.State) := put (delta2 s) 2 (load32 (delta2 s).memory ((delta2 s).regs 1+8))
def delta4 (s : X86Memory.State) := put (delta3 s) 3 ((delta3 s).regs 3-(delta3 s).regs 7)
def delta5 (s : X86Memory.State) := put (delta4 s) 7 ((delta4 s).regs 0)
def delta6 (s : X86Memory.State) := put (delta5 s) 0 (load32 (delta5 s).memory ((delta5 s).regs 1+12))
def delta7 (s : X86Memory.State) := put (delta6 s) 5 (load32 (delta6 s).memory ((delta6 s).regs 1+4))
def delta8 (s : X86Memory.State) := put (delta7 s) 0 ((delta7 s).regs 0 ^^^ (delta7 s).regs 2)
def delta9 (s : X86Memory.State) := put (delta8 s) 7 ((delta8 s).regs 7-(delta8 s).regs 5)
def delta10 (s : X86Memory.State) := put (delta9 s) 0 ((delta9 s).regs 0 ^^^ (delta9 s).regs 3)
def delta11 (s : X86Memory.State) := put (delta10 s) 0 ((delta10 s).regs 0 ^^^ (delta10 s).regs 7)
def delta12 (s : X86Memory.State) := delta11 s
def delta := delta12
theorem delta_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 12 ⟨s,f,0x2c243⟩ ⟨delta s,some (logical32 ((delta11 s).regs 0 &&& (0x80000000#32))),0x2c261⟩ := by
  have path : X86Routine.Prefix listed [] 12 ⟨s,f,0x2c243⟩ ⟨delta s,some (logical32 ((delta11 s).regs 0 &&& (0x80000000#32))),0x2c261⟩ := by
    apply X86Routine.Prefix.step (middle := ⟨delta1 s,f,0x2c245⟩) (by simp) (by rfl) (by simp [logical32,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,delta1,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := ⟨delta2 s,f,0x2c247⟩) (by simp) (by rfl) (by simp [logical32,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,delta1,delta2,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := ⟨delta3 s,f,0x2c24a⟩) (by simp) (by rfl) (by simp [logical32,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,delta1,delta2,delta3,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := ⟨delta4 s,none,0x2c24c⟩) (by simp) (by rfl) (by simp [logical32,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,delta1,delta2,delta3,delta4,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := ⟨delta5 s,none,0x2c24e⟩) (by simp) (by rfl) (by simp [logical32,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,delta1,delta2,delta3,delta4,delta5,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := ⟨delta6 s,none,0x2c251⟩) (by simp) (by rfl) (by simp [logical32,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,delta1,delta2,delta3,delta4,delta5,delta6,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := ⟨delta7 s,none,0x2c254⟩) (by simp) (by rfl) (by simp [logical32,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,delta1,delta2,delta3,delta4,delta5,delta6,delta7,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := ⟨delta8 s,some (logical32 ((delta8 s).regs 0)),0x2c256⟩) (by simp) (by rfl) (by simp [logical32,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,delta1,delta2,delta3,delta4,delta5,delta6,delta7,delta8,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := ⟨delta9 s,none,0x2c258⟩) (by simp) (by rfl) (by simp [logical32,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,delta1,delta2,delta3,delta4,delta5,delta6,delta7,delta8,delta9,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := ⟨delta10 s,some (logical32 ((delta10 s).regs 0)),0x2c25a⟩) (by simp) (by rfl) (by simp [logical32,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,delta1,delta2,delta3,delta4,delta5,delta6,delta7,delta8,delta9,delta10,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := ⟨delta11 s,some (logical32 ((delta11 s).regs 0)),0x2c25c⟩) (by simp) (by rfl) (by simp [logical32,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,delta1,delta2,delta3,delta4,delta5,delta6,delta7,delta8,delta9,delta10,delta11,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := ⟨delta12 s,some (logical32 ((delta12 s).regs 0 &&& (0x80000000#32))),0x2c261⟩) (by simp) (by rfl) (by simp [logical32,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,delta1,delta2,delta3,delta4,delta5,delta6,delta7,delta8,delta9,delta10,delta11,delta12,X86Routine.pushWord])
    exact .nil _
  exact path.transfer program [] decoded (by simp)

def product1 (s : X86Memory.State) := put (s) 0 (load32 (s).memory ((s).regs 1+12))
def product2 (s : X86Memory.State) := put (product1 s) 3 (((product1 s).regs 3).sshiftRight 8)
def product3 (s : X86Memory.State) := put (product2 s) 0 (((product2 s).regs 0).sshiftRight 8)
def product4 (s : X86Memory.State) := X86Block.execute (.arithmetic (.imul 3)) (product3 s)
def product5 (s : X86Memory.State) := multiply (product3 s)
def product6 (s : X86Memory.State) := put (product5 s) 6 ((product5 s).regs 0)
def product7 (s : X86Memory.State) := put (product6 s) 3 (load32 (product6 s).memory ((product6 s).regs 1+8))
def product8 (s : X86Memory.State) := put (product7 s) 0 ((product7 s).regs 7)
def product9 (s : X86Memory.State) := put (product8 s) 3 (((product8 s).regs 3).sshiftRight 8)
def product10 (s : X86Memory.State) := put (product9 s) 0 (((product9 s).regs 0).sshiftRight 8)
def product11 (s : X86Memory.State) := X86Block.execute (.arithmetic (.imul 3)) (product10 s)
def product12 (s : X86Memory.State) := multiply (product10 s)
def product := product12
theorem product_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 12 ⟨s,f,0x2c270⟩ ⟨product s,none,0x2c292⟩ := by
  have path : X86Routine.Prefix listed [] 12 ⟨s,f,0x2c270⟩ ⟨product s,none,0x2c292⟩ := by
    apply X86Routine.Prefix.step (middle := ⟨product1 s,f,0x2c273⟩) (by simp) (by rfl) (by simp [logical32,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,product1,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := ⟨product2 s,none,0x2c276⟩) (by simp) (by rfl) (by simp [logical32,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,product1,product2,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := ⟨product3 s,none,0x2c279⟩) (by simp) (by rfl) (by simp [logical32,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,product1,product2,product3,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := ⟨product4 s,none,0x2c27b⟩) (by simp) (by rfl) (by simp [logical32,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,product1,product2,product3,product4,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := ⟨product5 s,none,0x2c27f⟩) (by simp) (by rfl) (by simpa [X86Routine.execute,X86Control.execute,product5,product4,blockPreservesFlags] using congrArg (fun c => some (X86Control.State.mk c none 0x2c27f)) (multiply_correct (product3 s)))
    apply X86Routine.Prefix.step (middle := ⟨product6 s,none,0x2c281⟩) (by simp) (by rfl) (by simp [logical32,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,product1,product2,product3,product4,product5,product6,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := ⟨product7 s,none,0x2c284⟩) (by simp) (by rfl) (by simp [logical32,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,product1,product2,product3,product4,product5,product6,product7,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := ⟨product8 s,none,0x2c286⟩) (by simp) (by rfl) (by simp [logical32,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,product1,product2,product3,product4,product5,product6,product7,product8,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := ⟨product9 s,none,0x2c289⟩) (by simp) (by rfl) (by simp [logical32,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,product1,product2,product3,product4,product5,product6,product7,product8,product9,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := ⟨product10 s,none,0x2c28c⟩) (by simp) (by rfl) (by simp [logical32,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,product1,product2,product3,product4,product5,product6,product7,product8,product9,product10,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := ⟨product11 s,none,0x2c28e⟩) (by simp) (by rfl) (by simp [logical32,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,product1,product2,product3,product4,product5,product6,product7,product8,product9,product10,product11,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := ⟨product12 s,none,0x2c292⟩) (by simp) (by rfl) (by simpa [X86Routine.execute,X86Control.execute,product12,product11,blockPreservesFlags] using congrArg (fun c => some (X86Control.State.mk c none 0x2c292)) (multiply_correct (product10 s)))
    exact .nil _
  exact path.transfer program [] decoded (by simp)

def bit (b : Bool) : Word := if b then 1 else 0
def pop1 (s : X86Memory.State) := put (put s 4 (s.regs 4+4)) 5 (load32 s.memory (s.regs 4))
def pop2 (s : X86Memory.State) := put (put (pop1 s) 4 (s.regs 4+8)) 7 (load32 s.memory (s.regs 4+4))
def pop3 (s : X86Memory.State) := put (put (pop2 s) 4 (s.regs 4+12)) 6 (load32 s.memory (s.regs 4+8))
def pop4 (s : X86Memory.State) := put (put (pop3 s) 4 (s.regs 4+16)) 1 (load32 s.memory (s.regs 4+12))
def finish (s : X86Memory.State) (f : Option Flags) : X86Control.State :=
  ⟨put (pop4 s) 4 (s.regs 4+20),f,(load32 s.memory (s.regs 4+16)).toNat⟩
theorem finish_execution (s : X86Memory.State) (f : Option Flags) (pc : Nat)
    (atReturn : pc∈[0x2c200,0x2c211,0x2c22d,0x2c23e,0x2c298,0x2c2a2]) :
    X86Routine.Prefix program [] 5 ⟨s,f,pc⟩ (finish s f) := by
  have path : X86Routine.Prefix listed [] 5 ⟨s,f,pc⟩ (finish s f) := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at atReturn
    rcases atReturn with rfl|rfl|rfl|rfl|rfl|rfl
    · apply X86Routine.Prefix.step (middle := ⟨pop1 s,f,0x2c201⟩) (by simp) (by rfl) (by simp [X86Routine.execute,pop1,pop2,pop3,pop4,finish,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle := ⟨pop2 s,f,0x2c202⟩) (by simp) (by rfl) (by simp [X86Routine.execute,pop1,pop2,pop3,pop4,finish,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle := ⟨pop3 s,f,0x2c203⟩) (by simp) (by rfl) (by simp [X86Routine.execute,pop1,pop2,pop3,pop4,finish,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle := ⟨pop4 s,f,0x2c204⟩) (by simp) (by rfl) (by simp [X86Routine.execute,pop1,pop2,pop3,pop4,finish,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle := finish s f) (by simp) (by rfl) (by simp [X86Routine.execute,pop1,pop2,pop3,pop4,finish,put,write,BitVec.add_assoc])
      exact .nil _
    · apply X86Routine.Prefix.step (middle := ⟨pop1 s,f,0x2c212⟩) (by simp) (by rfl) (by simp [X86Routine.execute,pop1,pop2,pop3,pop4,finish,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle := ⟨pop2 s,f,0x2c213⟩) (by simp) (by rfl) (by simp [X86Routine.execute,pop1,pop2,pop3,pop4,finish,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle := ⟨pop3 s,f,0x2c214⟩) (by simp) (by rfl) (by simp [X86Routine.execute,pop1,pop2,pop3,pop4,finish,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle := ⟨pop4 s,f,0x2c215⟩) (by simp) (by rfl) (by simp [X86Routine.execute,pop1,pop2,pop3,pop4,finish,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle := finish s f) (by simp) (by rfl) (by simp [X86Routine.execute,pop1,pop2,pop3,pop4,finish,put,write,BitVec.add_assoc])
      exact .nil _
    · apply X86Routine.Prefix.step (middle := ⟨pop1 s,f,0x2c22e⟩) (by simp) (by rfl) (by simp [X86Routine.execute,pop1,pop2,pop3,pop4,finish,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle := ⟨pop2 s,f,0x2c22f⟩) (by simp) (by rfl) (by simp [X86Routine.execute,pop1,pop2,pop3,pop4,finish,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle := ⟨pop3 s,f,0x2c230⟩) (by simp) (by rfl) (by simp [X86Routine.execute,pop1,pop2,pop3,pop4,finish,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle := ⟨pop4 s,f,0x2c231⟩) (by simp) (by rfl) (by simp [X86Routine.execute,pop1,pop2,pop3,pop4,finish,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle := finish s f) (by simp) (by rfl) (by simp [X86Routine.execute,pop1,pop2,pop3,pop4,finish,put,write,BitVec.add_assoc])
      exact .nil _
    · apply X86Routine.Prefix.step (middle := ⟨pop1 s,f,0x2c23f⟩) (by simp) (by rfl) (by simp [X86Routine.execute,pop1,pop2,pop3,pop4,finish,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle := ⟨pop2 s,f,0x2c240⟩) (by simp) (by rfl) (by simp [X86Routine.execute,pop1,pop2,pop3,pop4,finish,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle := ⟨pop3 s,f,0x2c241⟩) (by simp) (by rfl) (by simp [X86Routine.execute,pop1,pop2,pop3,pop4,finish,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle := ⟨pop4 s,f,0x2c242⟩) (by simp) (by rfl) (by simp [X86Routine.execute,pop1,pop2,pop3,pop4,finish,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle := finish s f) (by simp) (by rfl) (by simp [X86Routine.execute,pop1,pop2,pop3,pop4,finish,put,write,BitVec.add_assoc])
      exact .nil _
    · apply X86Routine.Prefix.step (middle := ⟨pop1 s,f,0x2c299⟩) (by simp) (by rfl) (by simp [X86Routine.execute,pop1,pop2,pop3,pop4,finish,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle := ⟨pop2 s,f,0x2c29a⟩) (by simp) (by rfl) (by simp [X86Routine.execute,pop1,pop2,pop3,pop4,finish,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle := ⟨pop3 s,f,0x2c29b⟩) (by simp) (by rfl) (by simp [X86Routine.execute,pop1,pop2,pop3,pop4,finish,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle := ⟨pop4 s,f,0x2c29c⟩) (by simp) (by rfl) (by simp [X86Routine.execute,pop1,pop2,pop3,pop4,finish,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle := finish s f) (by simp) (by rfl) (by simp [X86Routine.execute,pop1,pop2,pop3,pop4,finish,put,write,BitVec.add_assoc])
      exact .nil _
    · apply X86Routine.Prefix.step (middle := ⟨pop1 s,f,0x2c2a3⟩) (by simp) (by rfl) (by simp [X86Routine.execute,pop1,pop2,pop3,pop4,finish,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle := ⟨pop2 s,f,0x2c2a4⟩) (by simp) (by rfl) (by simp [X86Routine.execute,pop1,pop2,pop3,pop4,finish,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle := ⟨pop3 s,f,0x2c2a5⟩) (by simp) (by rfl) (by simp [X86Routine.execute,pop1,pop2,pop3,pop4,finish,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle := ⟨pop4 s,f,0x2c2a6⟩) (by simp) (by rfl) (by simp [X86Routine.execute,pop1,pop2,pop3,pop4,finish,put,write,BitVec.add_assoc])
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
    X86Routine.Prefix program [] 3 ⟨s,f,0x2c1f4⟩ (axisEnd s 12 true 0x2c1f4) := by
  have path : X86Routine.Prefix listed [] 3 ⟨s,f,0x2c1f4⟩ (axisEnd s 12 true 0x2c1f4) := by
    apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (load32 s.memory (s.regs 1+12)) 0),0x2c1f8⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.Address.eval])
    apply X86Routine.Prefix.step (middle := ⟨putByte s 0 (if 0<(load32 s.memory (s.regs 1+12)).toInt then 1 else 0),some (compare32 (load32 s.memory (s.regs 1+12)) 0),0x2c1fb⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,cmp32_signed_le,PlayerArmor.cmp_lt,PlayerHeight.cmp_ge_prop] <;> split <;> split <;> (try simp_all) <;> omega)
    apply X86Routine.Prefix.step (middle := axisEnd s 12 true 0x2c1f4) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,axisEnd,axisValue,bit,putByte,byteReg,put,write,eax,mask_byte] <;> split <;> simp_all [write_overwrite])
    exact .nil _
  exact path.transfer program [] decoded (by simp)
theorem vgt_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 3 ⟨s,f,0x2c205⟩ (axisEnd s 12 false 0x2c205) := by
  have path : X86Routine.Prefix listed [] 3 ⟨s,f,0x2c205⟩ (axisEnd s 12 false 0x2c205) := by
    apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (load32 s.memory (s.regs 1+12)) 0),0x2c209⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.Address.eval])
    apply X86Routine.Prefix.step (middle := ⟨putByte s 0 (if (load32 s.memory (s.regs 1+12)).toInt<0 then 1 else 0),some (compare32 (load32 s.memory (s.regs 1+12)) 0),0x2c20c⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,cmp32_signed_le,PlayerArmor.cmp_lt,PlayerHeight.cmp_ge_prop] <;> split <;> split <;> (try simp_all) <;> omega)
    apply X86Routine.Prefix.step (middle := axisEnd s 12 false 0x2c205) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,axisEnd,axisValue,bit,putByte,byteReg,put,write,eax,mask_byte] <;> split <;> simp_all [write_overwrite])
    exact .nil _
  exact path.transfer program [] decoded (by simp)
theorem hle_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 3 ⟨s,f,0x2c221⟩ (axisEnd s 8 false 0x2c221) := by
  have path : X86Routine.Prefix listed [] 3 ⟨s,f,0x2c221⟩ (axisEnd s 8 false 0x2c221) := by
    apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (load32 s.memory (s.regs 1+8)) 0),0x2c225⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.Address.eval])
    apply X86Routine.Prefix.step (middle := ⟨putByte s 0 (if (load32 s.memory (s.regs 1+8)).toInt<0 then 1 else 0),some (compare32 (load32 s.memory (s.regs 1+8)) 0),0x2c228⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,cmp32_signed_le,PlayerArmor.cmp_lt,PlayerHeight.cmp_ge_prop] <;> split <;> split <;> (try simp_all) <;> omega)
    apply X86Routine.Prefix.step (middle := axisEnd s 8 false 0x2c221) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,axisEnd,axisValue,bit,putByte,byteReg,put,write,eax,mask_byte] <;> split <;> simp_all [write_overwrite])
    exact .nil _
  exact path.transfer program [] decoded (by simp)
theorem hgt_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 3 ⟨s,f,0x2c232⟩ (axisEnd s 8 true 0x2c232) := by
  have path : X86Routine.Prefix listed [] 3 ⟨s,f,0x2c232⟩ (axisEnd s 8 true 0x2c232) := by
    apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (load32 s.memory (s.regs 1+8)) 0),0x2c236⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.Address.eval])
    apply X86Routine.Prefix.step (middle := ⟨putByte s 0 (if 0<(load32 s.memory (s.regs 1+8)).toInt then 1 else 0),some (compare32 (load32 s.memory (s.regs 1+8)) 0),0x2c239⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,cmp32_signed_le,PlayerArmor.cmp_lt,PlayerHeight.cmp_ge_prop] <;> split <;> split <;> (try simp_all) <;> omega)
    apply X86Routine.Prefix.step (middle := axisEnd s 8 true 0x2c232) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,axisEnd,axisValue,bit,putByte,byteReg,put,write,eax,mask_byte] <;> split <;> simp_all [write_overwrite])
    exact .nil _
  exact path.transfer program [] decoded (by simp)

def compared (s : X86Memory.State) : X86Control.State :=
  if (s.regs 0).toInt<(s.regs 6).toInt then
    ⟨put s 0 0,some (logical32 0),0x2c298⟩
  else ⟨put s 0 1,some (compare32 (s.regs 0) (s.regs 6)),0x2c2a2⟩
theorem compare_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 3 ⟨s,f,0x2c292⟩ (compared s) := by
  have path : X86Routine.Prefix listed [] 3 ⟨s,f,0x2c292⟩ (compared s) := by
    apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (s.regs 0) (s.regs 6)),0x2c294⟩) (by simp) (by rfl) (by rfl)
    by_cases h : (s.regs 0).toInt<(s.regs 6).toInt
    · apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (s.regs 0) (s.regs 6)),0x2c296⟩) (by simp) (by rfl) (by simp [X86Routine.execute,PlayerHeight.cmp_ge,PlayerHeight.cmp_ge_prop,show ¬(s.regs 6).toInt≤(s.regs 0).toInt by omega])
      apply X86Routine.Prefix.step (middle := compared s) (by simp) (by rfl) (by simp [X86Routine.execute,compared,h,logical32])
      exact .nil _
    · apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (s.regs 0) (s.regs 6)),0x2c29d⟩) (by simp) (by rfl) (by simp [X86Routine.execute,PlayerHeight.cmp_ge,PlayerHeight.cmp_ge_prop,show (s.regs 6).toInt≤(s.regs 0).toInt by omega])
      apply X86Routine.Prefix.step (middle := compared s) (by simp) (by rfl) (by simp [X86Routine.execute,compared,h,logical32])
      exact .nil _
  exact path.transfer program [] decoded (by simp)



def signFlags (w : Word) := logical32 (w &&& (0x80000000#32))
def shortcutCore (s : X86Memory.State) := put s 3 (s.regs 3 ^^^ load32 s.memory (s.regs 1+12))
def shortcut (s : X86Memory.State) : X86Control.State :=
  if (signFlags ((shortcutCore s).regs 3)).zero then
    ⟨put (shortcutCore s) 0 0,some (logical32 0),0x2c298⟩
  else ⟨put (shortcutCore s) 0 1,some (signFlags ((shortcutCore s).regs 3)),0x2c2a2⟩
theorem shortcut_execution (s : X86Memory.State) (f : Option Flags) :
    ∃ n, n≤5 ∧ X86Routine.Prefix program [] n ⟨s,f,0x2c263⟩ (shortcut s) := by
  have head : X86Routine.Prefix listed [] 2 ⟨s,f,0x2c263⟩
      ⟨shortcutCore s,some (signFlags ((shortcutCore s).regs 3)),0x2c26c⟩ := by
    apply X86Routine.Prefix.step (middle := ⟨shortcutCore s,some (logical32 ((shortcutCore s).regs 3)),0x2c266⟩) (by simp) (by rfl) (by simp [X86Routine.execute,shortcutCore,X86Block.Address.eval,put,write])
    apply X86Routine.Prefix.step (middle := ⟨shortcutCore s,some (signFlags ((shortcutCore s).regs 3)),0x2c26c⟩) (by simp) (by rfl) (by rfl)
    exact .nil _
  have head := head.transfer program [] decoded (by simp)
  by_cases h : (signFlags ((shortcutCore s).regs 3)).zero=true
  · have tail : X86Routine.Prefix listed [] 2
        ⟨shortcutCore s,some (signFlags ((shortcutCore s).regs 3)),0x2c26c⟩ (shortcut s) := by
      apply X86Routine.Prefix.step (middle := ⟨shortcutCore s,some (signFlags ((shortcutCore s).regs 3)),0x2c296⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,h])
      apply X86Routine.Prefix.step (middle := shortcut s) (by simp) (by rfl) (by simp [X86Routine.execute,shortcut,h,logical32])
      exact .nil _
    exact ⟨4,by omega,OriginalGroupBounds.prefix_join head (tail.transfer program [] decoded (by simp))⟩
  · have tail : X86Routine.Prefix listed [] 3
        ⟨shortcutCore s,some (signFlags ((shortcutCore s).regs 3)),0x2c26c⟩ (shortcut s) := by
      apply X86Routine.Prefix.step (middle := ⟨shortcutCore s,some (signFlags ((shortcutCore s).regs 3)),0x2c26e⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,h])
      apply X86Routine.Prefix.step (middle := ⟨shortcutCore s,some (signFlags ((shortcutCore s).regs 3)),0x2c29d⟩) (by simp) (by rfl) (by rfl)
      apply X86Routine.Prefix.step (middle := shortcut s) (by simp) (by rfl) (by simp [X86Routine.execute,shortcut,h])
      exact .nil _
    exact ⟨5,by omega,OriginalGroupBounds.prefix_join head (tail.transfer program [] decoded (by simp))⟩

def diagonal (s : X86Memory.State) : X86Control.State :=
  if (signFlags ((delta s).regs 0)).zero then
    finish (compared (product (delta s))).core (compared (product (delta s))).flags
  else finish (shortcut (delta s)).core (shortcut (delta s)).flags

theorem diagonal_execution (s : X86Memory.State) (f : Option Flags) :
    ∃ n, n≤33 ∧ X86Routine.Prefix program [] n ⟨s,f,0x2c243⟩ (diagonal s) := by
  have start := delta_execution s f
  by_cases h : (signFlags ((delta s).regs 0)).zero=true
  · have branch : X86Routine.Prefix listed [] 1
        ⟨delta s,some (signFlags ((delta s).regs 0)),0x2c261⟩
        ⟨delta s,some (signFlags ((delta s).regs 0)),0x2c270⟩ := by
      apply X86Routine.Prefix.step (middle := ⟨delta s,some (signFlags ((delta s).regs 0)),0x2c270⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,h])
      exact .nil _
    have branch := branch.transfer program [] decoded (by simp)
    have arithmetic := product_execution (delta s) (some (signFlags ((delta s).regs 0)))
    have cmp := compare_execution (product (delta s)) none
    have done := finish_execution (compared (product (delta s))).core (compared (product (delta s))).flags
      (compared (product (delta s))).pc (by unfold compared; split <;> simp)
    refine ⟨33,by omega,?_⟩
    simpa only [diagonal,if_pos h] using OriginalGroupBounds.prefix_join start
      (OriginalGroupBounds.prefix_join branch (OriginalGroupBounds.prefix_join arithmetic (OriginalGroupBounds.prefix_join cmp done)))
  · have branch : X86Routine.Prefix listed [] 1
        ⟨delta s,some (signFlags ((delta s).regs 0)),0x2c261⟩
        ⟨delta s,some (signFlags ((delta s).regs 0)),0x2c263⟩ := by
      apply X86Routine.Prefix.step (middle := ⟨delta s,some (signFlags ((delta s).regs 0)),0x2c263⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,h])
      exact .nil _
    have branch := branch.transfer program [] decoded (by simp)
    obtain ⟨n,hn,fast⟩ := shortcut_execution (delta s) (some (signFlags ((delta s).regs 0)))
    have done := finish_execution (shortcut (delta s)).core (shortcut (delta s)).flags
      (shortcut (delta s)).pc (by unfold shortcut; split <;> simp)
    refine ⟨12+(1+(n+5)),by omega,?_⟩
    simpa only [diagonal,if_neg h] using OriginalGroupBounds.prefix_join start
      (OriginalGroupBounds.prefix_join branch (OriginalGroupBounds.prefix_join fast done))

def vx (s : X86Memory.State) := load32 s.memory (s.regs 1)
def vy (s : X86Memory.State) := load32 s.memory (s.regs 1+4)
def dx (s : X86Memory.State) := load32 s.memory (s.regs 1+8)
def dy (s : X86Memory.State) := load32 s.memory (s.regs 1+12)
def body (s : X86Memory.State) : X86Control.State :=
  if dx s=0 then
    if (s.regs 6).toInt≤(vx s).toInt then
      finish (axisEnd s 12 true 0x2c1f4).core (axisEnd s 12 true 0x2c1f4).flags
    else finish (axisEnd s 12 false 0x2c205).core (axisEnd s 12 false 0x2c205).flags
  else if dy s=0 then
    if (s.regs 0).toInt≤(vy s).toInt then
      finish (axisEnd s 8 false 0x2c221).core (axisEnd s 8 false 0x2c221).flags
    else finish (axisEnd s 8 true 0x2c232).core (axisEnd s 8 true 0x2c232).flags
  else diagonal s

@[simp] theorem compare_zero (w : Word) : (compare32 w (0#32)).zero=(w==0) := by simp [compare32]
theorem body_execution (s : X86Memory.State) (f : Option Flags) (same : s.regs 3=s.regs 1) :
    ∃ n, n≤37 ∧ X86Routine.Prefix program [] n ⟨s,f,0x2c1ea⟩ (body s) := by
  by_cases hx : dx s=0
  · by_cases hv : (s.regs 6).toInt≤(vx s).toInt
    · let t := axisEnd s 12 true 0x2c1f4
      have head : X86Routine.Prefix listed [] 4 ⟨s,f,0x2c1ea⟩ ⟨s,some (compare32 (s.regs 6) (vx s)),0x2c1f4⟩ := by
        apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (dx s) 0),0x2c1ee⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,blockPreservesFlags,cmp32_signed_le,PlayerHeight.cmp_ge,PlayerHeight.cmp_ge_prop,compare_zero,vx,vy,dx,dy,OriginalLineSide.dx,OriginalLineSide.dy,put,write,hx,hv,same])
        apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (dx s) 0),0x2c1f0⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,blockPreservesFlags,cmp32_signed_le,PlayerHeight.cmp_ge,PlayerHeight.cmp_ge_prop,compare_zero,vx,vy,dx,dy,OriginalLineSide.dx,OriginalLineSide.dy,put,write,hx,hv,same])
        apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (s.regs 6) (vx s)),0x2c1f2⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,blockPreservesFlags,cmp32_signed_le,PlayerHeight.cmp_ge,PlayerHeight.cmp_ge_prop,compare_zero,vx,vy,dx,dy,OriginalLineSide.dx,OriginalLineSide.dy,put,write,hx,hv,same])
        apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (s.regs 6) (vx s)),0x2c1f4⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,blockPreservesFlags,cmp32_signed_le,PlayerHeight.cmp_ge,PlayerHeight.cmp_ge_prop,compare_zero,vx,vy,dx,dy,OriginalLineSide.dx,OriginalLineSide.dy,put,write,hx,hv,same])
        exact .nil _
      have head := head.transfer program [] decoded (by simp)
      have tail := vle_execution s (some (compare32 (s.regs 6) (vx s)))
      have done := finish_execution t.core t.flags t.pc (by simp [t,axisEnd])
      refine ⟨12,by omega,?_⟩
      simpa only [body,if_pos hx,if_pos hv] using OriginalGroupBounds.prefix_join (OriginalGroupBounds.prefix_join head tail) done
    · let t := axisEnd s 12 false 0x2c205
      have head : X86Routine.Prefix listed [] 4 ⟨s,f,0x2c1ea⟩ ⟨s,some (compare32 (s.regs 6) (vx s)),0x2c205⟩ := by
        apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (dx s) 0),0x2c1ee⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,blockPreservesFlags,cmp32_signed_le,PlayerHeight.cmp_ge,PlayerHeight.cmp_ge_prop,compare_zero,vx,vy,dx,dy,OriginalLineSide.dx,OriginalLineSide.dy,put,write,hx,hv,same])
        apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (dx s) 0),0x2c1f0⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,blockPreservesFlags,cmp32_signed_le,PlayerHeight.cmp_ge,PlayerHeight.cmp_ge_prop,compare_zero,vx,vy,dx,dy,OriginalLineSide.dx,OriginalLineSide.dy,put,write,hx,hv,same])
        apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (s.regs 6) (vx s)),0x2c1f2⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,blockPreservesFlags,cmp32_signed_le,PlayerHeight.cmp_ge,PlayerHeight.cmp_ge_prop,compare_zero,vx,vy,dx,dy,OriginalLineSide.dx,OriginalLineSide.dy,put,write,hx,hv,same])
        apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (s.regs 6) (vx s)),0x2c205⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,blockPreservesFlags,cmp32_signed_le,PlayerHeight.cmp_ge,PlayerHeight.cmp_ge_prop,compare_zero,vx,vy,dx,dy,OriginalLineSide.dx,OriginalLineSide.dy,put,write,hx,hv,same])
        exact .nil _
      have head := head.transfer program [] decoded (by simp)
      have tail := vgt_execution s (some (compare32 (s.regs 6) (vx s)))
      have done := finish_execution t.core t.flags t.pc (by simp [t,axisEnd])
      refine ⟨12,by omega,?_⟩
      simpa only [body,if_pos hx,if_neg hv] using OriginalGroupBounds.prefix_join (OriginalGroupBounds.prefix_join head tail) done
  · by_cases hy : dy s=0
    · by_cases hv : (s.regs 0).toInt≤(vy s).toInt
      · let t := axisEnd s 8 false 0x2c221
        have head : X86Routine.Prefix listed [] 6 ⟨s,f,0x2c1ea⟩ ⟨s,some (compare32 (s.regs 0) (vy s)),0x2c221⟩ := by
          apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (dx s) 0),0x2c1ee⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,blockPreservesFlags,cmp32_signed_le,PlayerHeight.cmp_ge,PlayerHeight.cmp_ge_prop,compare_zero,vx,vy,dx,dy,OriginalLineSide.dx,OriginalLineSide.dy,put,write,hx,hy,hv,same])
          apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (dx s) 0),0x2c216⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,blockPreservesFlags,cmp32_signed_le,PlayerHeight.cmp_ge,PlayerHeight.cmp_ge_prop,compare_zero,vx,vy,dx,dy,OriginalLineSide.dx,OriginalLineSide.dy,put,write,hx,hy,hv,same])
          apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (dy s) 0),0x2c21a⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,blockPreservesFlags,cmp32_signed_le,PlayerHeight.cmp_ge,PlayerHeight.cmp_ge_prop,compare_zero,vx,vy,dx,dy,OriginalLineSide.dx,OriginalLineSide.dy,put,write,hx,hy,hv,same])
          apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (dy s) 0),0x2c21c⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,blockPreservesFlags,cmp32_signed_le,PlayerHeight.cmp_ge,PlayerHeight.cmp_ge_prop,compare_zero,vx,vy,dx,dy,OriginalLineSide.dx,OriginalLineSide.dy,put,write,hx,hy,hv,same])
          apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (s.regs 0) (vy s)),0x2c21f⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,blockPreservesFlags,cmp32_signed_le,PlayerHeight.cmp_ge,PlayerHeight.cmp_ge_prop,compare_zero,vx,vy,dx,dy,OriginalLineSide.dx,OriginalLineSide.dy,put,write,hx,hy,hv,same])
          apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (s.regs 0) (vy s)),0x2c221⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,blockPreservesFlags,cmp32_signed_le,PlayerHeight.cmp_ge,PlayerHeight.cmp_ge_prop,compare_zero,vx,vy,dx,dy,OriginalLineSide.dx,OriginalLineSide.dy,put,write,hx,hy,hv,same])
          exact .nil _
        have head := head.transfer program [] decoded (by simp)
        have tail := hle_execution s (some (compare32 (s.regs 0) (vy s)))
        have done := finish_execution t.core t.flags t.pc (by simp [t,axisEnd])
        refine ⟨14,by omega,?_⟩
        simpa only [body,if_neg hx,if_pos hy,if_pos hv] using OriginalGroupBounds.prefix_join (OriginalGroupBounds.prefix_join head tail) done
      · let t := axisEnd s 8 true 0x2c232
        have head : X86Routine.Prefix listed [] 6 ⟨s,f,0x2c1ea⟩ ⟨s,some (compare32 (s.regs 0) (vy s)),0x2c232⟩ := by
          apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (dx s) 0),0x2c1ee⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,blockPreservesFlags,cmp32_signed_le,PlayerHeight.cmp_ge,PlayerHeight.cmp_ge_prop,compare_zero,vx,vy,dx,dy,OriginalLineSide.dx,OriginalLineSide.dy,put,write,hx,hy,hv,same])
          apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (dx s) 0),0x2c216⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,blockPreservesFlags,cmp32_signed_le,PlayerHeight.cmp_ge,PlayerHeight.cmp_ge_prop,compare_zero,vx,vy,dx,dy,OriginalLineSide.dx,OriginalLineSide.dy,put,write,hx,hy,hv,same])
          apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (dy s) 0),0x2c21a⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,blockPreservesFlags,cmp32_signed_le,PlayerHeight.cmp_ge,PlayerHeight.cmp_ge_prop,compare_zero,vx,vy,dx,dy,OriginalLineSide.dx,OriginalLineSide.dy,put,write,hx,hy,hv,same])
          apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (dy s) 0),0x2c21c⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,blockPreservesFlags,cmp32_signed_le,PlayerHeight.cmp_ge,PlayerHeight.cmp_ge_prop,compare_zero,vx,vy,dx,dy,OriginalLineSide.dx,OriginalLineSide.dy,put,write,hx,hy,hv,same])
          apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (s.regs 0) (vy s)),0x2c21f⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,blockPreservesFlags,cmp32_signed_le,PlayerHeight.cmp_ge,PlayerHeight.cmp_ge_prop,compare_zero,vx,vy,dx,dy,OriginalLineSide.dx,OriginalLineSide.dy,put,write,hx,hy,hv,same])
          apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (s.regs 0) (vy s)),0x2c232⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,blockPreservesFlags,cmp32_signed_le,PlayerHeight.cmp_ge,PlayerHeight.cmp_ge_prop,compare_zero,vx,vy,dx,dy,OriginalLineSide.dx,OriginalLineSide.dy,put,write,hx,hy,hv,same])
          exact .nil _
        have head := head.transfer program [] decoded (by simp)
        have tail := hgt_execution s (some (compare32 (s.regs 0) (vy s)))
        have done := finish_execution t.core t.flags t.pc (by simp [t,axisEnd])
        refine ⟨14,by omega,?_⟩
        simpa only [body,if_neg hx,if_pos hy,if_neg hv] using OriginalGroupBounds.prefix_join (OriginalGroupBounds.prefix_join head tail) done
    ·
      have head : X86Routine.Prefix listed [] 4 ⟨s,f,0x2c1ea⟩ ⟨s,some (compare32 (dy s) 0),0x2c243⟩ := by
        apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (dx s) 0),0x2c1ee⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,blockPreservesFlags,cmp32_signed_le,PlayerHeight.cmp_ge,PlayerHeight.cmp_ge_prop,compare_zero,vx,vy,dx,dy,OriginalLineSide.dx,OriginalLineSide.dy,put,write,hx,hy,same])
        apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (dx s) 0),0x2c216⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,blockPreservesFlags,cmp32_signed_le,PlayerHeight.cmp_ge,PlayerHeight.cmp_ge_prop,compare_zero,vx,vy,dx,dy,OriginalLineSide.dx,OriginalLineSide.dy,put,write,hx,hy,same])
        apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (dy s) 0),0x2c21a⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,blockPreservesFlags,cmp32_signed_le,PlayerHeight.cmp_ge,PlayerHeight.cmp_ge_prop,compare_zero,vx,vy,dx,dy,OriginalLineSide.dx,OriginalLineSide.dy,put,write,hx,hy,same])
        apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (dy s) 0),0x2c243⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,blockPreservesFlags,cmp32_signed_le,PlayerHeight.cmp_ge,PlayerHeight.cmp_ge_prop,compare_zero,vx,vy,dx,dy,OriginalLineSide.dx,OriginalLineSide.dy,put,write,hx,hy,same])
        exact .nil _
      have head := head.transfer program [] decoded (by simp)
      obtain ⟨n,hn,rest⟩ := diagonal_execution s (some (compare32 (dy s) 0))
      refine ⟨4+n,by omega,?_⟩
      simpa only [body,if_neg hx,if_neg hy] using OriginalGroupBounds.prefix_join head rest

def result (s : X86Memory.State) := body (prepare s)
theorem execution (s : X86Memory.State) (f : Option Flags) :
    ∃ n, n≤44 ∧ X86Routine.Prefix program [] n ⟨s,f,0x2c1e0⟩ (result s) := by
  have first := prepare_execution s f
  have same : (prepare s).regs 3=(prepare s).regs 1 := by
    simp [prepare,prepare1,prepare2,prepare3,prepare4,prepare5,prepare6,prepare7,X86Routine.pushWord,put,write]
  obtain ⟨n,hn,rest⟩ := body_execution (prepare s) f same
  exact ⟨7+n,by omega,OriginalGroupBounds.prefix_join first rest⟩
theorem sign_zero (w : Word) : (logical32 (w &&& (0x80000000#32))).zero = !decide (w.toInt<0) := by
  have mask : (0x80000000#32)=BitVec.twoPow 32 31 := by decide
  have bit : w.getLsbD 31=w.msb := by rfl
  have neg : decide (w.toInt<0)=w.msb := by
    cases h : w.msb
    · have := BitVec.toInt_nonneg_of_msb_false h
      simp [show ¬w.toInt<0 by omega]
    · simp [BitVec.toInt_neg_of_msb_true h]
  rw [neg]
  unfold logical32
  rw [mask,BitVec.and_twoPow,bit]
  cases w.msb <;> decide +kernel

def left (s : X86Memory.State) := mulWord ((dy s).sshiftRight 8) ((s.regs 6-vx s).sshiftRight 8)
def right (s : X86Memory.State) := mulWord ((s.regs 0-vy s).sshiftRight 8) ((dx s).sshiftRight 8)
def signs (s : X86Memory.State) := dy s ^^^ dx s ^^^ (s.regs 6-vx s) ^^^ (s.regs 0-vy s)
def fastSign (s : X86Memory.State) := dy s ^^^ (s.regs 6-vx s)
@[simp] theorem delta_sign (s : X86Memory.State) : (delta s).regs 0=signs s := by
  simp [delta,delta1,delta2,delta3,delta4,delta5,delta6,delta7,delta8,delta9,delta10,delta11,delta12,product,product1,product2,product3,product4,product5,product6,product7,product8,product9,product10,product11,product12,multiply,put,write,eax,ebx,edx,vx,vy,dx,dy,OriginalLineSide.dx,OriginalLineSide.dy,left,right,signs,fastSign,shortcutCore,BitVec.xor_comm]
@[simp] theorem fast_sign (s : X86Memory.State) : (shortcutCore (delta s)).regs 3=fastSign s := by
  simp [delta,delta1,delta2,delta3,delta4,delta5,delta6,delta7,delta8,delta9,delta10,delta11,delta12,product,product1,product2,product3,product4,product5,product6,product7,product8,product9,product10,product11,product12,multiply,put,write,eax,ebx,edx,vx,vy,dx,dy,OriginalLineSide.dx,OriginalLineSide.dy,left,right,signs,fastSign,shortcutCore,BitVec.xor_comm]
@[simp] theorem product_value (s : X86Memory.State) : (product (delta s)).regs 0=right s ∧ (product (delta s)).regs 6=left s := by
  simp [delta,delta1,delta2,delta3,delta4,delta5,delta6,delta7,delta8,delta9,delta10,delta11,delta12,product,product1,product2,product3,product4,product5,product6,product7,product8,product9,product10,product11,product12,multiply,put,write,eax,ebx,edx,vx,vy,dx,dy,OriginalLineSide.dx,OriginalLineSide.dy,left,right,signs,fastSign,shortcutCore,BitVec.xor_comm]
@[simp] theorem delta_memory (s : X86Memory.State) : (delta s).memory=s.memory := by
  simp [delta,delta1,delta2,delta3,delta4,delta5,delta6,delta7,delta8,delta9,delta10,delta11,delta12,product,product1,product2,product3,product4,product5,product6,product7,product8,product9,product10,product11,product12,multiply,put,write,eax,ebx,edx,vx,vy,dx,dy,OriginalLineSide.dx,OriginalLineSide.dy,left,right,signs,fastSign,shortcutCore,BitVec.xor_comm]
@[simp] theorem delta_stack (s : X86Memory.State) : (delta s).regs 4=s.regs 4 := by
  simp [delta,delta1,delta2,delta3,delta4,delta5,delta6,delta7,delta8,delta9,delta10,delta11,delta12,product,product1,product2,product3,product4,product5,product6,product7,product8,product9,product10,product11,product12,multiply,put,write,eax,ebx,edx,vx,vy,dx,dy,OriginalLineSide.dx,OriginalLineSide.dy,left,right,signs,fastSign,shortcutCore,BitVec.xor_comm]
@[simp] theorem product_memory (s : X86Memory.State) : (product s).memory=s.memory := by
  simp [delta,delta1,delta2,delta3,delta4,delta5,delta6,delta7,delta8,delta9,delta10,delta11,delta12,product,product1,product2,product3,product4,product5,product6,product7,product8,product9,product10,product11,product12,multiply,put,write,eax,ebx,edx,vx,vy,dx,dy,OriginalLineSide.dx,OriginalLineSide.dy,left,right,signs,fastSign,shortcutCore,BitVec.xor_comm]
@[simp] theorem product_stack (s : X86Memory.State) : (product s).regs 4=s.regs 4 := by
  simp [delta,delta1,delta2,delta3,delta4,delta5,delta6,delta7,delta8,delta9,delta10,delta11,delta12,product,product1,product2,product3,product4,product5,product6,product7,product8,product9,product10,product11,product12,multiply,put,write,eax,ebx,edx,vx,vy,dx,dy,OriginalLineSide.dx,OriginalLineSide.dy,left,right,signs,fastSign,shortcutCore,BitVec.xor_comm]
def side (s : X86Memory.State) : Bool :=
  if dx s=0 then
    if (s.regs 6).toInt≤(vx s).toInt then decide (0<(dy s).toInt) else decide ((dy s).toInt<0)
  else if dy s=0 then
    if (s.regs 0).toInt≤(vy s).toInt then decide ((dx s).toInt<0) else decide (0<(dx s).toInt)
  else if (signs s).toInt<0 then decide ((fastSign s).toInt<0)
  else decide ((left s).toInt≤(right s).toInt)
@[simp] theorem finish_value (s : X86Memory.State) (f : Option Flags) :
    (finish s f).core.regs 0=s.regs 0 := by
  simp [finish,pop1,pop2,pop3,pop4,put,write]
theorem body_value (s : X86Memory.State) : (body s).core.regs 0=bit (side s) := by
  by_cases hx : dx s=0
  · simp only [body,side,if_pos hx]
    split <;> simp [finish_value,axisEnd,axisValue,dx,dy,put,write]
  · by_cases hy : dy s=0
    · simp only [body,side,if_neg hx,if_pos hy]
      split <;> simp [finish_value,axisEnd,axisValue,dx,dy,put,write]
    · simp only [body,side,if_neg hx,if_neg hy,diagonal,signFlags,sign_zero,delta_sign]
      by_cases h : (signs s).toInt<0
      · simp only [h,decide_true,Bool.not_true,Bool.false_eq_true,if_false,if_true,finish_value]
        unfold shortcut
        simp only [signFlags,sign_zero,fast_sign]
        by_cases k : (fastSign s).toInt<0 <;>
          simp [k,put,write,bit]
      · simp only [h,decide_false,Bool.not_false,if_true,if_false,finish_value]
        unfold compared
        split <;> simp_all [bit,put,write,(product_value s).1,(product_value s).2]

theorem body_frame (s : X86Memory.State) :
    (body s).core.memory=s.memory ∧ (body s).core.regs 4=s.regs 4+20 ∧
    (body s).core.regs 5=load32 s.memory (s.regs 4) ∧
    (body s).core.regs 7=load32 s.memory (s.regs 4+4) ∧
    (body s).core.regs 6=load32 s.memory (s.regs 4+8) ∧
    (body s).core.regs 1=load32 s.memory (s.regs 4+12) ∧
    (body s).pc=(load32 s.memory (s.regs 4+16)).toNat := by
  unfold body
  split <;> (try split) <;> (try split)
  all_goals try (simp [axisEnd,finish,pop1,pop2,pop3,pop4,put,write])
  unfold diagonal
  split
  · unfold compared; split <;> simp [finish,pop1,pop2,pop3,pop4,put,write]
  · unfold shortcut; split <;> simp [shortcutCore,finish,pop1,pop2,pop3,pop4,put,write]
def saved (s : X86Memory.State) : Memory :=
  store32 (store32 (store32 (store32 s.memory (s.regs 4-(4#32)) (s.regs 1))
    (s.regs 4-(8#32)) (s.regs 6)) (s.regs 4-(12#32)) (s.regs 7)) (s.regs 4-(16#32)) (s.regs 5)
theorem prepared_memory (s : X86Memory.State) : (prepare s).memory=saved s := by
  simp [prepare,prepare1,prepare2,prepare3,prepare4,prepare5,prepare6,prepare7,X86Routine.pushWord,put,write,saved,BitVec.sub_eq_add_neg,BitVec.add_assoc]
theorem prepared_regs (s : X86Memory.State) :
    (prepare s).regs 6=s.regs 0 ∧ (prepare s).regs 0=s.regs 2 ∧
    (prepare s).regs 1=s.regs 3 ∧ (prepare s).regs 4=s.regs 4-(16#32) := by
  simp [prepare,prepare1,prepare2,prepare3,prepare4,prepare5,prepare6,prepare7,X86Routine.pushWord,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc]
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

structure Inputs (s : X86Memory.State) (line : Collision.Divline) (x y : Fixed)
    (linePtr : Word) : Prop where
  pointX : s.regs 0=x.raw.toBitVec
  pointY : s.regs 2=y.raw.toBitVec
  pointer : s.regs 3=linePtr
  originX : load32 s.memory linePtr=line.x.raw.toBitVec
  originY : load32 s.memory (linePtr+4)=line.y.raw.toBitVec
  deltaX : load32 s.memory (linePtr+8)=line.dx.raw.toBitVec
  deltaY : load32 s.memory (linePtr+12)=line.dy.raw.toBitVec
  safe : ∀ a∈[linePtr,linePtr+4,linePtr+8,linePtr+12],
    ∀ off∈[(4#32),8,12,16], Apart a (s.regs 4-off)

theorem live (s : X86Memory.State) (line : Collision.Divline) (x y : Fixed)
    (linePtr : Word) (h : Inputs s line x y linePtr) :
    (result s).core.regs 0=bit (line.pointSide x y) := by
  have keep (a : Word) (ha : a∈[linePtr,linePtr+4,linePtr+8,linePtr+12]) := prepare_frame s a (h.safe a ha)
  have r := prepared_regs s
  have ptr := r.2.2.1.trans h.pointer
  have vx' : vx (prepare s)=line.x.raw.toBitVec := by
    unfold vx; rw [ptr,keep _ (by simp),h.originX]
  have vy' : vy (prepare s)=line.y.raw.toBitVec := by
    unfold vy; rw [ptr,keep _ (by simp),h.originY]
  have dx' : dx (prepare s)=line.dx.raw.toBitVec := by
    unfold dx; rw [ptr,keep _ (by simp),h.deltaX]
  have dy' : dy (prepare s)=line.dy.raw.toBitVec := by
    unfold dy; rw [ptr,keep _ (by simp),h.deltaY]
  unfold result
  rw [body_value]
  unfold side left right signs fastSign
  rw [vx',vy',dx',dy',r.1,r.2.1,h.pointX,h.pointY]
  congr 1
  simp only [Collision.Divline.pointSide,mulWord,Fixed.sub,Int32.le_iff_toInt_le,Int32.lt_iff_toInt_lt,
    Int32.toInt_toBitVec,Int32.toBitVec_inj,Int32.toBitVec_ofBitVec]
  simp only [show (0 : Word)=(0 : Int32).toBitVec from rfl,Int32.toBitVec_inj,beq_iff_eq,Int32.toInt_zero]
  rfl
end Doom.Proofs.OriginalDivlineSide
