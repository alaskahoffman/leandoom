import Doom.Proofs.E1M1AimActorSkipAligned
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalAimActorTop
open Verification X86 X86Memory X86Control BlockSummary Collision
attribute [local irreducible] load32 store32
def code : List UInt8 := [0xa1,0xb8,0xb9,0x2,0x0,0x8b,0x1a,0xf7,0xeb,0xf,0xac,0xd0,0x10,0x89,0xc3,0x8b,0x79,0x44,0x8b,0x41,0x14,0x8b,0x2d,0xa8,0xb9,0x2,0x0,0x1,0xf8,0x89,0xda,0x29,0xe8,0xe8,0x17,0x19,0xff,0xff,0x89,0xc6,0x89,0xc7,0x3b,0x35,0xe4,0xc1,0x2,0x0,0x7d,0xc]
def bytesProgram (bytes : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2b843≤pc ∧ pc<0x2b875 then X86Routine.decodeAt bytes (pc-0x2b843) else none
def program := bytesProgram code
def listed : X86Routine.Program
  | 0x2b843 => some (.control (.block (.load 0 ⟨none,none,0,0x2b9b8⟩)),5)
  | 0x2b848 => some (.control (.block (.legacy (.load 3 2 0))),2)
  | 0x2b84a => some (.control (.block (.arithmetic (.imul 3))),2)
  | 0x2b84c => some (.control (.block (.arithmetic (.shrd 0 2 16))),4)
  | 0x2b850 => some (.control (.block (.legacy (.mov 3 0))),2)
  | 0x2b852 => some (.control (.block (.legacy (.load 7 1 68))),3)
  | 0x2b855 => some (.control (.block (.legacy (.load 0 1 20))),3)
  | 0x2b858 => some (.control (.block (.load 5 ⟨none,none,0,0x2b9a8⟩)),6)
  | 0x2b85e => some (.control (.block (.arithmetic (.add 0 7))),2)
  | 0x2b860 => some (.control (.block (.legacy (.mov 2 3))),2)
  | 0x2b862 => some (.control (.block (.arithmetic (.sub 0 5))),2)
  | 0x2b864 => some (.call (-59113),5)
  | 0x2b869 => some (.control (.block (.legacy (.mov 6 0))),2)
  | 0x2b86b => some (.control (.block (.legacy (.mov 7 0))),2)
  | 0x2b86d => some (.control (.cmpMemory 6 ⟨none,none,0,0x2c1e4⟩),6)
  | 0x2b873 => some (.jumpSigned 0 12,2)
  | _ => none

theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def first := OriginalAimDistance.first
def inputs := OriginalAimDistance.inputs
def product := OriginalAimDistance.product
def shifted := OriginalAimDistance.shifted
def distance (s : X86Memory.State) := (shifted s).regs 0
def z (s : X86Memory.State) := load32 s.memory (s.regs 1+20)
def height (s : X86Memory.State) := load32 s.memory (s.regs 1+68)
def eye (s : X86Memory.State) := load32 s.memory (0x2b9a8#32)
def d (s : X86Memory.State) := put (shifted s) 3 (distance s)
def h (s : X86Memory.State) := put (d s) 7 (height s)
def v (s : X86Memory.State) := put (h s) 0 (z s)
def e (s : X86Memory.State) := put (v s) 5 (eye s)
def top (s : X86Memory.State) := put (e s) 0 (z s+height s)
def den (s : X86Memory.State) := put (top s) 2 (distance s)
def numerator (s : X86Memory.State) := z s+height s-eye s
def argument (s : X86Memory.State) := put (den s) 0 (numerator s)
def called (s : X86Memory.State) := X86Routine.pushWord (argument s) 0x2b869

def savedSlope (s : X86Memory.State) := put s 6 (s.regs 0)
def slopes (s : X86Memory.State) := put (savedSlope s) 7 (s.regs 0)
def lower (s : X86Memory.State) := load32 s.memory (0x2c1e4#32)
def gate (s : X86Memory.State) : X86Control.State :=
  ⟨slopes s,some (compare32 (s.regs 0) (lower s)),if (s.regs 0).toInt < (lower s).toInt then 0x2b875 else 0x2b881⟩

/-- Inline distance product and wrapped top-height subtraction, followed by the
actual FixedDiv CALL. No abstract callee summary is used. -/
theorem call_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 12 ⟨s,f,0x2b843⟩ ⟨called s,none,0x1d180⟩ := by
  have run : X86Routine.Prefix listed [] 12 ⟨s,f,0x2b843⟩ ⟨called s,none,0x1d180⟩ := by
    apply X86Routine.Prefix.step (middle := ⟨first s,f,0x2b848⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,X86.write,first,inputs,product,shifted,distance,z,height,eye,d,h,v,e,top,den,numerator,argument,called,X86Routine.pushWord,savedSlope,slopes,lower,gate,OriginalAimDistance.first,OriginalAimDistance.inputs,OriginalAimDistance.product,OriginalAimDistance.shifted,OriginalAimDistance.range,OriginalAimDistance.fraction,multiply,eax,edx,ebx,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge])
    apply X86Routine.Prefix.step (middle := ⟨inputs s,f,0x2b84a⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,X86.write,first,inputs,product,shifted,distance,z,height,eye,d,h,v,e,top,den,numerator,argument,called,X86Routine.pushWord,savedSlope,slopes,lower,gate,OriginalAimDistance.first,OriginalAimDistance.inputs,OriginalAimDistance.product,OriginalAimDistance.shifted,OriginalAimDistance.range,OriginalAimDistance.fraction,multiply,eax,edx,ebx,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge])
    apply X86Routine.Prefix.step (middle := ⟨product s,none,0x2b84c⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,X86.write,first,inputs,product,shifted,distance,z,height,eye,d,h,v,e,top,den,numerator,argument,called,X86Routine.pushWord,savedSlope,slopes,lower,gate,OriginalAimDistance.first,OriginalAimDistance.inputs,OriginalAimDistance.product,OriginalAimDistance.shifted,OriginalAimDistance.range,OriginalAimDistance.fraction,multiply,eax,edx,ebx,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge])
    apply X86Routine.Prefix.step (middle := ⟨shifted s,none,0x2b850⟩) (by simp) (by rfl) (by
      change some (⟨X86Block.execute (.arithmetic (.shrd 0 2 16)) (product s),none,0x2b850⟩ : X86Control.State)=_
      simp only [product,OriginalAimDistance.product,show (0 : Fin 8)=eax from rfl,show (2 : Fin 8)=edx from rfl,multiply_correct]
      rfl)
    apply X86Routine.Prefix.step (middle := ⟨d s,none,0x2b852⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,X86.write,first,inputs,product,shifted,distance,z,height,eye,d,h,v,e,top,den,numerator,argument,called,X86Routine.pushWord,savedSlope,slopes,lower,gate,OriginalAimDistance.first,OriginalAimDistance.inputs,OriginalAimDistance.product,OriginalAimDistance.shifted,OriginalAimDistance.range,OriginalAimDistance.fraction,multiply,eax,edx,ebx,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge])
    apply X86Routine.Prefix.step (middle := ⟨h s,none,0x2b855⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,X86.write,first,inputs,product,shifted,distance,z,height,eye,d,h,v,e,top,den,numerator,argument,called,X86Routine.pushWord,savedSlope,slopes,lower,gate,OriginalAimDistance.first,OriginalAimDistance.inputs,OriginalAimDistance.product,OriginalAimDistance.shifted,OriginalAimDistance.range,OriginalAimDistance.fraction,multiply,eax,edx,ebx,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge])
    apply X86Routine.Prefix.step (middle := ⟨v s,none,0x2b858⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,X86.write,first,inputs,product,shifted,distance,z,height,eye,d,h,v,e,top,den,numerator,argument,called,X86Routine.pushWord,savedSlope,slopes,lower,gate,OriginalAimDistance.first,OriginalAimDistance.inputs,OriginalAimDistance.product,OriginalAimDistance.shifted,OriginalAimDistance.range,OriginalAimDistance.fraction,multiply,eax,edx,ebx,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge])
    apply X86Routine.Prefix.step (middle := ⟨e s,none,0x2b85e⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,X86.write,first,inputs,product,shifted,distance,z,height,eye,d,h,v,e,top,den,numerator,argument,called,X86Routine.pushWord,savedSlope,slopes,lower,gate,OriginalAimDistance.first,OriginalAimDistance.inputs,OriginalAimDistance.product,OriginalAimDistance.shifted,OriginalAimDistance.range,OriginalAimDistance.fraction,multiply,eax,edx,ebx,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge])
    apply X86Routine.Prefix.step (middle := ⟨top s,none,0x2b860⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,X86.write,first,inputs,product,shifted,distance,z,height,eye,d,h,v,e,top,den,numerator,argument,called,X86Routine.pushWord,savedSlope,slopes,lower,gate,OriginalAimDistance.first,OriginalAimDistance.inputs,OriginalAimDistance.product,OriginalAimDistance.shifted,OriginalAimDistance.range,OriginalAimDistance.fraction,multiply,eax,edx,ebx,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge])
    apply X86Routine.Prefix.step (middle := ⟨den s,none,0x2b862⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,X86.write,first,inputs,product,shifted,distance,z,height,eye,d,h,v,e,top,den,numerator,argument,called,X86Routine.pushWord,savedSlope,slopes,lower,gate,OriginalAimDistance.first,OriginalAimDistance.inputs,OriginalAimDistance.product,OriginalAimDistance.shifted,OriginalAimDistance.range,OriginalAimDistance.fraction,multiply,eax,edx,ebx,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge])
    apply X86Routine.Prefix.step (middle := ⟨argument s,none,0x2b864⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,X86.write,first,inputs,product,shifted,distance,z,height,eye,d,h,v,e,top,den,numerator,argument,called,X86Routine.pushWord,savedSlope,slopes,lower,gate,OriginalAimDistance.first,OriginalAimDistance.inputs,OriginalAimDistance.product,OriginalAimDistance.shifted,OriginalAimDistance.range,OriginalAimDistance.fraction,multiply,eax,edx,ebx,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge])
    apply X86Routine.Prefix.step (middle := ⟨called s,none,0x1d180⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,X86.write,first,inputs,product,shifted,distance,z,height,eye,d,h,v,e,top,den,numerator,argument,called,X86Routine.pushWord,savedSlope,slopes,lower,gate,OriginalAimDistance.first,OriginalAimDistance.inputs,OriginalAimDistance.product,OriginalAimDistance.shifted,OriginalAimDistance.range,OriginalAimDistance.fraction,multiply,eax,edx,ebx,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge])
    exact .nil _
  exact run.transfer program [] decoded (by simp)

theorem gate_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 4 ⟨s,f,0x2b869⟩ (gate s) := by
  have run : X86Routine.Prefix listed [] 4 ⟨s,f,0x2b869⟩ (gate s) := by
    apply X86Routine.Prefix.step (middle := ⟨savedSlope s,f,0x2b86b⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,X86.write,first,inputs,product,shifted,distance,z,height,eye,d,h,v,e,top,den,numerator,argument,called,X86Routine.pushWord,savedSlope,slopes,lower,gate,OriginalAimDistance.first,OriginalAimDistance.inputs,OriginalAimDistance.product,OriginalAimDistance.shifted,OriginalAimDistance.range,OriginalAimDistance.fraction,multiply,eax,edx,ebx,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge]
      all_goals split <;> simp_all)
    apply X86Routine.Prefix.step (middle := ⟨slopes s,f,0x2b86d⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,X86.write,first,inputs,product,shifted,distance,z,height,eye,d,h,v,e,top,den,numerator,argument,called,X86Routine.pushWord,savedSlope,slopes,lower,gate,OriginalAimDistance.first,OriginalAimDistance.inputs,OriginalAimDistance.product,OriginalAimDistance.shifted,OriginalAimDistance.range,OriginalAimDistance.fraction,multiply,eax,edx,ebx,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge]
      all_goals split <;> simp_all)
    apply X86Routine.Prefix.step (middle := ⟨slopes s,some (compare32 (s.regs 0) (lower s)),0x2b873⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,X86.write,first,inputs,product,shifted,distance,z,height,eye,d,h,v,e,top,den,numerator,argument,called,X86Routine.pushWord,savedSlope,slopes,lower,gate,OriginalAimDistance.first,OriginalAimDistance.inputs,OriginalAimDistance.product,OriginalAimDistance.shifted,OriginalAimDistance.range,OriginalAimDistance.fraction,multiply,eax,edx,ebx,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge]
      all_goals split <;> simp_all)
    apply X86Routine.Prefix.step (middle := gate s) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,X86.write,first,inputs,product,shifted,distance,z,height,eye,d,h,v,e,top,den,numerator,argument,called,X86Routine.pushWord,savedSlope,slopes,lower,gate,OriginalAimDistance.first,OriginalAimDistance.inputs,OriginalAimDistance.product,OriginalAimDistance.shifted,OriginalAimDistance.range,OriginalAimDistance.fraction,multiply,eax,edx,ebx,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge]
      all_goals split <;> simp_all)
    exact .nil _
  exact run.transfer program [] decoded (by simp)

/-- Bit-exact source operands include wrapped height addition/subtraction and
signed fixed-point multiplication, for all represented input bit patterns. -/
theorem operands (s : X86Memory.State) (range frac targetZ targetHeight shootZ : Fixed)
    (r : OriginalAimDistance.range s=range.raw.toBitVec)
    (f : OriginalAimDistance.fraction s=frac.raw.toBitVec)
    (z0 : z s=targetZ.raw.toBitVec) (ht : height s=targetHeight.raw.toBitVec)
    (eye0 : eye s=shootZ.raw.toBitVec) :
    (called s).regs 0=(targetZ+targetHeight-shootZ).raw.toBitVec ∧
    (called s).regs 2=(range*frac).raw.toBitVec ∧
    (called s).regs 3=(range*frac).raw.toBitVec ∧
    (called s).regs 1=s.regs 1 ∧ (called s).regs 4=s.regs 4-4 := by
  simp [called,argument,numerator,den,top,e,v,h,d,distance,shifted,
    OriginalAimDistance.shifted,multiply,OriginalAimDistance.inputs,OriginalAimDistance.first,
    X86Routine.pushWord,put,X86.write,eax,edx,ebx,r,f,z0,ht,eye0,mulWord]
  exact ⟨rfl,rfl⟩
end Doom.Proofs.OriginalAimActorTop
