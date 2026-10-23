import Doom.Proofs.OriginalPathIntercept
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalPathSecondIntercept
open Verification X86 X86Memory X86Control BlockSummary
def code : List UInt8 := [0x89,0x44,0x24,0x24,0x8b,0x4c,0x24,0x10,0xc1,0xfe,0x7,0x89,0xd8,0x8b,0x5c,0x24,0x24,0x31,0xff,0xf7,0xeb,0xf,0xac,0xd0,0x10,0x8d,0x2c,0x6,0x8b,0x74,0x24,0xc]
def bytesProgram (bytes : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2ca5f≤pc ∧ pc<0x2ca7f then X86Routine.decodeAt bytes (pc-0x2ca5f) else none
def program := bytesProgram code
def listed : X86Routine.Program
  | 0x2ca5f => some (.control (.block (.store ⟨some 4,none,0,36⟩ 0)),4)
  | 0x2ca63 => some (.control (.block (.load 1 ⟨some 4,none,0,16⟩)),4)
  | 0x2ca67 => some (.sar 6 7,3)
  | 0x2ca6a => some (.control (.block (.legacy (.mov 0 3))),2)
  | 0x2ca6c => some (.control (.block (.load 3 ⟨some 4,none,0,36⟩)),4)
  | 0x2ca70 => some (.xorRegister 7 7,2)
  | 0x2ca72 => some (.control (.block (.arithmetic (.imul 3))),2)
  | 0x2ca74 => some (.control (.block (.arithmetic (.shrd 0 2 16))),4)
  | 0x2ca78 => some (.control (.block (.lea 5 ⟨some 6,some 0,0,0⟩)),3)
  | 0x2ca7b => some (.control (.block (.load 6 ⟨some 4,none,0,12⟩)),4)
  | _ => none
theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def shifted (s : X86Memory.State) := (s.regs 6).sshiftRight 7
def product (s : X86Memory.State) := mulWord (s.regs 3) (s.regs 0)
def intercept (s : X86Memory.State) := shifted s+product s
def saved (s : X86Memory.State) := store32 s.memory (s.regs 4+36) (s.regs 0)
@[local simp] theorem slot_12_36 (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(36#32)) v) (sp+(12#32))=load32 m (sp+(12#32)) := by
  exact load_store_apart _ _ _ _ (OriginalPathXStep.apart_translate sp _ _ (by unfold Apart; decide))
@[local simp] theorem slot_16_36 (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(36#32)) v) (sp+(16#32))=load32 m (sp+(16#32)) := by
  exact load_store_apart _ _ _ _ (OriginalPathXStep.apart_translate sp _ _ (by unfold Apart; decide))
@[local simp] theorem slot_28_36 (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(36#32)) v) (sp+(28#32))=load32 m (sp+(28#32)) := by
  exact load_store_apart _ _ _ _ (OriginalPathXStep.apart_translate sp _ _ (by unfold Apart; decide))
@[local simp] theorem slot_32_36 (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(36#32)) v) (sp+(32#32))=load32 m (sp+(32#32)) := by
  exact load_store_apart _ _ _ _ (OriginalPathXStep.apart_translate sp _ _ (by unfold Apart; decide))
@[local simp] theorem slot_40_36 (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(36#32)) v) (sp+(40#32))=load32 m (sp+(40#32)) := by
  exact load_store_apart _ _ _ _ (OriginalPathXStep.apart_translate sp _ _ (by unfold Apart; decide))
@[local simp] theorem slot_44_36 (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(36#32)) v) (sp+(44#32))=load32 m (sp+(44#32)) := by
  exact load_store_apart _ _ _ _ (OriginalPathXStep.apart_translate sp _ _ (by unfold Apart; decide))
def c1 (s : X86Memory.State) : X86Memory.State := {s with memory:=saved s}
def c2 (s : X86Memory.State) : X86Memory.State := put (c1 s) 1 (load32 s.memory (s.regs 4+(16#32)))
def c3 (s : X86Memory.State) : X86Memory.State := put (c2 s) 6 (shifted s)
def c4 (s : X86Memory.State) : X86Memory.State := put (c3 s) 0 (s.regs 3)
def c5 (s : X86Memory.State) : X86Memory.State := put (c4 s) 3 (s.regs 0)
def c6 (s : X86Memory.State) : X86Memory.State := put (c5 s) 7 0
def c7 (s : X86Memory.State) : X86Memory.State := X86Block.execute (.arithmetic (.imul 3)) (c6 s)
def c8 (s : X86Memory.State) : X86Memory.State := multiply (c6 s)
def c9 (s : X86Memory.State) : X86Memory.State := put (c8 s) 5 (intercept s)
def c10 (s : X86Memory.State) : X86Memory.State := put (c9 s) 6 (load32 s.memory (s.regs 4+(12#32)))
def result (s : X86Memory.State) : X86Control.State := ⟨c10 s,none,0x2ca7f⟩
theorem execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 10 ⟨s,f,0x2ca5f⟩ (result s) := by
  have path : X86Routine.Prefix listed [] 10 ⟨s,f,0x2ca5f⟩ (result s) := by
    apply X86Routine.Prefix.step (middle := ⟨c1 s,f,0x2ca63⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,load_store,blockPreservesFlags,eax,ebx,edx,product,intercept,shifted,saved,multiply,c1])
    apply X86Routine.Prefix.step (middle := ⟨c2 s,f,0x2ca67⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,load_store,blockPreservesFlags,eax,ebx,edx,product,intercept,shifted,saved,multiply,c2,c1])
    apply X86Routine.Prefix.step (middle := ⟨c3 s,none,0x2ca6a⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,load_store,blockPreservesFlags,eax,ebx,edx,product,intercept,shifted,saved,multiply,c3,c2,c1])
    apply X86Routine.Prefix.step (middle := ⟨c4 s,none,0x2ca6c⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,load_store,blockPreservesFlags,eax,ebx,edx,product,intercept,shifted,saved,multiply,c4,c3,c2,c1])
    apply X86Routine.Prefix.step (middle := ⟨c5 s,none,0x2ca70⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,load_store,blockPreservesFlags,eax,ebx,edx,product,intercept,shifted,saved,multiply,c5,c4,c3,c2,c1])
    apply X86Routine.Prefix.step (middle := ⟨c6 s,some {(logical32 0) with carry:=some false},0x2ca72⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,load_store,blockPreservesFlags,eax,ebx,edx,product,intercept,shifted,saved,multiply,c6,c5,c4,c3,c2,c1])
    apply X86Routine.Prefix.step (middle := ⟨c7 s,none,0x2ca74⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,load_store,blockPreservesFlags,eax,ebx,edx,product,intercept,shifted,saved,multiply,c7,c6,c5,c4,c3,c2,c1])
    apply X86Routine.Prefix.step (middle := ⟨c8 s,none,0x2ca78⟩) (by simp) (by rfl) (by
      change some (⟨X86Block.execute (.arithmetic (.shrd 0 2 16)) (c7 s),none,0x2ca78⟩ : X86Control.State) = _
      simp only [c7,show (0 : Fin 8)=eax from rfl,show (2 : Fin 8)=edx from rfl,multiply_correct]
      rfl)
    apply X86Routine.Prefix.step (middle := ⟨c9 s,none,0x2ca7b⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,load_store,blockPreservesFlags,eax,ebx,edx,product,intercept,shifted,saved,multiply,c9,c8,c7,c6,c5,c4,c3,c2,c1])
    apply X86Routine.Prefix.step (middle := ⟨c10 s,none,0x2ca7f⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,load_store,blockPreservesFlags,eax,ebx,edx,product,intercept,shifted,saved,multiply,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1])
    exact .nil _
  exact path.transfer program [] decoded (by simp)

structure Inputs (s : X86Memory.State) (p : Collision.PathStart) (portion stride : Fixed) : Prop where
  startX : s.regs 6=p.x1.raw.toBitVec
  portionReg : s.regs 3=portion.raw.toBitVec
  strideReg : s.regs 0=stride.raw.toBitVec
  startBlockX : load32 s.memory (s.regs 4+(12#32))=p.startBlockX.toBitVec
  startBlockY : load32 s.memory (s.regs 4+(16#32))=p.startBlockY.toBitVec

structure Ready (s : X86Memory.State) (t : X86Control.State)
    (p : Collision.PathStart) (portion stride : Fixed) : Prop where
  firstIntercept : t.core.regs 5=(Collision.pathFirstIntercept p.x1 portion stride).raw.toBitVec
  strideSlot : load32 t.core.memory (s.regs 4+36)=stride.raw.toBitVec
  mapX : t.core.regs 6=p.startBlockX.toBitVec
  mapY : t.core.regs 1=p.startBlockY.toBitVec
  counter : t.core.regs 7=0
  stack : t.core.regs 4=s.regs 4
  pc : t.pc=0x2ca7f

theorem live (s : X86Memory.State) (p : Collision.PathStart) (portion stride : Fixed)
    (h : Inputs s p portion stride) : Ready s (result s) p portion stride := by
  have value : intercept s=(Collision.pathFirstIntercept p.x1 portion stride).raw.toBitVec := by
    simp only [intercept,shifted,product,mulWord,h.startX,h.portionReg,h.strideReg]
    rfl
  constructor <;> simp [result,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,multiply,put,write,eax,edx,ebx,saved,load_store,value,
    h.startX,h.portionReg,h.strideReg,h.startBlockX,h.startBlockY,shifted]

theorem frame (s : X86Memory.State) (a : Word) (safe : Apart a (s.regs 4+36)) :
    load32 (result s).core.memory a=load32 s.memory a :=
  load_store_apart _ _ _ _ safe
end Doom.Proofs.OriginalPathSecondIntercept
