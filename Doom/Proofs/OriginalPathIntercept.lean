import Doom.Proofs.OriginalPathXStep
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalPathIntercept
open Verification X86 X86Memory X86Control BlockSummary
def code : List UInt8 := [0x89,0x44,0x24,0x28,0x89,0xf8,0xc1,0xf8,0x7,0x89,0x44,0x24,0x4,0x89,0xd8,0x8b,0x5c,0x24,0x28,0x29,0xf5,0xf7,0xeb,0xf,0xac,0xd0,0x10,0x8b,0x54,0x24,0x4,0x8b,0x5c,0x24,0x4,0x1,0xc2,0x81,0xe3,0xff,0xff,0x0,0x0,0x89,0x54,0x24,0x2c,0x89,0xc8,0x8b,0x54,0x24,0x18,0x8b,0x4c,0x24,0x10,0x29,0xf8,0x39,0xca]
def bytesProgram (bytes : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2c9d3≤pc ∧ pc<0x2ca10 then X86Routine.decodeAt bytes (pc-0x2c9d3) else none
def program := bytesProgram code
def listed : X86Routine.Program
  | 0x2c9d3 => some (.control (.block (.store ⟨some 4,none,0,40⟩ 0)),4)
  | 0x2c9d7 => some (.control (.block (.legacy (.mov 0 7))),2)
  | 0x2c9d9 => some (.sar 0 7,3)
  | 0x2c9dc => some (.control (.block (.store ⟨some 4,none,0,4⟩ 0)),4)
  | 0x2c9e0 => some (.control (.block (.legacy (.mov 0 3))),2)
  | 0x2c9e2 => some (.control (.block (.load 3 ⟨some 4,none,0,40⟩)),4)
  | 0x2c9e6 => some (.control (.block (.arithmetic (.sub 5 6))),2)
  | 0x2c9e8 => some (.control (.block (.arithmetic (.imul 3))),2)
  | 0x2c9ea => some (.control (.block (.arithmetic (.shrd 0 2 16))),4)
  | 0x2c9ee => some (.control (.block (.load 2 ⟨some 4,none,0,4⟩)),4)
  | 0x2c9f2 => some (.control (.block (.load 3 ⟨some 4,none,0,4⟩)),4)
  | 0x2c9f6 => some (.control (.block (.arithmetic (.add 2 0))),2)
  | 0x2c9f8 => some (.andRegister 3 65535,6)
  | 0x2c9fe => some (.control (.block (.store ⟨some 4,none,0,44⟩ 2)),4)
  | 0x2ca02 => some (.control (.block (.legacy (.mov 0 1))),2)
  | 0x2ca04 => some (.control (.block (.load 2 ⟨some 4,none,0,24⟩)),4)
  | 0x2ca08 => some (.control (.block (.load 1 ⟨some 4,none,0,16⟩)),4)
  | 0x2ca0c => some (.control (.block (.arithmetic (.sub 0 7))),2)
  | 0x2ca0e => some (.compareRegisters 2 1,2)
  | _ => none
theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def shifted (s : X86Memory.State) := (s.regs 7).sshiftRight 7
def product (s : X86Memory.State) := mulWord (s.regs 3) (s.regs 0)
def intercept (s : X86Memory.State) := shifted s+product s
def m1 (s : X86Memory.State) := store32 s.memory (s.regs 4+40) (s.regs 0)
def m4 (s : X86Memory.State) := store32 (m1 s) (s.regs 4+4) (shifted s)
def m14 (s : X86Memory.State) := store32 (m4 s) (s.regs 4+44) (intercept s)
@[local simp] theorem slot_4_40 (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(40#32)) v) (sp+(4#32))=load32 m (sp+(4#32)) := by
  exact load_store_apart _ _ _ _ (OriginalPathXStep.apart_translate sp _ _ (by unfold Apart; decide))
@[local simp] theorem slot_4_44 (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(44#32)) v) (sp+(4#32))=load32 m (sp+(4#32)) := by
  exact load_store_apart _ _ _ _ (OriginalPathXStep.apart_translate sp _ _ (by unfold Apart; decide))
@[local simp] theorem slot_16_4 (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(4#32)) v) (sp+(16#32))=load32 m (sp+(16#32)) := by
  exact load_store_apart _ _ _ _ (OriginalPathXStep.apart_translate sp _ _ (by unfold Apart; decide))
@[local simp] theorem slot_16_40 (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(40#32)) v) (sp+(16#32))=load32 m (sp+(16#32)) := by
  exact load_store_apart _ _ _ _ (OriginalPathXStep.apart_translate sp _ _ (by unfold Apart; decide))
@[local simp] theorem slot_16_44 (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(44#32)) v) (sp+(16#32))=load32 m (sp+(16#32)) := by
  exact load_store_apart _ _ _ _ (OriginalPathXStep.apart_translate sp _ _ (by unfold Apart; decide))
@[local simp] theorem slot_24_4 (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(4#32)) v) (sp+(24#32))=load32 m (sp+(24#32)) := by
  exact load_store_apart _ _ _ _ (OriginalPathXStep.apart_translate sp _ _ (by unfold Apart; decide))
@[local simp] theorem slot_24_40 (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(40#32)) v) (sp+(24#32))=load32 m (sp+(24#32)) := by
  exact load_store_apart _ _ _ _ (OriginalPathXStep.apart_translate sp _ _ (by unfold Apart; decide))
@[local simp] theorem slot_24_44 (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(44#32)) v) (sp+(24#32))=load32 m (sp+(24#32)) := by
  exact load_store_apart _ _ _ _ (OriginalPathXStep.apart_translate sp _ _ (by unfold Apart; decide))
@[local simp] theorem slot_40_4 (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(4#32)) v) (sp+(40#32))=load32 m (sp+(40#32)) := by
  exact load_store_apart _ _ _ _ (OriginalPathXStep.apart_translate sp _ _ (by unfold Apart; decide))
@[local simp] theorem slot_40_44 (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(44#32)) v) (sp+(40#32))=load32 m (sp+(40#32)) := by
  exact load_store_apart _ _ _ _ (OriginalPathXStep.apart_translate sp _ _ (by unfold Apart; decide))
@[local simp] theorem slot_44_4 (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(4#32)) v) (sp+(44#32))=load32 m (sp+(44#32)) := by
  exact load_store_apart _ _ _ _ (OriginalPathXStep.apart_translate sp _ _ (by unfold Apart; decide))
@[local simp] theorem slot_44_40 (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(40#32)) v) (sp+(44#32))=load32 m (sp+(44#32)) := by
  exact load_store_apart _ _ _ _ (OriginalPathXStep.apart_translate sp _ _ (by unfold Apart; decide))
def c1 (s : X86Memory.State) : X86Memory.State := {s with memory:=m1 s}
def c2 (s : X86Memory.State) : X86Memory.State := put (c1 s) 0 (s.regs 7)
def c3 (s : X86Memory.State) : X86Memory.State := put (c2 s) 0 (shifted s)
def c4 (s : X86Memory.State) : X86Memory.State := {c3 s with memory:=m4 s}
def c5 (s : X86Memory.State) : X86Memory.State := put (c4 s) 0 (s.regs 3)
def c6 (s : X86Memory.State) : X86Memory.State := put (c5 s) 3 (s.regs 0)
def c7 (s : X86Memory.State) : X86Memory.State := put (c6 s) 5 (s.regs 5-s.regs 6)
def c8 (s : X86Memory.State) : X86Memory.State := X86Block.execute (.arithmetic (.imul 3)) (c7 s)
def c9 (s : X86Memory.State) : X86Memory.State := multiply (c7 s)
def c10 (s : X86Memory.State) : X86Memory.State := put (c9 s) 2 (shifted s)
def c11 (s : X86Memory.State) : X86Memory.State := put (c10 s) 3 (shifted s)
def c12 (s : X86Memory.State) : X86Memory.State := put (c11 s) 2 (intercept s)
def c13 (s : X86Memory.State) : X86Memory.State := put (c12 s) 3 (shifted s &&& 65535)
def c14 (s : X86Memory.State) : X86Memory.State := {c13 s with memory:=m14 s}
def c15 (s : X86Memory.State) : X86Memory.State := put (c14 s) 0 (s.regs 1)
def c16 (s : X86Memory.State) : X86Memory.State := put (c15 s) 2 (load32 s.memory (s.regs 4+(24#32)))
def c17 (s : X86Memory.State) : X86Memory.State := put (c16 s) 1 (load32 s.memory (s.regs 4+(16#32)))
def c18 (s : X86Memory.State) : X86Memory.State := put (c17 s) 0 (s.regs 1-s.regs 7)
def c19 (s : X86Memory.State) : X86Memory.State := c18 s
def result (s : X86Memory.State) : X86Control.State :=
  ⟨c19 s,some (compare32 (load32 s.memory (s.regs 4+(24#32))) (load32 s.memory (s.regs 4+(16#32)))),0x2ca10⟩
/-- The nineteen decoded instructions, including the original IMUL/SHRD pair. -/
theorem execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 19 ⟨s,f,0x2c9d3⟩ (result s) := by
  have path : X86Routine.Prefix listed [] 19 ⟨s,f,0x2c9d3⟩ (result s) := by
    apply X86Routine.Prefix.step (middle := ⟨c1 s,f,0x2c9d7⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,load_store,blockPreservesFlags,eax,ebx,edx,product,intercept,shifted,m14,m4,m1,multiply,c1])
    apply X86Routine.Prefix.step (middle := ⟨c2 s,f,0x2c9d9⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,load_store,blockPreservesFlags,eax,ebx,edx,product,intercept,shifted,m14,m4,m1,multiply,c2,c1])
    apply X86Routine.Prefix.step (middle := ⟨c3 s,none,0x2c9dc⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,load_store,blockPreservesFlags,eax,ebx,edx,product,intercept,shifted,m14,m4,m1,multiply,c3,c2,c1])
    apply X86Routine.Prefix.step (middle := ⟨c4 s,none,0x2c9e0⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,load_store,blockPreservesFlags,eax,ebx,edx,product,intercept,shifted,m14,m4,m1,multiply,c4,c3,c2,c1])
    apply X86Routine.Prefix.step (middle := ⟨c5 s,none,0x2c9e2⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,load_store,blockPreservesFlags,eax,ebx,edx,product,intercept,shifted,m14,m4,m1,multiply,c5,c4,c3,c2,c1])
    apply X86Routine.Prefix.step (middle := ⟨c6 s,none,0x2c9e6⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,load_store,blockPreservesFlags,eax,ebx,edx,product,intercept,shifted,m14,m4,m1,multiply,c6,c5,c4,c3,c2,c1])
    apply X86Routine.Prefix.step (middle := ⟨c7 s,none,0x2c9e8⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,load_store,blockPreservesFlags,eax,ebx,edx,product,intercept,shifted,m14,m4,m1,multiply,c7,c6,c5,c4,c3,c2,c1])
    apply X86Routine.Prefix.step (middle := ⟨c8 s,none,0x2c9ea⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,load_store,blockPreservesFlags,eax,ebx,edx,product,intercept,shifted,m14,m4,m1,multiply,c8,c7,c6,c5,c4,c3,c2,c1])
    apply X86Routine.Prefix.step (middle := ⟨c9 s,none,0x2c9ee⟩) (by simp) (by rfl) (by
      change some (⟨X86Block.execute (.arithmetic (.shrd 0 2 16)) (c8 s),none,0x2c9ee⟩ : X86Control.State) = _
      simp only [c8,show (0 : Fin 8)=eax from rfl,show (2 : Fin 8)=edx from rfl,multiply_correct]
      rfl)
    apply X86Routine.Prefix.step (middle := ⟨c10 s,none,0x2c9f2⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,load_store,blockPreservesFlags,eax,ebx,edx,product,intercept,shifted,m14,m4,m1,multiply,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1])
    apply X86Routine.Prefix.step (middle := ⟨c11 s,none,0x2c9f6⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,load_store,blockPreservesFlags,eax,ebx,edx,product,intercept,shifted,m14,m4,m1,multiply,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1])
    apply X86Routine.Prefix.step (middle := ⟨c12 s,none,0x2c9f8⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,load_store,blockPreservesFlags,eax,ebx,edx,product,intercept,shifted,m14,m4,m1,multiply,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1])
    apply X86Routine.Prefix.step (middle := ⟨c13 s,some {(logical32 (shifted s &&& 65535)) with carry:=some false},0x2c9fe⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,load_store,blockPreservesFlags,eax,ebx,edx,product,intercept,shifted,m14,m4,m1,multiply,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1])
    apply X86Routine.Prefix.step (middle := ⟨c14 s,some {(logical32 (shifted s &&& 65535)) with carry:=some false},0x2ca02⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,load_store,blockPreservesFlags,eax,ebx,edx,product,intercept,shifted,m14,m4,m1,multiply,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1])
    apply X86Routine.Prefix.step (middle := ⟨c15 s,some {(logical32 (shifted s &&& 65535)) with carry:=some false},0x2ca04⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,load_store,blockPreservesFlags,eax,ebx,edx,product,intercept,shifted,m14,m4,m1,multiply,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1])
    apply X86Routine.Prefix.step (middle := ⟨c16 s,some {(logical32 (shifted s &&& 65535)) with carry:=some false},0x2ca08⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,load_store,blockPreservesFlags,eax,ebx,edx,product,intercept,shifted,m14,m4,m1,multiply,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1])
    apply X86Routine.Prefix.step (middle := ⟨c17 s,some {(logical32 (shifted s &&& 65535)) with carry:=some false},0x2ca0c⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,load_store,blockPreservesFlags,eax,ebx,edx,product,intercept,shifted,m14,m4,m1,multiply,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1])
    apply X86Routine.Prefix.step (middle := ⟨c18 s,none,0x2ca0e⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,load_store,blockPreservesFlags,eax,ebx,edx,product,intercept,shifted,m14,m4,m1,multiply,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1])
    apply X86Routine.Prefix.step (middle := ⟨c19 s,some (compare32 (load32 s.memory (s.regs 4+(24#32))) (load32 s.memory (s.regs 4+(16#32)))),0x2ca10⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86.execute,X86Memory.execute,X86Block.Address.eval,put,write,load_store,blockPreservesFlags,eax,ebx,edx,product,intercept,shifted,m14,m4,m1,multiply,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1])
    exact .nil _
  exact path.transfer program [] decoded (by simp)



/-- Machine inputs at the seam; the joining proof derives these from the prior block. -/
structure Inputs (s : X86Memory.State) (p : Collision.PathStart) (portion stride : Fixed) : Prop where
  startX : s.regs 6=p.x1.raw.toBitVec
  startY : s.regs 7=p.y1.raw.toBitVec
  endX : s.regs 5=p.x2.raw.toBitVec
  endY : s.regs 1=p.y2.raw.toBitVec
  portionReg : s.regs 3=portion.raw.toBitVec
  strideReg : s.regs 0=stride.raw.toBitVec
  startBlockY : load32 s.memory (s.regs 4+(16#32))=p.startBlockY.toBitVec
  endBlockY : load32 s.memory (s.regs 4+(24#32))=p.endBlockY.toBitVec

/-- First crossing and every input to the following Y-axis direction calculation. -/
structure Ready (s : X86Memory.State) (t : X86Control.State)
    (p : Collision.PathStart) (portion stride : Fixed) : Prop where
  firstIntercept : load32 t.core.memory (s.regs 4+44)=
    (Collision.pathFirstIntercept p.y1 portion stride).raw.toBitVec
  strideSlot : load32 t.core.memory (s.regs 4+40)=stride.raw.toBitVec
  shiftedSlot : load32 t.core.memory (s.regs 4+4)=(p.y1.raw >>> 7).toBitVec
  deltaX : t.core.regs 5=(p.x2-p.x1).raw.toBitVec
  deltaY : t.core.regs 0=(p.y2-p.y1).raw.toBitVec
  fraction : t.core.regs 3=((⟨(p.y1.raw >>> 7) &&& 65535⟩ : Fixed).raw.toBitVec)
  startX : t.core.regs 6=p.x1.raw.toBitVec
  startY : t.core.regs 7=p.y1.raw.toBitVec
  startBlockY : t.core.regs 1=p.startBlockY.toBitVec
  endBlockY : t.core.regs 2=p.endBlockY.toBitVec
  comparison : t.flags=some (compare32 p.endBlockY.toBitVec p.startBlockY.toBitVec)
  stack : t.core.regs 4=s.regs 4
  pc : t.pc=0x2ca10

theorem live (s : X86Memory.State) (p : Collision.PathStart) (portion stride : Fixed)
    (h : Inputs s p portion stride) : Ready s (result s) p portion stride := by
  have value : intercept s=(Collision.pathFirstIntercept p.y1 portion stride).raw.toBitVec := by
    simp only [intercept,shifted,product,mulWord,h.startY,h.portionReg,h.strideReg]
    rfl
  constructor <;> simp [result,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,
    multiply,put,write,eax,edx,ebx,m14,m4,m1,load_store,value,
    h.startX,h.startY,h.endX,h.endY,h.portionReg,h.strideReg,h.startBlockY,h.endBlockY,shifted]
  all_goals rfl

/-- Reads outside the three written stack words retain their original values. -/
theorem frame (s : X86Memory.State) (a : Word)
    (safe : ∀ off∈[(4#32),40,44], Apart a (s.regs 4+off)) :
    load32 (result s).core.memory a=load32 s.memory a := by
  change load32 (m14 s) a=_
  unfold m14 m4 m1
  repeat rw [load_store_apart _ _ _ _ (safe _ (by simp))]

end Doom.Proofs.OriginalPathIntercept
