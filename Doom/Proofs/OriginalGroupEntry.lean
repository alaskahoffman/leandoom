import Doom.Proofs.OriginalGroupAllocation
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalGroupEntry
open Verification X86 X86Memory X86Control BlockSummary
def entryBytes : List UInt8 := [0x8b,0x2d,0x48,0xc1,0x2,0x0,0x89,0xc6,0x31,0xc0,0x8b,0x15,0x4c,0xc1,0x2,0x0,0x89,0x44,0x24,0x10,0x85,0xd2,0xf,0x8e,0x37,0x1,0x0,0x0,0x89,0xe0,0xe8,0x5f,0x5b,0xff,0xff]
def clearBytes : List UInt8 := [0x52,0xc7,0x40,0xc,0x0,0x0,0x0,0x80,0xc7,0x40,0x8,0xff,0xff,0xff,0x7f,0x8b,0x50,0xc,0x89,0x10,0x8b,0x50,0x8,0x89,0x50,0x4,0x5a,0xc3]
def bytesProgram (entry clear : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2e63e≤pc ∧ pc<0x2e661 then X86Routine.decodeAt entry (pc-0x2e63e)
  else if 0x241c0≤pc ∧ pc<0x241dc then X86Routine.decodeAt clear (pc-0x241c0) else none
def program := bytesProgram entryBytes clearBytes
def listed : X86Routine.Program
  | 0x2e63e => some (.control (.block (.load 5 ⟨none,none,0,0x2c148⟩)),6)
  | 0x2e644 => some (.control (.block (.legacy (.mov 6 0))),2)
  | 0x2e646 => some (.xorRegister 0 0,2)
  | 0x2e648 => some (.control (.block (.load 2 ⟨none,none,0,0x2c14c⟩)),6)
  | 0x2e64e => some (.control (.block (.store ⟨some 4,none,0,16⟩ 0)),4)
  | 0x2e652 => some (.control (.testWord 2 2),2)
  | 0x2e654 => some (.jumpSigned 1 311,6)
  | 0x2e65a => some (.control (.block (.legacy (.mov 0 4))),2)
  | 0x2e65c => some (.call (-42145),5)
  | 0x241c0 => some (.push 2,1)
  | 0x241c1 => some (.storeImmediate ⟨some 0,none,0,12⟩ 0x80000000,7)
  | 0x241c8 => some (.storeImmediate ⟨some 0,none,0,8⟩ 0x7fffffff,7)
  | 0x241cf => some (.control (.block (.legacy (.load 2 0 12))),3)
  | 0x241d2 => some (.control (.block (.store ⟨some 0,none,0,0⟩ 2)),2)
  | 0x241d4 => some (.control (.block (.legacy (.load 2 0 8))),3)
  | 0x241d7 => some (.control (.block (.store ⟨some 0,none,0,4⟩ 2)),3)
  | 0x241da => some (.pop 2,1)
  | 0x241db => some (.ret,1)
  | _ => none
theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def sector (s : X86Memory.State) := load32 s.memory 0x2c148
def sectorCount (s : X86Memory.State) := load32 s.memory 0x2c14c
def prepared (s : X86Memory.State) : X86Memory.State :=
  {put (put (put (put s 5 (sector s)) 6 (s.regs 0)) 0 0) 2 (sectorCount s) with
    memory := store32 s.memory (s.regs 4+16) 0}
def boxMemory (s : X86Memory.State) : Memory :=
  let m := store32 (prepared s).memory (s.regs 4-4) 0x2e661
  let m := store32 m (s.regs 4-8) (sectorCount s)
  let m := store32 m (s.regs 4+12) 0x80000000
  let m := store32 m (s.regs 4+8) 0x7fffffff
  let m := store32 m (s.regs 4) 0x80000000
  store32 m (s.regs 4+4) 0x7fffffff
def result (s : X86Memory.State) : X86Control.State :=
  if (sectorCount s).toInt≤0 then ⟨prepared s,some (logical32 (sectorCount s)),0x2e791⟩
  else ⟨{put (prepared s) 0 (s.regs 4) with memory:=boxMemory s},some (logical32 (sectorCount s)),0x2e661⟩
private theorem offset_apart (sp a b : Word) (h : Apart a b) : Apart (sp+a) (sp+b) := by
  intro i j eq
  rw [BitVec.add_assoc,BitVec.add_assoc] at eq
  exact h i j ((BitVec.add_right_inj sp).mp eq)
@[local simp] private theorem slot_0_4 (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(0x4#32)) v) sp=load32 m sp := by
  simpa only [BitVec.add_zero] using load_store_apart m (sp+(0x4#32)) (sp+(0x0#32)) v
    (offset_apart sp (0x0#32) (0x4#32) (by unfold Apart; decide))
@[local simp] private theorem slot_0_8 (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(0x8#32)) v) sp=load32 m sp := by
  simpa only [BitVec.add_zero] using load_store_apart m (sp+(0x8#32)) (sp+(0x0#32)) v
    (offset_apart sp (0x0#32) (0x8#32) (by unfold Apart; decide))
@[local simp] private theorem slot_0_c (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(0xc#32)) v) sp=load32 m sp := by
  simpa only [BitVec.add_zero] using load_store_apart m (sp+(0xc#32)) (sp+(0x0#32)) v
    (offset_apart sp (0x0#32) (0xc#32) (by unfold Apart; decide))
@[local simp] private theorem slot_0_10 (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(0x10#32)) v) sp=load32 m sp := by
  simpa only [BitVec.add_zero] using load_store_apart m (sp+(0x10#32)) (sp+(0x0#32)) v
    (offset_apart sp (0x0#32) (0x10#32) (by unfold Apart; decide))
@[local simp] private theorem slot_0_fffffff8 (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(0xfffffff8#32)) v) sp=load32 m sp := by
  simpa only [BitVec.add_zero] using load_store_apart m (sp+(0xfffffff8#32)) (sp+(0x0#32)) v
    (offset_apart sp (0x0#32) (0xfffffff8#32) (by unfold Apart; decide))
@[local simp] private theorem slot_0_fffffffc (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(0xfffffffc#32)) v) sp=load32 m sp := by
  simpa only [BitVec.add_zero] using load_store_apart m (sp+(0xfffffffc#32)) (sp+(0x0#32)) v
    (offset_apart sp (0x0#32) (0xfffffffc#32) (by unfold Apart; decide))
@[local simp] private theorem slot_4_0 (m : Memory) (sp v : Word) :
    load32 (store32 m sp v) (sp+(0x4#32))=load32 m (sp+(0x4#32)) := by
  simpa only [BitVec.add_zero] using load_store_apart m (sp+(0x0#32)) (sp+(0x4#32)) v
    (offset_apart sp (0x4#32) (0x0#32) (by unfold Apart; decide))
@[local simp] private theorem slot_4_8 (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(0x8#32)) v) (sp+(0x4#32))=load32 m (sp+(0x4#32)) := by
  simpa only [BitVec.add_zero] using load_store_apart m (sp+(0x8#32)) (sp+(0x4#32)) v
    (offset_apart sp (0x4#32) (0x8#32) (by unfold Apart; decide))
@[local simp] private theorem slot_4_c (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(0xc#32)) v) (sp+(0x4#32))=load32 m (sp+(0x4#32)) := by
  simpa only [BitVec.add_zero] using load_store_apart m (sp+(0xc#32)) (sp+(0x4#32)) v
    (offset_apart sp (0x4#32) (0xc#32) (by unfold Apart; decide))
@[local simp] private theorem slot_4_10 (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(0x10#32)) v) (sp+(0x4#32))=load32 m (sp+(0x4#32)) := by
  simpa only [BitVec.add_zero] using load_store_apart m (sp+(0x10#32)) (sp+(0x4#32)) v
    (offset_apart sp (0x4#32) (0x10#32) (by unfold Apart; decide))
@[local simp] private theorem slot_4_fffffff8 (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(0xfffffff8#32)) v) (sp+(0x4#32))=load32 m (sp+(0x4#32)) := by
  simpa only [BitVec.add_zero] using load_store_apart m (sp+(0xfffffff8#32)) (sp+(0x4#32)) v
    (offset_apart sp (0x4#32) (0xfffffff8#32) (by unfold Apart; decide))
@[local simp] private theorem slot_4_fffffffc (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(0xfffffffc#32)) v) (sp+(0x4#32))=load32 m (sp+(0x4#32)) := by
  simpa only [BitVec.add_zero] using load_store_apart m (sp+(0xfffffffc#32)) (sp+(0x4#32)) v
    (offset_apart sp (0x4#32) (0xfffffffc#32) (by unfold Apart; decide))
@[local simp] private theorem slot_8_0 (m : Memory) (sp v : Word) :
    load32 (store32 m sp v) (sp+(0x8#32))=load32 m (sp+(0x8#32)) := by
  simpa only [BitVec.add_zero] using load_store_apart m (sp+(0x0#32)) (sp+(0x8#32)) v
    (offset_apart sp (0x8#32) (0x0#32) (by unfold Apart; decide))
@[local simp] private theorem slot_8_4 (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(0x4#32)) v) (sp+(0x8#32))=load32 m (sp+(0x8#32)) := by
  simpa only [BitVec.add_zero] using load_store_apart m (sp+(0x4#32)) (sp+(0x8#32)) v
    (offset_apart sp (0x8#32) (0x4#32) (by unfold Apart; decide))
@[local simp] private theorem slot_8_c (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(0xc#32)) v) (sp+(0x8#32))=load32 m (sp+(0x8#32)) := by
  simpa only [BitVec.add_zero] using load_store_apart m (sp+(0xc#32)) (sp+(0x8#32)) v
    (offset_apart sp (0x8#32) (0xc#32) (by unfold Apart; decide))
@[local simp] private theorem slot_8_10 (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(0x10#32)) v) (sp+(0x8#32))=load32 m (sp+(0x8#32)) := by
  simpa only [BitVec.add_zero] using load_store_apart m (sp+(0x10#32)) (sp+(0x8#32)) v
    (offset_apart sp (0x8#32) (0x10#32) (by unfold Apart; decide))
@[local simp] private theorem slot_8_fffffff8 (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(0xfffffff8#32)) v) (sp+(0x8#32))=load32 m (sp+(0x8#32)) := by
  simpa only [BitVec.add_zero] using load_store_apart m (sp+(0xfffffff8#32)) (sp+(0x8#32)) v
    (offset_apart sp (0x8#32) (0xfffffff8#32) (by unfold Apart; decide))
@[local simp] private theorem slot_8_fffffffc (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(0xfffffffc#32)) v) (sp+(0x8#32))=load32 m (sp+(0x8#32)) := by
  simpa only [BitVec.add_zero] using load_store_apart m (sp+(0xfffffffc#32)) (sp+(0x8#32)) v
    (offset_apart sp (0x8#32) (0xfffffffc#32) (by unfold Apart; decide))
@[local simp] private theorem slot_c_0 (m : Memory) (sp v : Word) :
    load32 (store32 m sp v) (sp+(0xc#32))=load32 m (sp+(0xc#32)) := by
  simpa only [BitVec.add_zero] using load_store_apart m (sp+(0x0#32)) (sp+(0xc#32)) v
    (offset_apart sp (0xc#32) (0x0#32) (by unfold Apart; decide))
@[local simp] private theorem slot_c_4 (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(0x4#32)) v) (sp+(0xc#32))=load32 m (sp+(0xc#32)) := by
  simpa only [BitVec.add_zero] using load_store_apart m (sp+(0x4#32)) (sp+(0xc#32)) v
    (offset_apart sp (0xc#32) (0x4#32) (by unfold Apart; decide))
@[local simp] private theorem slot_c_8 (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(0x8#32)) v) (sp+(0xc#32))=load32 m (sp+(0xc#32)) := by
  simpa only [BitVec.add_zero] using load_store_apart m (sp+(0x8#32)) (sp+(0xc#32)) v
    (offset_apart sp (0xc#32) (0x8#32) (by unfold Apart; decide))
@[local simp] private theorem slot_c_10 (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(0x10#32)) v) (sp+(0xc#32))=load32 m (sp+(0xc#32)) := by
  simpa only [BitVec.add_zero] using load_store_apart m (sp+(0x10#32)) (sp+(0xc#32)) v
    (offset_apart sp (0xc#32) (0x10#32) (by unfold Apart; decide))
@[local simp] private theorem slot_c_fffffff8 (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(0xfffffff8#32)) v) (sp+(0xc#32))=load32 m (sp+(0xc#32)) := by
  simpa only [BitVec.add_zero] using load_store_apart m (sp+(0xfffffff8#32)) (sp+(0xc#32)) v
    (offset_apart sp (0xc#32) (0xfffffff8#32) (by unfold Apart; decide))
@[local simp] private theorem slot_c_fffffffc (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(0xfffffffc#32)) v) (sp+(0xc#32))=load32 m (sp+(0xc#32)) := by
  simpa only [BitVec.add_zero] using load_store_apart m (sp+(0xfffffffc#32)) (sp+(0xc#32)) v
    (offset_apart sp (0xc#32) (0xfffffffc#32) (by unfold Apart; decide))
@[local simp] private theorem slot_10_0 (m : Memory) (sp v : Word) :
    load32 (store32 m sp v) (sp+(0x10#32))=load32 m (sp+(0x10#32)) := by
  simpa only [BitVec.add_zero] using load_store_apart m (sp+(0x0#32)) (sp+(0x10#32)) v
    (offset_apart sp (0x10#32) (0x0#32) (by unfold Apart; decide))
@[local simp] private theorem slot_10_4 (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(0x4#32)) v) (sp+(0x10#32))=load32 m (sp+(0x10#32)) := by
  simpa only [BitVec.add_zero] using load_store_apart m (sp+(0x4#32)) (sp+(0x10#32)) v
    (offset_apart sp (0x10#32) (0x4#32) (by unfold Apart; decide))
@[local simp] private theorem slot_10_8 (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(0x8#32)) v) (sp+(0x10#32))=load32 m (sp+(0x10#32)) := by
  simpa only [BitVec.add_zero] using load_store_apart m (sp+(0x8#32)) (sp+(0x10#32)) v
    (offset_apart sp (0x10#32) (0x8#32) (by unfold Apart; decide))
@[local simp] private theorem slot_10_c (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(0xc#32)) v) (sp+(0x10#32))=load32 m (sp+(0x10#32)) := by
  simpa only [BitVec.add_zero] using load_store_apart m (sp+(0xc#32)) (sp+(0x10#32)) v
    (offset_apart sp (0x10#32) (0xc#32) (by unfold Apart; decide))
@[local simp] private theorem slot_10_fffffff8 (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(0xfffffff8#32)) v) (sp+(0x10#32))=load32 m (sp+(0x10#32)) := by
  simpa only [BitVec.add_zero] using load_store_apart m (sp+(0xfffffff8#32)) (sp+(0x10#32)) v
    (offset_apart sp (0x10#32) (0xfffffff8#32) (by unfold Apart; decide))
@[local simp] private theorem slot_10_fffffffc (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(0xfffffffc#32)) v) (sp+(0x10#32))=load32 m (sp+(0x10#32)) := by
  simpa only [BitVec.add_zero] using load_store_apart m (sp+(0xfffffffc#32)) (sp+(0x10#32)) v
    (offset_apart sp (0x10#32) (0xfffffffc#32) (by unfold Apart; decide))
@[local simp] private theorem slot_fffffff8_0 (m : Memory) (sp v : Word) :
    load32 (store32 m sp v) (sp+(0xfffffff8#32))=load32 m (sp+(0xfffffff8#32)) := by
  simpa only [BitVec.add_zero] using load_store_apart m (sp+(0x0#32)) (sp+(0xfffffff8#32)) v
    (offset_apart sp (0xfffffff8#32) (0x0#32) (by unfold Apart; decide))
@[local simp] private theorem slot_fffffff8_4 (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(0x4#32)) v) (sp+(0xfffffff8#32))=load32 m (sp+(0xfffffff8#32)) := by
  simpa only [BitVec.add_zero] using load_store_apart m (sp+(0x4#32)) (sp+(0xfffffff8#32)) v
    (offset_apart sp (0xfffffff8#32) (0x4#32) (by unfold Apart; decide))
@[local simp] private theorem slot_fffffff8_8 (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(0x8#32)) v) (sp+(0xfffffff8#32))=load32 m (sp+(0xfffffff8#32)) := by
  simpa only [BitVec.add_zero] using load_store_apart m (sp+(0x8#32)) (sp+(0xfffffff8#32)) v
    (offset_apart sp (0xfffffff8#32) (0x8#32) (by unfold Apart; decide))
@[local simp] private theorem slot_fffffff8_c (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(0xc#32)) v) (sp+(0xfffffff8#32))=load32 m (sp+(0xfffffff8#32)) := by
  simpa only [BitVec.add_zero] using load_store_apart m (sp+(0xc#32)) (sp+(0xfffffff8#32)) v
    (offset_apart sp (0xfffffff8#32) (0xc#32) (by unfold Apart; decide))
@[local simp] private theorem slot_fffffff8_10 (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(0x10#32)) v) (sp+(0xfffffff8#32))=load32 m (sp+(0xfffffff8#32)) := by
  simpa only [BitVec.add_zero] using load_store_apart m (sp+(0x10#32)) (sp+(0xfffffff8#32)) v
    (offset_apart sp (0xfffffff8#32) (0x10#32) (by unfold Apart; decide))
@[local simp] private theorem slot_fffffff8_fffffffc (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(0xfffffffc#32)) v) (sp+(0xfffffff8#32))=load32 m (sp+(0xfffffff8#32)) := by
  simpa only [BitVec.add_zero] using load_store_apart m (sp+(0xfffffffc#32)) (sp+(0xfffffff8#32)) v
    (offset_apart sp (0xfffffff8#32) (0xfffffffc#32) (by unfold Apart; decide))
@[local simp] private theorem slot_fffffffc_0 (m : Memory) (sp v : Word) :
    load32 (store32 m sp v) (sp+(0xfffffffc#32))=load32 m (sp+(0xfffffffc#32)) := by
  simpa only [BitVec.add_zero] using load_store_apart m (sp+(0x0#32)) (sp+(0xfffffffc#32)) v
    (offset_apart sp (0xfffffffc#32) (0x0#32) (by unfold Apart; decide))
@[local simp] private theorem slot_fffffffc_4 (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(0x4#32)) v) (sp+(0xfffffffc#32))=load32 m (sp+(0xfffffffc#32)) := by
  simpa only [BitVec.add_zero] using load_store_apart m (sp+(0x4#32)) (sp+(0xfffffffc#32)) v
    (offset_apart sp (0xfffffffc#32) (0x4#32) (by unfold Apart; decide))
@[local simp] private theorem slot_fffffffc_8 (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(0x8#32)) v) (sp+(0xfffffffc#32))=load32 m (sp+(0xfffffffc#32)) := by
  simpa only [BitVec.add_zero] using load_store_apart m (sp+(0x8#32)) (sp+(0xfffffffc#32)) v
    (offset_apart sp (0xfffffffc#32) (0x8#32) (by unfold Apart; decide))
@[local simp] private theorem slot_fffffffc_c (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(0xc#32)) v) (sp+(0xfffffffc#32))=load32 m (sp+(0xfffffffc#32)) := by
  simpa only [BitVec.add_zero] using load_store_apart m (sp+(0xc#32)) (sp+(0xfffffffc#32)) v
    (offset_apart sp (0xfffffffc#32) (0xc#32) (by unfold Apart; decide))
@[local simp] private theorem slot_fffffffc_10 (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(0x10#32)) v) (sp+(0xfffffffc#32))=load32 m (sp+(0xfffffffc#32)) := by
  simpa only [BitVec.add_zero] using load_store_apart m (sp+(0x10#32)) (sp+(0xfffffffc#32)) v
    (offset_apart sp (0xfffffffc#32) (0x10#32) (by unfold Apart; decide))
@[local simp] private theorem slot_fffffffc_fffffff8 (m : Memory) (sp v : Word) :
    load32 (store32 m (sp+(0xfffffff8#32)) v) (sp+(0xfffffffc#32))=load32 m (sp+(0xfffffffc#32)) := by
  simpa only [BitVec.add_zero] using load_store_apart m (sp+(0xfffffff8#32)) (sp+(0xfffffffc#32)) v
    (offset_apart sp (0xfffffffc#32) (0xfffffff8#32) (by unfold Apart; decide))
@[local simp] private theorem step_2e63e (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e661,0x2e791] (n+1) ⟨s,f,0x2e63e⟩ =
      (X86Routine.execute (.control (.block (.load 5 ⟨none,none,0,0x2c148⟩))) ⟨s,f,0x2e644⟩).bind (X86Routine.run listed [0x2e661,0x2e791] n) := by rfl
@[local simp] private theorem step_2e644 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e661,0x2e791] (n+1) ⟨s,f,0x2e644⟩ =
      (X86Routine.execute (.control (.block (.legacy (.mov 6 0)))) ⟨s,f,0x2e646⟩).bind (X86Routine.run listed [0x2e661,0x2e791] n) := by rfl
@[local simp] private theorem step_2e646 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e661,0x2e791] (n+1) ⟨s,f,0x2e646⟩ =
      (X86Routine.execute (.xorRegister 0 0) ⟨s,f,0x2e648⟩).bind (X86Routine.run listed [0x2e661,0x2e791] n) := by rfl
@[local simp] private theorem step_2e648 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e661,0x2e791] (n+1) ⟨s,f,0x2e648⟩ =
      (X86Routine.execute (.control (.block (.load 2 ⟨none,none,0,0x2c14c⟩))) ⟨s,f,0x2e64e⟩).bind (X86Routine.run listed [0x2e661,0x2e791] n) := by rfl
@[local simp] private theorem step_2e64e (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e661,0x2e791] (n+1) ⟨s,f,0x2e64e⟩ =
      (X86Routine.execute (.control (.block (.store ⟨some 4,none,0,16⟩ 0))) ⟨s,f,0x2e652⟩).bind (X86Routine.run listed [0x2e661,0x2e791] n) := by rfl
@[local simp] private theorem step_2e652 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e661,0x2e791] (n+1) ⟨s,f,0x2e652⟩ =
      (X86Routine.execute (.control (.testWord 2 2)) ⟨s,f,0x2e654⟩).bind (X86Routine.run listed [0x2e661,0x2e791] n) := by rfl
@[local simp] private theorem step_2e654 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e661,0x2e791] (n+1) ⟨s,f,0x2e654⟩ =
      (X86Routine.execute (.jumpSigned 1 311) ⟨s,f,0x2e65a⟩).bind (X86Routine.run listed [0x2e661,0x2e791] n) := by rfl
@[local simp] private theorem step_2e65a (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e661,0x2e791] (n+1) ⟨s,f,0x2e65a⟩ =
      (X86Routine.execute (.control (.block (.legacy (.mov 0 4)))) ⟨s,f,0x2e65c⟩).bind (X86Routine.run listed [0x2e661,0x2e791] n) := by rfl
private theorem one_step (p : X86Routine.Program) (exits : List Nat) (n : Nat)
    (s : X86Control.State) (op : X86Routine.Op) (len : Nat)
    (active : s.pc∉exits) (decode : p s.pc=some (op,len)) :
    X86Routine.run p exits (n+1) s=
      (X86Routine.execute op {s with pc:=s.pc+len}).bind (X86Routine.run p exits n) := by
  rw [X86Routine.run,if_neg active,decode]
  rfl
@[local simp] private theorem step_2e65c (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e661,0x2e791] (n+1) ⟨s,f,0x2e65c⟩ =
      (X86Routine.execute (.call (-42145)) ⟨s,f,0x2e661⟩).bind (X86Routine.run listed [0x2e661,0x2e791] n) := by
  exact one_step listed [0x2e661,0x2e791] n ⟨s,f,0x2e65c⟩ (.call (-42145)) 5 (by change (0x2e65c : Nat)∉[0x2e661,0x2e791]; decide) rfl
@[local simp] private theorem step_241c0 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e661,0x2e791] (n+1) ⟨s,f,0x241c0⟩ =
      (X86Routine.execute (.push 2) ⟨s,f,0x241c1⟩).bind (X86Routine.run listed [0x2e661,0x2e791] n) := by rfl
@[local simp] private theorem step_241c1 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e661,0x2e791] (n+1) ⟨s,f,0x241c1⟩ =
      (X86Routine.execute (.storeImmediate ⟨some 0,none,0,12⟩ 0x80000000) ⟨s,f,0x241c8⟩).bind (X86Routine.run listed [0x2e661,0x2e791] n) := by rfl
@[local simp] private theorem step_241c8 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e661,0x2e791] (n+1) ⟨s,f,0x241c8⟩ =
      (X86Routine.execute (.storeImmediate ⟨some 0,none,0,8⟩ 0x7fffffff) ⟨s,f,0x241cf⟩).bind (X86Routine.run listed [0x2e661,0x2e791] n) := by rfl
@[local simp] private theorem step_241cf (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e661,0x2e791] (n+1) ⟨s,f,0x241cf⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 2 0 12)))) ⟨s,f,0x241d2⟩).bind (X86Routine.run listed [0x2e661,0x2e791] n) := by rfl
@[local simp] private theorem step_241d2 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e661,0x2e791] (n+1) ⟨s,f,0x241d2⟩ =
      (X86Routine.execute (.control (.block (.store ⟨some 0,none,0,0⟩ 2))) ⟨s,f,0x241d4⟩).bind (X86Routine.run listed [0x2e661,0x2e791] n) := by rfl
@[local simp] private theorem step_241d4 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e661,0x2e791] (n+1) ⟨s,f,0x241d4⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 2 0 8)))) ⟨s,f,0x241d7⟩).bind (X86Routine.run listed [0x2e661,0x2e791] n) := by rfl
@[local simp] private theorem step_241d7 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e661,0x2e791] (n+1) ⟨s,f,0x241d7⟩ =
      (X86Routine.execute (.control (.block (.store ⟨some 0,none,0,4⟩ 2))) ⟨s,f,0x241da⟩).bind (X86Routine.run listed [0x2e661,0x2e791] n) := by rfl
@[local simp] private theorem step_241da (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e661,0x2e791] (n+1) ⟨s,f,0x241da⟩ =
      (X86Routine.execute (.pop 2) ⟨s,f,0x241db⟩).bind (X86Routine.run listed [0x2e661,0x2e791] n) := by rfl
@[local simp] private theorem step_241db (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e661,0x2e791] (n+1) ⟨s,f,0x241db⟩ =
      (X86Routine.execute (.ret) ⟨s,f,0x241dc⟩).bind (X86Routine.run listed [0x2e661,0x2e791] n) := by rfl
@[local simp] private theorem stop_2e661 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e661,0x2e791] n ⟨s,f,0x2e661⟩=some ⟨s,f,0x2e661⟩ := by cases n <;> rfl
@[local simp] private theorem stop_2e791 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e661,0x2e791] n ⟨s,f,0x2e791⟩=some ⟨s,f,0x2e791⟩ := by cases n <;> rfl
/-- Summarize the CALL and the complete helper separately to keep proof terms small. -/
def clearMemory (s : X86Memory.State) : Memory :=
  let m := store32 s.memory (s.regs 4-4) 0x2e661
  let m := store32 m (s.regs 4-8) (s.regs 2)
  let m := store32 m (s.regs 4+12) 0x80000000
  let m := store32 m (s.regs 4+8) 0x7fffffff
  let m := store32 m (s.regs 4) 0x80000000
  store32 m (s.regs 4+4) 0x7fffffff
def callState (s : X86Memory.State) := X86Routine.pushWord (put s 0 (s.regs 4)) 0x2e661
def firstState (s : X86Memory.State) : X86Memory.State :=
  let t := X86Routine.pushWord (callState s) (s.regs 2)
  let m := store32 t.memory (s.regs 4+12) 0x80000000
  {t with memory:=store32 m (s.regs 4+8) 0x7fffffff}
def copyState (s : X86Memory.State) : X86Memory.State :=
  let v := load32 s.memory (s.regs 0+12)
  let m := store32 s.memory (s.regs 0) v
  let w := load32 m (s.regs 0+8)
  {put s 2 w with memory:=store32 m (s.regs 0+4) w}
def returnState (s : X86Memory.State) (f : Option Flags) : X86Control.State :=
  ⟨put (put s 2 (load32 s.memory (s.regs 4))) 4 (s.regs 4+8),f,
    (load32 s.memory (s.regs 4+4)).toNat⟩
private theorem first_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run listed [0x241cf] 4 ⟨put s 0 (s.regs 4),f,0x2e65c⟩=
      some ⟨firstState s,f,0x241cf⟩ := by
  simp only [X86Routine.run]
  simp [listed,X86Routine.execute,X86Routine.pushWord,firstState,callState,
    X86Block.Address.eval,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc]
private theorem copy_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run listed [0x241da] 4 ⟨s,f,0x241cf⟩=some ⟨copyState s,f,0x241da⟩ := by
  simp only [X86Routine.run]
  simp [listed,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
    X86Block.Address.eval,X86.execute,blockPreservesFlags,copyState,put,write]
  funext r
  by_cases h : r=2 <;> simp [write,h]
private theorem return_execution (s : X86Memory.State) (f : Option Flags)
    (ret : load32 s.memory (s.regs 4+(4#32))=(0x2e661#32)) :
    X86Routine.run listed [0x2e661,0x2e791] 2 ⟨s,f,0x241da⟩=some (returnState s f) := by
  simp [X86Routine.execute,returnState,put,write,BitVec.add_assoc]
  rw [ret]
  simp
  funext r
  by_cases h : r=4 <;> simp [write,h]
private theorem transfer {exits n s t}
    (h : X86Routine.run listed exits n s=some t) :
    ∃ k, k≤n ∧ X86Routine.Prefix listed [0x2e661,0x2e791] k s t := by
  obtain ⟨k,hk,path,_⟩ := X86Routine.run_path h
  refine ⟨k,hk,path.transfer _ _ (by intros; rfl) ?_⟩
  intro pc h member
  simp at member
  rcases member with rfl|rfl <;> exact h (by decide)
private theorem helper_memory (s : X86Memory.State) :
    (copyState (firstState s)).memory=clearMemory s := by
  simp [copyState,firstState,callState,clearMemory,X86Routine.pushWord,
    put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,load_store]
private theorem helper_registers (s : X86Memory.State) :
    (copyState (firstState s)).regs=
      write (write (write s.regs 0 (s.regs 4)) 4 (s.regs 4-8)) 2 0x7fffffff := by
  simp [copyState,firstState,callState,X86Routine.pushWord,
    put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,load_store]
  funext r
  by_cases h : r=4 <;> simp [write,h]
private theorem helper_return (s : X86Memory.State) :
    load32 (copyState (firstState s)).memory ((copyState (firstState s)).regs 4+4)=0x2e661 := by
  rw [helper_memory,helper_registers]
  simp [clearMemory,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,load_store]
private theorem helper_result (s : X86Memory.State) (f : Option Flags) :
    returnState (copyState (firstState s)) f=
      ⟨{put s 0 (s.regs 4) with memory:=clearMemory s},f,0x2e661⟩ := by
  unfold returnState
  rw [helper_return]
  have regs := helper_registers s
  have mem := helper_memory s
  cases h : copyState (firstState s) with
  | mk r m =>
    simp only [h] at regs mem
    simp only [regs,mem]
    simp [clearMemory,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,load_store]
    funext r
    by_cases h0 : r=0 <;> by_cases h2 : r=2 <;> by_cases h4 : r=4 <;> simp [write,h0,h2,h4]
@[local simp] theorem clear_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run listed [0x2e661,0x2e791] 10 ⟨put s 0 (s.regs 4),f,0x2e65c⟩=
      some ⟨{put s 0 (s.regs 4) with memory:=clearMemory s},f,0x2e661⟩ := by
  obtain ⟨a,ha,pa⟩ := transfer (first_execution s f)
  obtain ⟨b,hb,pb⟩ := transfer (copy_execution (firstState s) f)
  have tail := return_execution (copyState (firstState s)) f (helper_return s)
  rw [helper_result] at tail
  exact pa.finish (pb.finish tail 6 (by omega)) 10 (by omega)

def callerResult (s : X86Memory.State) : X86Control.State :=
  if (sectorCount s).toInt≤0 then ⟨prepared s,some (logical32 (sectorCount s)),0x2e791⟩
  else ⟨put (prepared s) 0 (s.regs 4),some (logical32 (sectorCount s)),0x2e65c⟩
private theorem caller_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run listed [0x2e65c,0x2e791] 8 ⟨s,f,0x2e63e⟩=some (callerResult s) := by
  by_cases positive : 0<(load32 s.memory (0x2c14c#32)).toInt
  all_goals have branch : (load32 s.memory (0x2c14c#32)).toInt≤0 ↔ ¬0<(load32 s.memory (0x2c14c#32)).toInt := by omega
  all_goals simp only [X86Routine.run]
  all_goals simp [listed,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
    X86Block.Address.eval,X86.execute,blockPreservesFlags,callerResult,
    prepared,sector,sectorCount,PlayerHeight.logical_le,positive,branch,put,write]
theorem execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x2e661,0x2e791] 18 ⟨s,f,0x2e63e⟩=some (result s) := by
  obtain ⟨n,hn,path⟩ := transfer (caller_execution s f)
  have tail : X86Routine.run listed [0x2e661,0x2e791] 10 (callerResult s)=some (result s) := by
    by_cases h : (sectorCount s).toInt≤0
    · simp [callerResult,result,h]
    · simp only [callerResult,result,if_neg h]
      have clear := clear_execution (prepared s) (some (logical32 (sectorCount s)))
      simpa only [prepared,sectorCount,clearMemory,boxMemory,put,write,
        show (4 : Reg)≠0 by decide, show (4 : Reg)≠2 by decide,
        show (4 : Reg)≠5 by decide, show (4 : Reg)≠6 by decide,
        show (2 : Reg)≠0 by decide, show (2 : Reg)≠5 by decide,
        show (2 : Reg)≠6 by decide,↓reduceIte] using clear
  have run := path.finish tail 18 (by omega)
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

/-- The only caller/helper writes: outer index, return/save slots and four box words. -/
def SafeWord (a sp : Word) : Prop :=
  ∀ b∈[sp+16,sp-4,sp-8,sp+12,sp+8,sp,sp+4], Apart a b

theorem frame (s : X86Memory.State) (a : Word) (safe : SafeWord a (s.regs 4)) :
    load32 (result s).core.memory a=load32 s.memory a := by
  have h0 := safe _ (by simp : s.regs 4+16∈[s.regs 4+16,s.regs 4-4,s.regs 4-8,s.regs 4+12,s.regs 4+8,s.regs 4,s.regs 4+4])
  have h1 := safe _ (by simp : s.regs 4-4∈[s.regs 4+16,s.regs 4-4,s.regs 4-8,s.regs 4+12,s.regs 4+8,s.regs 4,s.regs 4+4])
  have h2 := safe _ (by simp : s.regs 4-8∈[s.regs 4+16,s.regs 4-4,s.regs 4-8,s.regs 4+12,s.regs 4+8,s.regs 4,s.regs 4+4])
  have h3 := safe _ (by simp : s.regs 4+12∈[s.regs 4+16,s.regs 4-4,s.regs 4-8,s.regs 4+12,s.regs 4+8,s.regs 4,s.regs 4+4])
  have h4 := safe _ (by simp : s.regs 4+8∈[s.regs 4+16,s.regs 4-4,s.regs 4-8,s.regs 4+12,s.regs 4+8,s.regs 4,s.regs 4+4])
  have h5 := safe _ (by simp : s.regs 4∈[s.regs 4+16,s.regs 4-4,s.regs 4-8,s.regs 4+12,s.regs 4+8,s.regs 4,s.regs 4+4])
  have h6 := safe _ (by simp : s.regs 4+4∈[s.regs 4+16,s.regs 4-4,s.regs 4-8,s.regs 4+12,s.regs 4+8,s.regs 4,s.regs 4+4])
  simp only [result]
  split
  · exact load_store_apart _ _ _ _ h0
  · change load32 (boxMemory s) a=_
    unfold boxMemory
    rw [load_store_apart _ _ _ _ h6,load_store_apart _ _ _ _ h5,
      load_store_apart _ _ _ _ h4,load_store_apart _ _ _ _ h3,
      load_store_apart _ _ _ _ h2,load_store_apart _ _ _ _ h1]
    exact load_store_apart _ _ _ _ h0

theorem registers (s : X86Memory.State) :
    (result s).core.regs 5=sector s ∧ (result s).core.regs 6=s.regs 0 ∧
    (result s).core.regs 4=s.regs 4 := by
  by_cases h : (sectorCount s).toInt≤0 <;> simp [result,h,prepared,put,write]

theorem positive_pc (s : X86Memory.State) (h : 0<(sectorCount s).toInt) : (result s).pc=0x2e661 := by
  simp only [result,if_neg (show ¬(sectorCount s).toInt≤0 by omega)]

theorem box_ready (s : X86Memory.State) (h : 0<(sectorCount s).toInt) :
    load32 (result s).core.memory (s.regs 4)=0x80000000 ∧
    load32 (result s).core.memory (s.regs 4+4)=0x7fffffff ∧
    load32 (result s).core.memory (s.regs 4+8)=0x7fffffff ∧
    load32 (result s).core.memory (s.regs 4+12)=0x80000000 ∧
    load32 (result s).core.memory (s.regs 4+16)=0 := by
  simp only [result,if_neg (show ¬(sectorCount s).toInt≤0 by omega)]
  simp [boxMemory,prepared,put,BitVec.sub_eq_add_neg,load_store]

end Doom.Proofs.OriginalGroupEntry
