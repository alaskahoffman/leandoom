import Doom.Proofs.E1M1AimSidePublish
import Doom.Verification.X86FillRoutine
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1AimSideMemset
open Verification X86 X86Memory X86Control BlockSummary
/-! Execute the actual wrapper and first aligned helper path through the second
nested CALL. The word filler, its output and all returns are still open. -/
def memsetBytes : List UInt8 := [0x50,0x51,0x8a,0xf2,0xc1,0xe2,0x8,0x8a,0xd6,0xc1,0xe2,0x8,0x8a,0xd6,0x8b,0xcb,0xe8,0x5b,0x1a,0x0,0x0,0x59,0x58,0xc3]
def fillBytes : List UInt8 := [0xb,0xc9,0x74,0x2c,0x38,0x10,0xa8,0x3,0x74,0x9,0x88,0x10,0x40,0xc1,0xca,0x8,0x49,0x75,0xf3,0x51,0xc1,0xe9,0x2,0xe8,0x1b,0x0,0x0,0x0,0x59,0x83,0xe1,0x3,0x74,0xe,0x88,0x10,0x49,0x74,0x9,0x88,0x70,0x1,0x49,0x74,0x3,0x88,0x50,0x2,0xc3]
def bytesProgram (wrapper helper : List UInt8) : X86FillRoutine.Program := fun pc =>
  if 0x3fe70≤pc ∧ pc<0x3fe88 then X86FillRoutine.decodeAt wrapper (pc-0x3fe70)
  else if 0x418e0≤pc ∧ pc<0x41911 then X86FillRoutine.decodeAt helper (pc-0x418e0)
  else X86FillRoutine.liftProgram E1M1AimSideAllocate.program pc
def program := bytesProgram memsetBytes fillBytes
abbrev op (i : X86Routine.Op) : X86FillRoutine.Op := .base (.base (.base i))
def listed : X86FillRoutine.Program
  | 0x3fe70 => some (op (.push 0),1)
  | 0x3fe71 => some (op (.push 1),1)
  | 0x3fe72 => some (op (.moveByte 6 2),2)
  | 0x3fe74 => some (op (.control (.block (.legacy (.shl 2 8)))) ,3)
  | 0x3fe77 => some (op (.moveByte 2 6),2)
  | 0x3fe79 => some (op (.control (.block (.legacy (.shl 2 8)))) ,3)
  | 0x3fe7c => some (op (.moveByte 2 6),2)
  | 0x3fe7e => some (op (.control (.block (.legacy (.mov 1 3)))) ,2)
  | 0x3fe80 => some (op (.call 6747),5)
  | 0x418e0 => some (.orRegisters 1 1,2)
  | 0x418e2 => some (op (.control (.jumpZero true 44)),2)
  | 0x418e4 => some (.compareMemoryByte ⟨some 0,none,0,0⟩ 2,2)
  | 0x418e6 => some (op (.testByteImmediate 0 3),2)
  | 0x418e8 => some (op (.control (.jumpZero true 9)),2)
  | 0x418f3 => some (op (.push 1),1)
  | 0x418f4 => some (op (.control (.block (.shr 1 2))),3)
  | 0x418f7 => some (op (.call 27),5)
  | _ => none

theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def fillCalled (s : X86Memory.State) : X86Control.State :=
  ⟨X86Routine.pushWord (put (put
    (X86Routine.pushWord (X86Routine.pushWord s (s.regs 0)) (s.regs 1)) 2 0) 1 11664) 0x3fe85,
    none,0x418e0⟩
def callWords (s : X86Memory.State) : X86Control.State :=
  ⟨X86Routine.pushWord (put (X86Routine.pushWord s 11664) 1 2916) 0x418fc,none,0x41917⟩
def wordsCalled (s : X86Memory.State) := callWords (fillCalled s).core

theorem wrapper_execution (s : X86Memory.State) (f : Option Flags)
    (zero : s.regs 2=0) (size : s.regs 3=11664) :
    X86FillRoutine.Prefix program [] 9 ⟨s,f,0x3fe70⟩ (fillCalled s) := by
  have path : X86FillRoutine.Prefix listed [] 9 ⟨s,f,0x3fe70⟩ (fillCalled s) := by
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (middle:=fillCalled s) (by simp) rfl ?_ (.nil _)
    simp [X86FillRoutine.execute,X86StartupRoutine.execute,X86ByteRoutine.execute,
      X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      X86Routine.pushWord,fillCalled,putByte,readByte,byteReg,put,write,zero,size,
      blockPreservesFlags,show (6:Reg).val=6 from rfl,show Fin.ofNat 8 2=(2:Reg) from rfl]
  exact path.transfer _ [] decoded (by simp)

theorem helper_execution (s : X86Memory.State) (f : Option Flags)
    (count : s.regs 1=11664) (aligned : readByte s.regs 0 &&& 3=0) :
    X86FillRoutine.Prefix program [] 8 ⟨s,f,0x418e0⟩ (callWords s) := by
  simp only [BitVec.ofNat_eq_ofNat] at aligned
  have path : X86FillRoutine.Prefix listed [] 8 ⟨s,f,0x418e0⟩ (callWords s) := by
    refine .step (middle:=⟨s,some (logical32 11664),0x418e2⟩) (by simp) rfl ?_ ?_
    · simp [X86FillRoutine.execute,count,put]
      have regs : write s.regs 1 11664=s.regs := by
        funext r
        by_cases h : r=1 <;> simp [write,h,count]
      simp only [BitVec.ofNat_eq_ofNat] at regs
      rw [regs]
    refine .step (middle:=⟨s,some (logical32 11664),0x418e4⟩) (by simp) rfl ?_ ?_
    · simp [X86FillRoutine.execute,X86StartupRoutine.execute,X86ByteRoutine.execute,
        X86Routine.execute,X86Control.execute,logical32]
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (middle:=⟨s,some (logical8 0),0x418f3⟩) (by simp) rfl ?_ ?_
    · simp [X86FillRoutine.execute,X86StartupRoutine.execute,X86ByteRoutine.execute,
        X86Routine.execute,X86Control.execute,logical8,aligned]
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (middle:=callWords s) (by simp) rfl ?_ (.nil _)
    simp [X86FillRoutine.execute,X86StartupRoutine.execute,X86ByteRoutine.execute,
      X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      X86Routine.pushWord,callWords,put,write,count,blockPreservesFlags]
  exact path.transfer _ [] decoded (by simp)

theorem nested_execution (s : X86Memory.State) (f : Option Flags)
    (zero : s.regs 2=0) (size : s.regs 3=11664)
    (aligned : readByte s.regs 0 &&& 3=0) :
    X86FillRoutine.Prefix program [] 17 ⟨s,f,0x3fe70⟩ (wordsCalled s) := by
  have first := wrapper_execution s f zero size
  have count : (fillCalled s).core.regs 1=11664 := by
    simp [fillCalled,X86Routine.pushWord,put,write]
  have align : readByte (fillCalled s).core.regs 0 &&& 3=0 := by
    simpa [fillCalled,X86Routine.pushWord,readByte,byteReg,put,write] using aligned
  exact first.trans (helper_execution (fillCalled s).core none count align)

def SafeWord (s : X86Memory.State) (a : Word) : Prop :=
  OriginalGroupHeap.Separated a [s.regs 4-4,s.regs 4-8,s.regs 4-12,s.regs 4-16,s.regs 4-20]
theorem nested_frame (s : X86Memory.State) (a : Word) (safe : SafeWord s a) :
    load32 (wordsCalled s).core.memory a=load32 s.memory a := by
  have h4 := safe (s.regs 4-4) (by simp)
  have h8 := safe (s.regs 4-8) (by simp)
  have h12 := safe (s.regs 4-12) (by simp)
  have h16 := safe (s.regs 4-16) (by simp)
  have h20 := safe (s.regs 4-20) (by simp)
  simp [wordsCalled,callWords,fillCalled,X86Routine.pushWord,put,write,
    BitVec.sub_eq_add_neg,BitVec.add_assoc] at h4 h8 h12 h16 h20 ⊢
  simp [load_store_apart _ _ _ _ h4,load_store_apart _ _ _ _ h8,
    load_store_apart _ _ _ _ h12,load_store_apart _ _ _ _ h16,load_store_apart _ _ _ _ h20]

theorem startup_agrees (pc : Nat)
    (h : X86FillRoutine.liftProgram E1M1AimSideAllocate.program pc≠none) :
    program pc=X86FillRoutine.liftProgram E1M1AimSideAllocate.program pc := by
  by_cases helper : (0x3fe70≤pc ∧ pc<0x3fe88) ∨ (0x418e0≤pc ∧ pc<0x41911)
  · have a : ¬((0x2e3e0≤pc ∧ pc<0x2e445) ∨ (0x38bb0≤pc ∧ pc<0x38be4)) := by omega
    have b : ¬((0x2e639≤pc ∧ pc<0x2e63e) ∨ (0x39690≤pc ∧ pc<0x396f8)) := by omega
    have c : ¬(0x396f8≤pc ∧ pc<0x39731) := by omega
    have d : ¬(0x39731≤pc ∧ pc<0x39776) := by omega
    have e : ¬(0x2e63e≤pc ∧ pc<0x2e661) := by omega
    have g : ¬(0x241c0≤pc ∧ pc<0x241dc) := by omega
    simp [X86FillRoutine.liftProgram,E1M1AimSideAllocate.program,E1M1AimSideAllocate.lift,
      X86StartupRoutine.liftProgram,X86ByteRoutine.liftProgram,OriginalGroupMalloc.program,
      OriginalGroupSelected.program,OriginalGroupHandoff.program,OriginalGroupEntry.program,
      OriginalGroupEntry.bytesProgram,a,b,c,d,e,g] at h
  · have a : ¬(0x3fe70≤pc ∧ pc<0x3fe88) := by omega
    have b : ¬(0x418e0≤pc ∧ pc<0x41911) := by omega
    simp [program,bytesProgram,a,b]

def nested (s : X86Memory.State) := wordsCalled (E1M1AimSidePublish.published s).core

theorem execution (s : X86Memory.State) (f : Option Flags) (table : Word)
    (h : E1M1AimSideEntry.Initial s table) (v : OriginalGroupHeap.View)
    (heap : E1M1AimSideAllocate.HeapInitial s v)
    (frame : E1M1AimSidePublish.AllocationFrame s v)
    (aligned : (v.block+24).extractLsb' 0 8 &&& 3=0) :
    (∃ n≤117, X86FillRoutine.Prefix program [] n ⟨s,f,0x2e3e0⟩ (nested s)) ∧
    (nested s).pc=0x41917 ∧ (nested s).core.regs 0=v.block+24 ∧
    (nested s).core.regs 1=2916 ∧ (nested s).core.regs 2=0 ∧
    (nested s).core.regs 4=s.regs 4-56 := by
  obtain ⟨⟨n,bound,path⟩,pc,base,index,zero,size,sp,ret⟩ :=
    E1M1AimSidePublish.execution s f table h v heap frame
  have align : readByte (E1M1AimSidePublish.published s).core.regs 0 &&& 3=0 := by
    simpa [readByte,byteReg,base] using aligned
  have suffix := nested_execution (E1M1AimSidePublish.published s).core
    (E1M1AimSidePublish.published s).flags zero size align
  have seam : (⟨(E1M1AimSidePublish.published s).core,(E1M1AimSidePublish.published s).flags,
      0x3fe70⟩ : X86Control.State)=E1M1AimSidePublish.published s := by rw [←pc]
  rw [seam] at suffix
  have lead := (X86FillRoutine.lift_prefix path).transfer program [] startup_agrees (by simp)
  refine ⟨⟨n+17,by omega,lead.trans suffix⟩,rfl,?_,?_,?_,?_⟩
  · simpa [nested,wordsCalled,callWords,fillCalled,X86Routine.pushWord,put,write] using base
  · simp [nested,wordsCalled,callWords,fillCalled,X86Routine.pushWord,put,write]
  · simp [nested,wordsCalled,callWords,fillCalled,X86Routine.pushWord,put,write]
  · simp [nested,wordsCalled,callWords,fillCalled,X86Routine.pushWord,put,write,sp,
      BitVec.sub_eq_add_neg,BitVec.add_assoc]

/-- Original-address separation, not a preservation hypothesis on a reached state. -/
def EntrySafe (s : X86Memory.State) (a : Word) : Prop :=
  Apart a 0x2c118 ∧ OriginalGroupHeap.Separated a
    [s.regs 4-36,s.regs 4-40,s.regs 4-44,s.regs 4-48,s.regs 4-52,s.regs 4-56]

theorem publication_frame (s : X86Memory.State) (f : Option Flags) (table : Word)
    (h : E1M1AimSideEntry.Initial s table) (v : OriginalGroupHeap.View)
    (heap : E1M1AimSideAllocate.HeapInitial s v) (a : Word)
    (safe : OriginalGroupHeap.Separated a
      [s.regs 4-36,s.regs 4-40,s.regs 4-44,s.regs 4-48,s.regs 4-52,s.regs 4-56]) :
    load32 (nested s).core.memory a=load32 (E1M1AimSidePublish.published s).core.memory a := by
  have sp := (E1M1AimSideAllocate.execution s f table h v heap).2.2.2
  apply nested_frame
  have stack : (E1M1AimSidePublish.published s).core.regs 4=s.regs 4-36 := by
    simp [E1M1AimSidePublish.published,E1M1AimSidePublish.publish,X86Routine.pushWord,put,write,sp,
      BitVec.sub_eq_add_neg,BitVec.add_assoc]
  unfold SafeWord
  rw [stack]
  simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc] at safe ⊢
  intro b hb
  apply safe b
  simpa using List.mem_cons_of_mem (s.regs 4 + -36) hb

theorem allocation_frame (s : X86Memory.State) (f : Option Flags) (table : Word)
    (h : E1M1AimSideEntry.Initial s table) (v : OriginalGroupHeap.View)
    (heap : E1M1AimSideAllocate.HeapInitial s v) (a : Word) (safe : EntrySafe s a) :
    load32 (nested s).core.memory a=load32 (E1M1AimSideAllocate.allocated s).core.memory a := by
  apply (publication_frame s f table h v heap a safe.2).trans
  apply E1M1AimSidePublish.published_frame s a safe.1
  have sp := (E1M1AimSideAllocate.execution s f table h v heap).2.2.2
  rw [sp]
  simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe.2 (s.regs 4-36) (by simp)

theorem count_preserved (s : X86Memory.State) (f : Option Flags) (table : Word)
    (h : E1M1AimSideEntry.Initial s table) (v : OriginalGroupHeap.View)
    (heap : E1M1AimSideAllocate.HeapInitial s v)
    (frame : E1M1AimSidePublish.AllocationFrame s v) (safe : EntrySafe s 0x2c11c) :
    load32 (nested s).core.memory 0x2c11c=648 := by
  exact (allocation_frame s f table h v heap 0x2c11c safe).trans
    (E1M1AimSidePublish.allocation_inputs s table h v heap frame).1

theorem base_preserved (s : X86Memory.State) (f : Option Flags) (table : Word)
    (h : E1M1AimSideEntry.Initial s table) (v : OriginalGroupHeap.View)
    (heap : E1M1AimSideAllocate.HeapInitial s v)
    (safe : OriginalGroupHeap.Separated 0x2c118
      [s.regs 4-36,s.regs 4-40,s.regs 4-44,s.regs 4-48,s.regs 4-52,s.regs 4-56]) :
    load32 (nested s).core.memory 0x2c118=v.block+24 := by
  exact (publication_frame s f table h v heap 0x2c118 safe).trans
    (E1M1AimSidePublish.published_base s f table h v heap (safe _ (by simp)))

theorem upper_preserved (s : X86Memory.State) (f : Option Flags) (table : Word)
    (h : E1M1AimSideEntry.Initial s table) (v : OriginalGroupHeap.View)
    (heap : E1M1AimSideAllocate.HeapInitial s v)
    (frame : E1M1AimSidePublish.AllocationFrame s v) (a : Word)
    (ha : a∈E1M1AimSidePublish.upperWords s) (safe : EntrySafe s a) :
    load32 (nested s).core.memory a=load32 (E1M1AimSideEntry.savedMemory s) a := by
  exact (allocation_frame s f table h v heap a safe).trans
    (E1M1AimSidePublish.allocation_upper s v heap frame a ha)
end Doom.Proofs.E1M1AimSideMemset
