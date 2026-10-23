import Doom.Proofs.E1M1AimCacheRead
/-! Actual W_ReadLump prologue. Neither disk-icon nor file success is assumed. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1AimReadPrologue
open Verification X86 X86Memory X86Control BlockSummary
open OriginalGroupHeap (Separated)
abbrev op := E1M1AimWordFill.op
def readBytes : List UInt8 := [0x53,0x51,0x56,0x57,0x55,0x89,0xc7,0x89,0xd5,0x3b,0x5,0xa0,0x4f,0x7,0x0,0x7c,0xe,0x50,0x68,0xfc,0x39,0x2,0x0,0xe8,0x4,0x1f,0xfe,0xff,0x83,0xc4,0x8,0x8d,0xc,0xbd,0x0,0x0,0x0,0x0,0x1,0xf9,0xa1,0xa4,0x4f,0x7,0x0,0x8d,0xc,0x8d,0x0,0x0,0x0,0x0,0x1,0xc1,0xe8,0x85,0x21,0xfe,0xff,0x8b,0x59,0x8,0x83,0xfb,0xff,0x75,0x2f,0x68,0x0,0x2,0x0,0x0,0x8b,0x35,0x9c,0x4f,0x7,0x0,0x56,0xe8,0x4d,0x7a,0x0,0x0,0x83,0xc4,0x8,0x89,0xc6,0x39,0xd8,0x75,0x17,0xa1,0x9c,0x4f,0x7,0x0,0x50,0x68,0x18,0x3a,0x2,0x0,0xe8,0xb3,0x1e,0xfe,0xff,0x83,0xc4,0x8,0xeb,0x2,0x89,0xde,0x89,0xf0,0x8b,0x51,0xc,0x31,0xdb,0xe8,0x50,0x7c,0x0,0x0,0x89,0xf0,0x89,0xea,0x8b,0x59,0x10,0xe8,0xb9,0x7c,0x0,0x0,0x8b,0x51,0x10,0x39,0xd0,0x7d,0x10,0x57,0x52,0x50,0x68,0x38,0x3a,0x2,0x0,0xe8,0x80,0x1e,0xfe,0xff,0x83,0xc4,0x10,0x83,0x79,0x8,0xff,0x75,0x7,0x89,0xf0,0xe8,0x62,0x7c,0x0,0x0,0xe8,0xfb,0x21,0xfe,0xff,0x5d,0x5f,0x5e,0x59,0x5b,0xc3]
def beginReadBytes : List UInt8 := [0x53,0x51,0x52,0x83,0x3d,0x34,0x91,0x2,0x0,0x0,0xf,0x84,0xdc,0x0,0x0,0x0,0xba,0xc4,0x3,0x0,0x0,0xb0,0x2,0xee,0xba,0xc5,0x3,0x0,0x0,0xb0,0xf,0xee,0xba,0xce,0x3,0x0,0x0,0xb0,0x5,0xee,0xba,0xcf,0x3,0x0,0x0,0x29,0xc0,0xec,0xc,0x1,0x31,0xdb,0xee,0xa1,0xf8,0x90,0x2,0x0,0xba,0xc8,0xf9,0xa,0x0,0x5,0xcc,0x39,0x0,0x0,0x8a,0x8,0x88,0xa,0x8a,0x48,0x1,0x88,0x4a,0x1,0x8a,0x48,0x2,0x88,0x4a,0x2,0x8a,0x48,0x3,0x88,0x4a,0x3,0x8a,0x48,0x50,0x88,0x4a,0x50,0x8a,0x48,0x51,0x83,0xc0,0x50,0x88,0x4a,0x51,0x83,0xc2,0x50,0x8a,0x48,0x2,0x83,0xc3,0x2,0x88,0x4a,0x2,0x83,0xc2,0x50,0x8a,0x48,0x3,0x83,0xc0,0x50,0x88,0x4a,0xb3,0x83,0xfb,0x10,0x7c,0xbe,0xba,0xcc,0xf9,0xa,0x0,0xa1,0xf8,0x90,0x2,0x0,0x31,0xdb,0x5,0xcc,0x39,0x0,0x0,0x8a,0xa,0x88,0x8,0x8a,0x4a,0x1,0x88,0x48,0x1,0x8a,0x4a,0x2,0x88,0x48,0x2,0x8a,0x4a,0x3,0x88,0x48,0x3,0x8a,0x4a,0x50,0x88,0x48,0x50,0x8a,0x4a,0x51,0x83,0xc2,0x50,0x88,0x48,0x51,0x83,0xc0,0x50,0x8a,0x4a,0x2,0x83,0xc3,0x2,0x88,0x48,0x2,0x83,0xc0,0x50,0x8a,0x4a,0x3,0x83,0xc2,0x50,0x88,0x48,0xb3,0x83,0xfb,0x10,0x7c,0xbe,0xba,0xce,0x3,0x0,0x0,0xb0,0x5,0xee,0xba,0xcf,0x3,0x0,0x0,0x29,0xc0,0xec,0x24,0xfe,0xee,0x5a,0x59,0x5b,0xc3]
def extend (previous : X86WordFillRoutine.Program) (read beginRead : List UInt8) : X86WordFillRoutine.Program := fun pc =>
  match previous pc with
  | some x => some x
  | none => if 0x38bf0≤pc ∧ pc<0x38cab then X86WordFillRoutine.decodeAt read (pc-0x38bf0)
    else if 0x1adb0≤pc ∧ pc<0x1aea0 then X86WordFillRoutine.decodeAt beginRead (pc-0x1adb0)
    else none
def program := extend E1M1AimCacheRead.program readBytes beginReadBytes
theorem previous_agrees (pc : Nat) (h : E1M1AimCacheRead.program pc≠none) :
    program pc=E1M1AimCacheRead.program pc := by
  unfold program extend
  cases e : E1M1AimCacheRead.program pc <;> simp_all

def listed : X86WordFillRoutine.Program
  | 0x38bf0 => some (op (.push 3),1)
  | 0x38bf1 => some (op (.push 1),1)
  | 0x38bf2 => some (op (.push 6),1)
  | 0x38bf3 => some (op (.push 7),1)
  | 0x38bf4 => some (op (.push 5),1)
  | 0x38bf5 => some (op (.control (.block (.legacy (.mov 7 0)))),2)
  | 0x38bf7 => some (op (.control (.block (.legacy (.mov 5 2)))),2)
  | 0x38bf9 => some (op (.control (.cmpMemory 0 ⟨none,none,0,0x74fa0⟩)),6)
  | 0x38bff => some (op (.jumpSigned 3 14),2)
  | 0x38c0f => some (op (.control (.block (.lea 1 ⟨none,some 7,2,0⟩))),7)
  | 0x38c16 => some (op (.control (.block (.arithmetic (.add 1 7)))),2)
  | 0x38c18 => some (op (.control (.block (.load 0 ⟨none,none,0,0x74fa4⟩))),5)
  | 0x38c1d => some (op (.control (.block (.lea 1 ⟨none,some 1,2,0⟩))),7)
  | 0x38c24 => some (op (.control (.block (.arithmetic (.add 1 0)))),2)
  | 0x38c26 => some (op (.call (-122491)),5)
  | _ => none
theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def saves (s : X86Memory.State) : List (Word × Word) :=
  [(s.regs 4-4,s.regs 3),(s.regs 4-8,s.regs 1),(s.regs 4-12,s.regs 6),
   (s.regs 4-16,s.regs 7),(s.regs 4-20,s.regs 5)]
def saved (s : X86Memory.State) := X86Routine.pushWord (X86Routine.pushWord
  (X86Routine.pushWord (X86Routine.pushWord (X86Routine.pushWord s (s.regs 3)) (s.regs 1))
    (s.regs 6)) (s.regs 7)) (s.regs 5)
def Safe (s : X86Memory.State) (a : Word) : Prop := ∀ w∈saves s, Apart a w.1
theorem saved_memory (s : X86Memory.State) : (saved s).memory=HeapWrites.apply (saves s) s.memory := by
  simp [saved,saves,HeapWrites.apply,X86Routine.pushWord,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc]
theorem saved_frame (s : X86Memory.State) (a : Word) (safe : Safe s a) :
    load32 (saved s).memory a=load32 s.memory a := by
  rw [saved_memory]; exact HeapWrites.frame _ _ _ safe
def opened (s : X86Memory.State) : X86WordFillRoutine.State :=
  ⟨put (put (saved s) 7 9) 5 (s.regs 2),.legacy (some (compare32 9 1264)),0x38c0f⟩
def iconCalled (s : X86Memory.State) (table : Word) : X86WordFillRoutine.State :=
  ⟨X86Routine.pushWord (put (put (opened s).core 0 table) 1 (180+table)) 0x38c2b,.legacy none,0x1adb0⟩

theorem open_execution (s : X86Memory.State) (f : Option Flags)
    (index : s.regs 0=9) (count : load32 s.memory 0x74fa0=1264) (safe : Safe s 0x74fa0) :
    X86WordFillRoutine.Prefix program [] 9 (X86WordFillRoutine.embed ⟨s,f,0x38bf0⟩) (opened s) := by
  have c := (saved_frame s _ safe).trans count
  simp only [BitVec.ofNat_eq_ofNat] at c index
  have path : X86WordFillRoutine.Prefix listed [] 9 (X86WordFillRoutine.embed ⟨s,f,0x38bf0⟩) (opened s) := by
    refine .step (by simp [X86WordFillRoutine.embed]) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (middle:=⟨(opened s).core,.legacy f,0x38bf9⟩) (by simp) rfl ?_ ?_
    · simp [opened,saved,X86WordFillRoutine.execute,X86WordFillRoutine.embed,
        X86FillRoutine.execute,X86StartupRoutine.execute,X86ByteRoutine.execute,X86Routine.execute,
        X86Control.execute,X86Block.execute,X86Memory.execute,blockPreservesFlags,
        X86Routine.pushWord,put,write,index]
    refine .step (middle:=⟨(opened s).core,.legacy (some (compare32 9 1264)),0x38bff⟩) (by simp) rfl ?_ ?_
    · simp [opened,X86WordFillRoutine.execute,X86WordFillRoutine.embed,
        X86FillRoutine.execute,X86StartupRoutine.execute,X86ByteRoutine.execute,X86Routine.execute,
        X86Control.execute,X86Block.Address.eval,put,write,c]
      simp only [saved,X86Routine.pushWord,put,write] at c
      simp [saved,X86Routine.pushWord,put,write,index,c]
    refine .step (middle:=opened s) (by simp) rfl ?_ (.nil _)
    simp [opened,X86WordFillRoutine.execute,X86WordFillRoutine.embed,
      X86FillRoutine.execute,X86StartupRoutine.execute,X86ByteRoutine.execute,X86Routine.execute,compare32,BitVec.msb]
  exact path.transfer _ [] decoded (by simp)

theorem call_execution (s : X86Memory.State) (table : Word)
    (pointer : load32 s.memory 0x74fa4=table) (safe : Safe s 0x74fa4) :
    X86WordFillRoutine.Prefix program [] 6 (opened s) (iconCalled s table) := by
  have ptr := (saved_frame s _ safe).trans pointer
  simp only [BitVec.ofNat_eq_ofNat] at ptr
  have path : X86WordFillRoutine.Prefix listed [] 6 (opened s) (iconCalled s table) := by
    refine .step (by simp [opened]) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (middle:=iconCalled s table) (by simp) rfl ?_ (.nil _)
    simp [iconCalled,opened,X86WordFillRoutine.execute,X86WordFillRoutine.embed,
      X86FillRoutine.execute,X86StartupRoutine.execute,X86ByteRoutine.execute,X86Routine.execute,
      X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,blockPreservesFlags,
      X86.execute,X86Routine.pushWord,put,write,ptr]
    funext r
    by_cases h0 : r=0 <;> by_cases h1 : r=1 <;> simp [write,h0,h1]
  exact path.transfer _ [] decoded (by simp)

theorem local_execution (s : X86Memory.State) (f : Option Flags) (table : Word)
    (index : s.regs 0=9) (count : load32 s.memory 0x74fa0=1264)
    (pointer : load32 s.memory 0x74fa4=table)
    (countSafe : Safe s 0x74fa0) (pointerSafe : Safe s 0x74fa4) :
    X86WordFillRoutine.Prefix program [] 15 (X86WordFillRoutine.embed ⟨s,f,0x38bf0⟩) (iconCalled s table) := by
  exact (open_execution s f index count countSafe).trans (call_execution s table pointer pointerSafe)
def writes (s : X86Memory.State) := saves s++[(s.regs 4-24,0x38c2b)]
theorem call_memory (s : X86Memory.State) (table : Word) :
    (iconCalled s table).core.memory=HeapWrites.apply (writes s) s.memory := by
  simp [iconCalled,opened,writes,saves,HeapWrites.append,saved_memory,HeapWrites.apply,
    saved,X86Routine.pushWord,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc]
theorem call_frame (s : X86Memory.State) (table a : Word)
    (safe : ∀ w∈writes s, Apart a w.1) :
    load32 (iconCalled s table).core.memory a=load32 s.memory a := by
  rw [call_memory]; exact HeapWrites.frame _ _ _ safe
theorem call_observations (s : X86Memory.State) (table : Word) :
    (iconCalled s table).core.regs 7=9 ∧ (iconCalled s table).core.regs 5=s.regs 2 ∧
    (iconCalled s table).core.regs 1=180+table ∧ (iconCalled s table).core.regs 4=s.regs 4-24 ∧
    load32 (iconCalled s table).core.memory (s.regs 4-24)=0x38c2b := by
  simp [iconCalled,opened,saved,X86Routine.pushWord,put,write,
    BitVec.sub_eq_add_neg,BitVec.add_assoc,load_store]

/-- Original-address preservation through both real allocations and zeroing. -/
structure OriginalSafe (s : X86Memory.State) (v : OriginalGroupHeap.View)
    (cache nextSize nextNext a : Word) : Prop where
  prior : E1M1AimCacheCall.ReadSafe s v a
  later : Separated a (E1M1AimCacheRead.laterAddresses s (E1M1AimCacheHeap.nextView v nextSize nextNext) cache)

theorem read_frame (s : X86Memory.State) (f : Option Flags) (table cache : Word)
    (initial : E1M1AimSideEntry.Initial s table) (v : OriginalGroupHeap.View)
    (heap : E1M1AimSideAllocate.HeapInitial s v) (frame : E1M1AimSidePublish.AllocationFrame s v)
    (h : Nat) (small : h<8) (safe : E1M1AimWordFill.Entry32Safe s v)
    (nextSize nextNext : Word) (history : E1M1AimCacheHeap.History s v nextSize nextNext)
    (conditions : E1M1AimCacheAllocate.Conditions s v cache nextSize nextNext)
    (a : Word) (kept : OriginalSafe s v cache nextSize nextNext a) :
    load32 (E1M1AimCacheRead.readCalled s h cache).core.memory a=load32 s.memory a := by
  exact (E1M1AimCacheRead.produced_frame s f table cache initial v heap frame h small safe
    nextSize nextNext history conditions a kept.prior.nested kept.prior.output kept.later).trans
      (E1M1AimSidePublish.allocation_frame s v heap a kept.prior.allocation)

def stackAddresses (s : X86Memory.State) : List Word :=
  [s.regs 4-60,s.regs 4-64,s.regs 4-68,s.regs 4-72,s.regs 4-76,s.regs 4-80]
structure Conditions (s : X86Memory.State) (v : OriginalGroupHeap.View)
    (cache nextSize nextNext : Word) : Prop where
  original : ∀ a∈[0x74fa0,0x74fa4], OriginalSafe s v cache nextSize nextNext a
  stack : ∀ a∈[0x74fa0,0x74fa4], Separated a (stackAddresses s)
def entered (s : X86Memory.State) (h : Nat) (table cache : Word) :=
  iconCalled (E1M1AimCacheRead.readCalled s h cache).core table

theorem stack_writes (s t : X86Memory.State) (sp : t.regs 4=s.regs 4-56) :
    (writes t).map Prod.fst=stackAddresses s := by
  simp [writes,saves,stackAddresses,sp,BitVec.sub_eq_add_neg,BitVec.add_assoc]
theorem entry_execution (s : X86Memory.State) (f : Option Flags) (table cache : Word)
    (initial : E1M1AimSideEntry.Initial s table) (v : OriginalGroupHeap.View)
    (heap : E1M1AimSideAllocate.HeapInitial s v) (frame : E1M1AimSidePublish.AllocationFrame s v)
    (aligned : (v.block+24).extractLsb' 0 8 &&& 3=0) (safe : E1M1AimWordFill.Entry32Safe s v)
    (inputs : E1M1AimCacheDispatch.CacheInitial s v cache) (miss : load32 s.memory (cache+36)=0)
    (pointerSafe : E1M1AimCacheCall.ReadSafe s v 0x74fa4)
    (lengthSafe : E1M1AimCacheCall.ReadSafe s v (180+table+16))
    (nextSize nextNext : Word) (history : E1M1AimCacheHeap.History s v nextSize nextNext)
    (conditions : E1M1AimCacheAllocate.Conditions s v cache nextSize nextNext)
    (readSafe : E1M1AimCacheRead.ReadConditions s v cache nextSize nextNext)
    (bodySafe : Conditions s v cache nextSize nextNext) :
    ∃ h<8, (∃ n≤5419, X86WordFillRoutine.Prefix program [] n
      (X86WordFillRoutine.embed ⟨s,f,0x2e3e0⟩) (entered s h table cache)) ∧
      (entered s h table cache).pc=0x1adb0 ∧ (entered s h table cache).core.regs 7=9 ∧
      (entered s h table cache).core.regs 5=(E1M1AimCacheHeap.nextView v nextSize nextNext).block+24 ∧
      (entered s h table cache).core.regs 1=180+table ∧
      (entered s h table cache).core.regs 4=s.regs 4-80 ∧
      load32 (entered s h table cache).core.memory (s.regs 4-80)=0x38c2b := by
  obtain ⟨h,small,⟨n,b,path⟩,pc,idx,raw,sp,_ret⟩ := E1M1AimCacheRead.entry_execution
    s f table cache initial v heap frame aligned safe inputs miss pointerSafe lengthSafe
    nextSize nextNext history conditions readSafe
  have kept := read_frame s f table cache initial v heap frame h small safe nextSize nextNext history conditions
  have cf := (kept _ (bodySafe.original _ (by simp))).trans initial.count
  have pf := (kept _ (bodySafe.original _ (by simp))).trans initial.tablePointer
  have ss (a : Word) (ha : a∈[0x74fa0,0x74fa4]) : Safe (E1M1AimCacheRead.readCalled s h cache).core a := by
    intro w hw
    apply bodySafe.stack a ha w.1
    rw [←stack_writes s _ sp]
    exact List.mem_map.mpr ⟨w,List.mem_append_left _ hw,rfl⟩
  have flags : (E1M1AimCacheRead.readCalled s h cache).flags=
      .legacy (some (logical32 (cache+36))) := by rfl
  have tail := local_execution (E1M1AimCacheRead.readCalled s h cache).core
    (some (logical32 (cache+36))) table idx cf pf (ss _ (by simp)) (ss _ (by simp))
  have seam : X86WordFillRoutine.embed ⟨(E1M1AimCacheRead.readCalled s h cache).core,
      some (logical32 (cache+36)),0x38bf0⟩=E1M1AimCacheRead.readCalled s h cache := by
    simp only [X86WordFillRoutine.embed]; rw [←pc,←flags]
  rw [seam] at tail
  have obs := call_observations (E1M1AimCacheRead.readCalled s h cache).core table
  have esp : (entered s h table cache).core.regs 4=s.regs 4-80 := by
    rw [show (entered s h table cache).core.regs 4=_ from obs.2.2.2.1,sp]
    simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  refine ⟨h,small,⟨n+15,by omega,(path.transfer _ [] previous_agrees (by simp)).trans tail⟩,
    rfl,obs.1,obs.2.1.trans raw,obs.2.2.1,esp,?_⟩
  have slot : (E1M1AimCacheRead.readCalled s h cache).core.regs 4-24=s.regs 4-80 := by
    rw [sp]; simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  simpa only [entered,slot] using obs.2.2.2.2

/-- Frame relative to actual read entry. Instantiates both produced metadata and
upper caller words; it does not replace produced memory by a loaded image. -/
theorem entry_frame (s : X86Memory.State) (h : Nat) (table cache a : Word)
    (sp : (E1M1AimCacheRead.readCalled s h cache).core.regs 4=s.regs 4-56)
    (safe : Separated a (stackAddresses s)) :
    load32 (entered s h table cache).core.memory a=
      load32 (E1M1AimCacheRead.readCalled s h cache).core.memory a := by
  apply call_frame
  intro w hw
  apply safe w.1
  rw [←stack_writes s _ sp]
  exact List.mem_map.mpr ⟨w,hw,rfl⟩

theorem output_preserved (s : X86Memory.State) (f : Option Flags) (table cache : Word)
    (initial : E1M1AimSideEntry.Initial s table) (v : OriginalGroupHeap.View)
    (heap : E1M1AimSideAllocate.HeapInitial s v) (frame : E1M1AimSidePublish.AllocationFrame s v)
    (h : Nat) (small : h<8) (safe : E1M1AimWordFill.Entry32Safe s v)
    (nextSize nextNext : Word) (history : E1M1AimCacheHeap.History s v nextSize nextNext)
    (conditions : E1M1AimCacheAllocate.Conditions s v cache nextSize nextNext)
    (sp : (E1M1AimCacheRead.readCalled s h cache).core.regs 4=s.regs 4-56)
    (output : ∀ j<11664, E1M1AimCacheRead.ByteSafe (v.block+24+BitVec.ofNat 32 j)
      (E1M1AimCacheRead.laterAddresses s (E1M1AimCacheHeap.nextView v nextSize nextNext) cache))
    (stack : ∀ j<11664, E1M1AimCacheRead.ByteSafe (v.block+24+BitVec.ofNat 32 j) (stackAddresses s)) :
    ∀ j<11664, (entered s h table cache).core.memory (v.block+24+BitVec.ofNat 32 j)=0 := by
  have zero := E1M1AimCacheRead.output_preserved s f table cache initial v heap frame h small safe
    nextSize nextNext history conditions output
  intro j hj
  change (iconCalled _ table).core.memory _=0
  rw [call_memory,E1M1AimCacheRead.bytes_frame _ _ _ (by rw [stack_writes s _ sp]; exact stack j hj)]
  exact zero j hj
end Doom.Proofs.E1M1AimReadPrologue
