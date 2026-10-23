import Doom.Proofs.E1M1AimCacheCall
/-! W_CacheLumpNum's actual dispatcher. Both outcomes are retained: the preserved
original owner cell, not a convenient reached cache image, selects the branch.
Cache allocation, filesystem effects and cache initialization history are separate. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1AimCacheDispatch
open Verification X86 X86Memory X86Control BlockSummary
open E1M1AimWordFill (Entry32Safe OutputSafe)
open E1M1AimCacheCall (entered ReadSafe)
abbrev op := E1M1AimWordFill.op
def cacheBytes : List UInt8 := [0x53,0x51,0x56,0x57,0x89,0xc1,0x3b,0x05,0xa0,0x4f,0x07,0x00,0x72,0x0e,0x50,0x68,0x64,0x3a,0x02,0x00,0xe8,0xf7,0x1d,0xfe,0xff,0x83,0xc4,0x08,0x8b,0x1d,0x94,0x4f,0x07,0x00,0x8d,0x34,0x8d,0x00,0x00,0x00,0x00,0x01,0xf3,0x8b,0x3b,0x85,0xff,0x0f,0x85,0x76,0xff,0xff,0xff,0x89,0xc8,0xe8,0x74,0xfe,0xff,0xff,0xe8,0x4f,0x09,0x00,0x00,0xa1,0x94,0x4f,0x07,0x00,0x8b,0x14,0x06,0x89,0xc8,0xe8,0xa0,0xfe,0xff,0xff,0x8b,0x15,0x94,0x4f,0x07,0x00,0x8b,0x04,0x8a,0x5f,0x5e,0x59,0x5b,0xc3]
def hitBytes : List UInt8 := [0x81,0x7f,0xf4,0x11,0x4a,0x1d,0x00,0x74,0x12,0x68,0xfe,0x01,0x00,0x00,0x68,0x84,0x3a,0x02,0x00,0xe8,0x4d,0x1e,0xfe,0xff,0x83,0xc4,0x08,0xa1,0x94,0x4f,0x07,0x00,0x8b,0x04,0x88,0xe8,0xdd,0x0c,0x00,0x00,0x8b,0x15,0x94,0x4f,0x07,0x00,0x8b,0x04,0x8a,0x5f,0x5e,0x59,0x5b,0xc3]
def extend (previous : X86WordFillRoutine.Program) (cache hit : List UInt8) : X86WordFillRoutine.Program := fun pc =>
  match previous pc with
  | some x => some x
  | none => if 0x38d00≤pc ∧ pc<0x38d5e then X86WordFillRoutine.decodeAt cache (pc-0x38d00)
    else if 0x38cab≤pc ∧ pc<0x38ce1 then X86WordFillRoutine.decodeAt hit (pc-0x38cab)
    else none
def program := extend E1M1AimCacheCall.program cacheBytes hitBytes
theorem previous_agrees (pc : Nat) (h : E1M1AimCacheCall.program pc≠none) :
    program pc=E1M1AimCacheCall.program pc := by
  unfold program extend
  cases e : E1M1AimCacheCall.program pc <;> simp_all

def listed : X86WordFillRoutine.Program
  | 0x38d00 => some (op (.push 3),1)
  | 0x38d01 => some (op (.push 1),1)
  | 0x38d02 => some (op (.push 6),1)
  | 0x38d03 => some (op (.push 7),1)
  | 0x38d04 => some (op (.control (.block (.legacy (.mov 1 0)))),2)
  | 0x38d06 => some (op (.control (.cmpMemory 0 ⟨none,none,0,0x74fa0⟩)),6)
  | 0x38d0c => some (op (.jumpUnsigned 0 14),2)
  | 0x38d1c => some (op (.control (.block (.load 3 ⟨none,none,0,0x74f94⟩))),6)
  | 0x38d22 => some (op (.control (.block (.lea 6 ⟨none,some 1,2,0⟩))),7)
  | 0x38d29 => some (op (.control (.block (.arithmetic (.add 3 6)))),2)
  | 0x38d2b => some (op (.control (.block (.legacy (.load 7 3 0)))),2)
  | 0x38d2d => some (op (.control (.testWord 7 7)),2)
  | 0x38d2f => some (op (.control (.jumpZero false (-138))),6)
  | _ => none
theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def saved (s : X86Memory.State) := X86Routine.pushWord (X86Routine.pushWord
  (X86Routine.pushWord (X86Routine.pushWord s (s.regs 3)) (s.regs 1)) (s.regs 6)) (s.regs 7)
def Safe (s : X86Memory.State) (a : Word) : Prop :=
  OriginalGroupHeap.Separated a [s.regs 4-4,s.regs 4-8,s.regs 4-12,s.regs 4-16]
theorem saved_frame (s : X86Memory.State) (a : Word) (safe : Safe s a) :
    load32 (saved s).memory a=load32 s.memory a := by
  have h4 := safe _ (by simp : s.regs 4-4∈[s.regs 4-4,s.regs 4-8,s.regs 4-12,s.regs 4-16])
  have h8 := safe _ (by simp : s.regs 4-8∈[s.regs 4-4,s.regs 4-8,s.regs 4-12,s.regs 4-16])
  have h12 := safe _ (by simp : s.regs 4-12∈[s.regs 4-4,s.regs 4-8,s.regs 4-12,s.regs 4-16])
  have h16 := safe _ (by simp : s.regs 4-16∈[s.regs 4-4,s.regs 4-8,s.regs 4-12,s.regs 4-16])
  simp only [BitVec.sub_eq_add_neg,BitVec.ofNat_eq_ofNat,BitVec.reduceNeg] at h4 h8 h12 h16
  simp [saved,X86Routine.pushWord,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,
    load_store_apart _ _ _ _ h4,load_store_apart _ _ _ _ h8,
    load_store_apart _ _ _ _ h12,load_store_apart _ _ _ _ h16]
def opened (s : X86Memory.State) : X86WordFillRoutine.State :=
  ⟨put (saved s) 1 9,.legacy (some (compare32 9 1264)),0x38d1c⟩
def branch (s : X86Memory.State) (cache value : Word) : X86WordFillRoutine.State :=
  ⟨put (put (put (opened s).core 3 (cache+36)) 6 36) 7 value,
    .legacy (some (logical32 value)),if value=0 then 0x38d35 else 0x38cab⟩

theorem open_execution (s : X86Memory.State) (f : X86WordFillRoutine.Knowledge)
    (index : s.regs 0=9) (count : load32 s.memory 0x74fa0=1264) (safe : Safe s 0x74fa0) :
    X86WordFillRoutine.Prefix program [] 7 ⟨s,f,0x38d00⟩ (opened s) := by
  have c := (saved_frame s _ safe).trans count
  simp only [BitVec.ofNat_eq_ofNat] at c index
  have path : X86WordFillRoutine.Prefix listed [] 7 ⟨s,f,0x38d00⟩ (opened s) := by
    cases hf : f <;>
      (refine .step (by simp) rfl rfl ?_
       refine .step (by simp) rfl rfl ?_
       refine .step (by simp) rfl rfl ?_
       refine .step (by simp) rfl rfl ?_
       refine .step (middle:=⟨(opened s).core,f,0x38d06⟩) (by simp) rfl ?_ ?_)
    all_goals first
      | (solve | simp [opened,saved,X86WordFillRoutine.execute,X86WordFillRoutine.embed,X86WordFillRoutine.preserves,
          X86FillRoutine.execute,X86StartupRoutine.execute,X86ByteRoutine.execute,X86Routine.execute,
          X86Control.execute,X86Block.execute,X86Memory.execute,blockPreservesFlags,
          X86Routine.pushWord,put,write,index,hf])
      | skip
    all_goals
      refine .step (middle:=⟨(opened s).core,.legacy (some (compare32 9 1264)),0x38d0c⟩) (by simp) rfl ?_ ?_
      · simp [opened,X86WordFillRoutine.execute,X86WordFillRoutine.embed,X86WordFillRoutine.preserves,
          X86FillRoutine.execute,X86StartupRoutine.execute,X86ByteRoutine.execute,X86Routine.execute,
          X86Control.execute,X86Block.Address.eval,put,write,c,hf]
        simp only [saved,X86Routine.pushWord,put,write] at c
        simpa [saved,X86Routine.pushWord,put,write,index] using congrArg (compare32 (9#32)) c
      refine .step (middle:=opened s) (by simp) rfl ?_ (.nil _)
      simp [opened,X86WordFillRoutine.execute,X86WordFillRoutine.embed,
        X86FillRoutine.execute,X86StartupRoutine.execute,X86ByteRoutine.execute,
        X86Routine.execute,compare32]
  exact path.transfer _ [] decoded (by simp)

theorem branch_execution (s : X86Memory.State) (cache value : Word)
    (pointer : load32 s.memory 0x74f94=cache) (cell : load32 s.memory (cache+36)=value)
    (ptrSafe : Safe s 0x74f94) (cellSafe : Safe s (cache+36)) :
    X86WordFillRoutine.Prefix program [] 6 (opened s) (branch s cache value) := by
  have p := (saved_frame s _ ptrSafe).trans pointer
  have v := (saved_frame s _ cellSafe).trans cell
  simp only [BitVec.ofNat_eq_ofNat] at p v
  have path : X86WordFillRoutine.Prefix listed [] 6 (opened s) (branch s cache value) := by
    refine .step (by simp [opened]) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (middle:=⟨(branch s cache value).core,.legacy (some (logical32 value)),0x38d2f⟩) (by simp) rfl ?_ ?_
    · simp [opened,branch,X86WordFillRoutine.execute,X86WordFillRoutine.embed,
        X86FillRoutine.execute,X86StartupRoutine.execute,X86ByteRoutine.execute,X86Routine.execute,
        X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,blockPreservesFlags,
        X86.execute,put,write,p,v,logical32]
      funext r
      by_cases h3 : r=3 <;> by_cases h6 : r=6 <;> by_cases h7 : r=7 <;> simp [write,h3,h6,h7]
    refine .step (middle:=branch s cache value) (by simp) rfl ?_ (.nil _)
    by_cases h : value=0#32 <;>
      simp [branch,X86WordFillRoutine.execute,X86WordFillRoutine.embed,
        X86FillRoutine.execute,X86StartupRoutine.execute,X86ByteRoutine.execute,X86Routine.execute,
        X86Control.execute,logical32,h]
  exact path.transfer _ [] decoded (by simp)

structure CacheInitial (s : X86Memory.State) (v : OriginalGroupHeap.View) (cache : Word) : Prop where
  pointer : load32 s.memory 0x74f94=cache
  countSafe : ReadSafe s v 0x74fa0
  pointerSafe : ReadSafe s v 0x74f94
  cellSafe : ReadSafe s v (cache+36)
def dispatched (s : X86Memory.State) (h : Nat) (cache : Word) :=
  branch (entered s h).core cache (load32 s.memory (cache+36))

theorem entered_safe (s : X86Memory.State) (f : Option Flags) (table : Word)
    (initial : E1M1AimSideEntry.Initial s table) (v : OriginalGroupHeap.View)
    (heap : E1M1AimSideAllocate.HeapInitial s v) (frame : E1M1AimSidePublish.AllocationFrame s v)
    (h : Nat) (small : h<8) (a : Word) (readSafe : ReadSafe s v a) :
    Safe (entered s h).core a := by
  have sp := (E1M1AimCacheCall.entry_registers s f table initial v heap frame h small).2.2.2.1
  unfold Safe
  rw [sp]
  intro b hb
  apply readSafe.nested.2 b
  simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc] at hb ⊢
  simp only [List.mem_cons,List.mem_singleton] at hb ⊢
  rcases hb with h|h|h|h <;> simp_all

theorem entry_execution (s : X86Memory.State) (f : Option Flags) (table cache : Word)
    (initial : E1M1AimSideEntry.Initial s table) (v : OriginalGroupHeap.View)
    (heap : E1M1AimSideAllocate.HeapInitial s v) (frame : E1M1AimSidePublish.AllocationFrame s v)
    (aligned : (v.block+24).extractLsb' 0 8 &&& 3=0) (safe : Entry32Safe s v)
    (inputs : CacheInitial s v cache) :
    ∃ h<8, (∃ n≤5317, X86WordFillRoutine.Prefix program [] n
      (X86WordFillRoutine.embed ⟨s,f,0x2e3e0⟩) (dispatched s h cache)) ∧
      (dispatched s h cache).pc=(if load32 s.memory (cache+36)=0 then 0x38d35 else 0x38cab) ∧
      (dispatched s h cache).core.regs 3=cache+36 ∧
      (dispatched s h cache).core.regs 7=load32 s.memory (cache+36) := by
  obtain ⟨h,small,⟨n,b,path⟩,pc,index,_⟩ := E1M1AimCacheCall.entry_execution s f table initial v heap frame aligned safe
  have keep := E1M1AimCacheCall.entry_frame s f table initial v heap frame h small safe
  have sep := entered_safe s f table initial v heap frame h small
  have lead := open_execution (entered s h).core (entered s h).flags index
    ((keep _ inputs.countSafe).trans initial.count) (sep _ inputs.countSafe)
  have seam : (⟨(entered s h).core,(entered s h).flags,0x38d00⟩ : X86WordFillRoutine.State)=entered s h := by rw [←pc]
  rw [seam] at lead
  have tail := branch_execution (entered s h).core cache (load32 s.memory (cache+36))
    ((keep _ inputs.pointerSafe).trans inputs.pointer) (keep _ inputs.cellSafe)
    (sep _ inputs.pointerSafe) (sep _ inputs.cellSafe)
  refine ⟨h,small,⟨n+7+6,by omega,((path.transfer _ [] previous_agrees (by simp)).trans lead).trans tail⟩,rfl,?_,rfl⟩
  simp [dispatched,branch,put,write]

def missListing : X86WordFillRoutine.Program
  | 0x38d35 => some (op (.control (.block (.legacy (.mov 0 1)))),2)
  | 0x38d37 => some (op (.call (-396)),5)
  | 0x38d3c => some (op (.call 2383),5)
  | 0x38bb0 => some (op (.push 2),1)
  | 0x38bb1 => some (op (.control (.block (.legacy (.mov 2 0)))),2)
  | 0x38bb3 => some (op (.control (.cmpMemory 0 ⟨none,none,0,0x74fa0⟩)),6)
  | 0x38bb9 => some (op (.jumpSigned 3 14),2)
  | 0x38bc9 => some (op (.control (.block (.lea 0 ⟨none,some 2,2,0⟩))),7)
  | 0x38bd0 => some (op (.control (.block (.arithmetic (.add 2 0)))),2)
  | 0x38bd2 => some (op (.control (.block (.load 0 ⟨none,none,0,0x74fa4⟩))),5)
  | 0x38bd7 => some (op (.control (.block (.lea 2 ⟨none,some 2,2,0⟩))),7)
  | 0x38bde => some (op (.control (.block (.load 0 ⟨some 2,some 0,0,16⟩))),4)
  | 0x38be2 => some (op (.pop 2),1)
  | 0x38be3 => some (op .ret,1)
  | _ => none
theorem miss_decoded (pc : Nat) (h : missListing pc≠none) : program pc=missListing pc := by
  fun_cases missListing pc <;> simp_all [missListing] <;> decide

def lengthCalled (s : X86Memory.State) := X86Routine.pushWord (put s 0 9) 0x38d3c
def lengthSaved (s : X86Memory.State) := X86Routine.pushWord (lengthCalled s) (s.regs 2)
def lengthOpened (s : X86Memory.State) : X86WordFillRoutine.State :=
  ⟨put (lengthSaved s) 2 9,.legacy (some (compare32 9 1264)),0x38bc9⟩
def measured (s : X86Memory.State) : X86WordFillRoutine.State :=
  ⟨put (put (put (lengthSaved s) 4 (s.regs 4)) 0 19440) 2 (s.regs 2),.legacy none,0x38d3c⟩
def request (s : X86Memory.State) : X86WordFillRoutine.State :=
  ⟨X86Routine.pushWord (measured s).core 0x38d41,.legacy none,0x39690⟩
def LengthSafe (s : X86Memory.State) (a : Word) : Prop :=
  Apart a (s.regs 4-4) ∧ Apart a (s.regs 4-8)
theorem length_frame (s : X86Memory.State) (a : Word) (safe : LengthSafe s a) :
    load32 (lengthSaved s).memory a=load32 s.memory a := by
  have h4 := safe.1; have h8 := safe.2
  simp only [BitVec.sub_eq_add_neg,BitVec.ofNat_eq_ofNat,BitVec.reduceNeg] at h4 h8
  simp [lengthSaved,lengthCalled,X86Routine.pushWord,put,write,BitVec.sub_eq_add_neg,
    BitVec.add_assoc,load_store_apart _ _ _ _ h4,load_store_apart _ _ _ _ h8]

theorem miss_call_execution (s : X86Memory.State) (index : s.regs 1=9) :
    X86WordFillRoutine.Prefix program [] 2 ⟨s,.legacy (some (logical32 0)),0x38d35⟩
      ⟨lengthCalled s,.legacy (some (logical32 0)),0x38bb0⟩ := by
  have path : X86WordFillRoutine.Prefix missListing [] 2 ⟨s,.legacy (some (logical32 0)),0x38d35⟩
      ⟨lengthCalled s,.legacy (some (logical32 0)),0x38bb0⟩ := by
    refine .step (by simp) rfl rfl ?_
    refine .step (middle:=⟨lengthCalled s,.legacy (some (logical32 0)),0x38bb0⟩) (by simp) rfl ?_ (.nil _)
    simp [lengthCalled,X86WordFillRoutine.execute,X86WordFillRoutine.embed,X86FillRoutine.execute,
      X86StartupRoutine.execute,X86ByteRoutine.execute,X86Routine.execute,X86Control.execute,
      X86Block.execute,X86Memory.execute,blockPreservesFlags,X86Routine.pushWord,put,write,index]
  exact path.transfer _ [] miss_decoded (by simp)

theorem length_open_execution (s : X86Memory.State)
    (count : load32 s.memory 0x74fa0=1264) (safe : LengthSafe s 0x74fa0) :
    X86WordFillRoutine.Prefix program [] 4
      ⟨lengthCalled s,.legacy (some (logical32 0)),0x38bb0⟩ (lengthOpened s) := by
  have c := (length_frame s _ safe).trans count
  simp only [BitVec.ofNat_eq_ofNat] at c
  have path : X86WordFillRoutine.Prefix missListing [] 4
      ⟨lengthCalled s,.legacy (some (logical32 0)),0x38bb0⟩ (lengthOpened s) := by
    refine .step (middle:=⟨lengthSaved s,.legacy (some (logical32 0)),0x38bb1⟩) (by simp) rfl ?_ ?_
    · rfl
    refine .step (middle:=⟨(lengthOpened s).core,.legacy (some (logical32 0)),0x38bb3⟩) (by simp) rfl ?_ ?_
    · rfl
    refine .step (middle:=⟨(lengthOpened s).core,.legacy (some (compare32 9 1264)),0x38bb9⟩) (by simp) rfl ?_ ?_
    · simp [lengthOpened,X86WordFillRoutine.execute,X86WordFillRoutine.embed,
        X86FillRoutine.execute,X86StartupRoutine.execute,X86ByteRoutine.execute,
        X86Routine.execute,X86Control.execute,X86Block.Address.eval,put,write,c]
      simp only [lengthSaved,lengthCalled,X86Routine.pushWord,put,write] at c
      simpa [lengthSaved,lengthCalled,X86Routine.pushWord,put,write] using congrArg (compare32 (9#32)) c
    exact .step (by simp) rfl rfl (.nil _)
  exact path.transfer _ [] miss_decoded (by simp)

theorem length_return_execution (s : X86Memory.State) (table : Word)
    (pointer : load32 s.memory 0x74fa4=table) (len : load32 s.memory (180+table+16)=19440)
    (ptrSafe : LengthSafe s 0x74fa4) (lenSafe : LengthSafe s (180+table+16)) :
    X86WordFillRoutine.Prefix program [] 7 (lengthOpened s) (measured s) := by
  have p := (length_frame s _ ptrSafe).trans pointer
  have l := (length_frame s _ lenSafe).trans len
  have sp : (lengthSaved s).regs 4=s.regs 4-8 := by
    simp [lengthSaved,lengthCalled,X86Routine.pushWord,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc]
  have edx : load32 (lengthSaved s).memory ((lengthSaved s).regs 4)=s.regs 2 := load_store _ _ _
  have ret : load32 (lengthSaved s).memory ((lengthSaved s).regs 4+4)=0x38d3c := by
    have sep : Apart (s.regs 4-4) (s.regs 4-8) := by
      simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using PlayerHeight.slots_apart (s.regs 4-8) 1 0 (by decide)
    simp only [BitVec.sub_eq_add_neg,BitVec.ofNat_eq_ofNat,BitVec.reduceNeg] at sep
    simp [lengthSaved,lengthCalled,X86Routine.pushWord,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,
      load_store_apart _ _ _ _ sep,load_store]
  unfold lengthOpened measured
  generalize ht : lengthSaved s=t at p l sp edx ret ⊢
  have restored : t.regs 4+8=s.regs 4 := by rw [sp]; exact BitVec.sub_add_cancel _ _
  simp only [BitVec.ofNat_eq_ofNat,BitVec.add_assoc] at p l ret edx restored
  have path : X86WordFillRoutine.Prefix missListing [] 7
      ⟨put t 2 9,.legacy (some (compare32 9 1264)),0x38bc9⟩
      ⟨put (put (put t 4 (s.regs 4)) 0 19440) 2 (s.regs 2),.legacy none,0x38d3c⟩ := by
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (middle:=⟨put (put (put t 4 (s.regs 4)) 0 19440) 2 (s.regs 2),.legacy none,0x38d3c⟩)
      (by simp) rfl ?_ (.nil _)
    simp [X86WordFillRoutine.execute,X86WordFillRoutine.embed,X86FillRoutine.execute,
      X86StartupRoutine.execute,X86ByteRoutine.execute,X86Routine.execute,X86Control.execute,
      X86Block.execute,X86Memory.execute,X86Block.Address.eval,X86.execute,blockPreservesFlags,
      put,write,p,l,edx,ret,BitVec.add_assoc,restored]
    funext r
    by_cases h0 : r=0 <;> by_cases h2 : r=2 <;> by_cases h4 : r=4 <;> simp [write,h0,h2,h4]
  exact path.transfer _ [] miss_decoded (by simp)

theorem miss_execution (s : X86Memory.State) (table : Word) (index : s.regs 1=9)
    (count : load32 s.memory 0x74fa0=1264) (pointer : load32 s.memory 0x74fa4=table)
    (len : load32 s.memory (180+table+16)=19440) (countSafe : LengthSafe s 0x74fa0)
    (ptrSafe : LengthSafe s 0x74fa4) (lenSafe : LengthSafe s (180+table+16)) :
    X86WordFillRoutine.Prefix program [] 14 ⟨s,.legacy (some (logical32 0)),0x38d35⟩ (request s) := by
  have tail : X86WordFillRoutine.Prefix missListing [] 1 (measured s) (request s) :=
    .step (by simp [measured]) rfl rfl (.nil _)
  exact (((miss_call_execution s index).trans (length_open_execution s count countSafe)).trans
    (length_return_execution s table pointer len ptrSafe lenSafe)).trans (tail.transfer _ [] miss_decoded (by simp))

theorem dispatched_frame (s : X86Memory.State) (f : Option Flags) (table cache : Word)
    (initial : E1M1AimSideEntry.Initial s table) (v : OriginalGroupHeap.View)
    (heap : E1M1AimSideAllocate.HeapInitial s v) (frame : E1M1AimSidePublish.AllocationFrame s v)
    (h : Nat) (small : h<8) (safe : Entry32Safe s v)
    (a : Word) (readSafe : ReadSafe s v a) :
    load32 (dispatched s h cache).core.memory a=load32 s.memory a := by
  exact (saved_frame _ a (entered_safe s f table initial v heap frame h small a readSafe)).trans
    (E1M1AimCacheCall.entry_frame s f table initial v heap frame h small safe a readSafe)

theorem dispatched_length_safe (s : X86Memory.State) (f : Option Flags) (table cache : Word)
    (initial : E1M1AimSideEntry.Initial s table) (v : OriginalGroupHeap.View)
    (heap : E1M1AimSideAllocate.HeapInitial s v) (frame : E1M1AimSidePublish.AllocationFrame s v)
    (h : Nat) (small : h<8) (a : Word) (readSafe : ReadSafe s v a) :
    LengthSafe (dispatched s h cache).core a := by
  have sp := (E1M1AimCacheCall.entry_registers s f table initial v heap frame h small).2.2.2.1
  have ds : (dispatched s h cache).core.regs 4=s.regs 4-52 := by
    simp [dispatched,branch,opened,saved,X86Routine.pushWord,put,write,sp,BitVec.sub_eq_add_neg,BitVec.add_assoc]
  have h56 := readSafe.nested.2 (s.regs 4-56) (by simp)
  have h60 := readSafe.output.1
  simpa [LengthSafe,ds,BitVec.sub_eq_add_neg,BitVec.add_assoc] using And.intro h56 h60

def requested (s : X86Memory.State) (h : Nat) (cache : Word) := request (dispatched s h cache).core

theorem miss_entry_execution (s : X86Memory.State) (f : Option Flags) (table cache : Word)
    (initial : E1M1AimSideEntry.Initial s table) (v : OriginalGroupHeap.View)
    (heap : E1M1AimSideAllocate.HeapInitial s v) (frame : E1M1AimSidePublish.AllocationFrame s v)
    (aligned : (v.block+24).extractLsb' 0 8 &&& 3=0) (safe : Entry32Safe s v)
    (inputs : CacheInitial s v cache) (miss : load32 s.memory (cache+36)=0)
    (pointerSafe : ReadSafe s v 0x74fa4) (lengthSafe : ReadSafe s v (180+table+16)) :
    ∃ h<8, (∃ n≤5331, X86WordFillRoutine.Prefix program [] n
      (X86WordFillRoutine.embed ⟨s,f,0x2e3e0⟩) (requested s h cache)) ∧
      (requested s h cache).pc=0x39690 ∧
      (requested s h cache).core.regs 0=19440 ∧
      (requested s h cache).core.regs 2=1 ∧
      (requested s h cache).core.regs 3=cache+36 ∧
      load32 (requested s h cache).core.memory ((requested s h cache).core.regs 4)=0x38d41 := by
  obtain ⟨h,small,⟨n,b,path⟩,pc,owner,_⟩ := entry_execution s f table cache initial v heap frame aligned safe inputs
  have keep := dispatched_frame s f table cache initial v heap frame h small safe
  have sep := dispatched_length_safe s f table cache initial v heap frame h small
  have index : (dispatched s h cache).core.regs 1=9 := by simp [dispatched,branch,opened,put,write]
  have tag : (dispatched s h cache).core.regs 2=1 := by
    have t := (E1M1AimCacheCall.entry_registers s f table initial v heap frame h small).2.1
    simpa [dispatched,branch,opened,saved,X86Routine.pushWord,put,write] using t
  have tail := miss_execution (dispatched s h cache).core table index
    ((keep _ inputs.countSafe).trans initial.count) ((keep _ pointerSafe).trans initial.tablePointer)
    ((keep _ lengthSafe).trans initial.length) (sep _ inputs.countSafe) (sep _ pointerSafe) (sep _ lengthSafe)
  have seam : (⟨(dispatched s h cache).core,.legacy (some (logical32 0)),0x38d35⟩ : X86WordFillRoutine.State)=dispatched s h cache := by
    simp only [dispatched,branch,miss,if_pos rfl,ite_true]
  rw [seam] at tail
  refine ⟨h,small,⟨n+14,by omega,path.trans tail⟩,rfl,rfl,?_,?_,?_⟩
  · simpa [requested,request,measured,lengthSaved,lengthCalled,X86Routine.pushWord,put,write] using tag
  · simpa [requested,request,measured,lengthSaved,lengthCalled,X86Routine.pushWord,put,write] using owner
  · exact load_store _ _ _

def hitListing : X86WordFillRoutine.Program
  | 0x38cab => some (op (.control (.cmpImmediate ⟨some 7,none,0,-12⟩ 0x1d4a11)),7)
  | 0x38cb2 => some (op (.control (.jumpZero true 18)),2)
  | 0x38cc6 => some (op (.control (.block (.load 0 ⟨none,none,0,0x74f94⟩))),5)
  | 0x38ccb => some (op (.control (.block (.load 0 ⟨some 0,some 1,2,0⟩))),3)
  | 0x38cce => some (op (.call 3293),5)
  | _ => none
theorem hit_decoded (pc : Nat) (h : hitListing pc≠none) : program pc=hitListing pc := by
  fun_cases hitListing pc <;> simp_all [hitListing] <;> decide
def tagCall (s : X86Memory.State) (raw : Word) : X86WordFillRoutine.State :=
  ⟨X86Routine.pushWord (put s 0 raw) 0x38cd3,.legacy (some (compare32 0x1d4a11 0x1d4a11)),0x399b0⟩
def tagRequested (s : X86Memory.State) (h : Nat) (cache : Word) :=
  tagCall (dispatched s h cache).core (load32 s.memory (cache+36))

theorem hit_execution (s : X86Memory.State) (f : X86WordFillRoutine.Knowledge) (cache raw : Word)
    (index : s.regs 1=9) (payload : s.regs 7=raw)
    (magic : load32 s.memory (raw-12)=0x1d4a11)
    (pointer : load32 s.memory 0x74f94=cache) (cell : load32 s.memory (cache+36)=raw) :
    X86WordFillRoutine.Prefix program [] 5 ⟨s,f,0x38cab⟩ (tagCall s raw) := by
  simp only [BitVec.ofNat_eq_ofNat,BitVec.sub_eq_add_neg,BitVec.reduceNeg] at index magic pointer cell
  have path : X86WordFillRoutine.Prefix hitListing [] 5 ⟨s,f,0x38cab⟩ (tagCall s raw) := by
    refine .step (middle:=⟨s,.legacy (some (compare32 0x1d4a11 0x1d4a11)),0x38cb2⟩) (by simp) rfl ?_ ?_
    · cases f <;> simp [X86WordFillRoutine.execute,X86WordFillRoutine.embed,X86WordFillRoutine.preserves,
        X86FillRoutine.execute,X86StartupRoutine.execute,X86ByteRoutine.execute,X86Routine.execute,
        X86Control.execute,X86Block.Address.eval,payload,magic]
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (middle:=tagCall s raw) (by simp) rfl ?_ (.nil _)
    simp [tagCall,X86WordFillRoutine.execute,X86WordFillRoutine.embed,X86FillRoutine.execute,
      X86StartupRoutine.execute,X86ByteRoutine.execute,X86Routine.execute,X86Control.execute,
      X86Block.execute,X86Memory.execute,X86Block.Address.eval,blockPreservesFlags,
      X86Routine.pushWord,put,write,index,pointer,cell,BitVec.add_comm]
  exact path.transfer _ [] hit_decoded (by simp)

theorem hit_entry_execution (s : X86Memory.State) (f : Option Flags) (table cache : Word)
    (initial : E1M1AimSideEntry.Initial s table) (v : OriginalGroupHeap.View)
    (heap : E1M1AimSideAllocate.HeapInitial s v) (frame : E1M1AimSidePublish.AllocationFrame s v)
    (aligned : (v.block+24).extractLsb' 0 8 &&& 3=0) (safe : Entry32Safe s v)
    (inputs : CacheInitial s v cache) (hit : load32 s.memory (cache+36)≠0)
    (magic : load32 s.memory (load32 s.memory (cache+36)-12)=0x1d4a11)
    (magicSafe : ReadSafe s v (load32 s.memory (cache+36)-12)) :
    ∃ h<8, (∃ n≤5322, X86WordFillRoutine.Prefix program [] n
      (X86WordFillRoutine.embed ⟨s,f,0x2e3e0⟩) (tagRequested s h cache)) ∧
      (tagRequested s h cache).pc=0x399b0 ∧
      (tagRequested s h cache).core.regs 0=load32 s.memory (cache+36) ∧
      (tagRequested s h cache).core.regs 2=1 ∧
      load32 (tagRequested s h cache).core.memory ((tagRequested s h cache).core.regs 4)=0x38cd3 := by
  obtain ⟨h,small,⟨n,b,path⟩,pc,_,payload⟩ := entry_execution s f table cache initial v heap frame aligned safe inputs
  have keep := dispatched_frame s f table cache initial v heap frame h small safe
  have index : (dispatched s h cache).core.regs 1=9 := by simp [dispatched,branch,opened,put,write]
  have tail := hit_execution (dispatched s h cache).core (dispatched s h cache).flags cache _ index payload
    ((keep _ magicSafe).trans magic) ((keep _ inputs.pointerSafe).trans inputs.pointer) (keep _ inputs.cellSafe)
  have seam : (⟨(dispatched s h cache).core,(dispatched s h cache).flags,0x38cab⟩ : X86WordFillRoutine.State)=dispatched s h cache := by
    rw [if_neg hit] at pc
    rw [←pc]
  rw [seam] at tail
  refine ⟨h,small,⟨n+5,by omega,path.trans tail⟩,rfl,rfl,?_,load_store _ _ _⟩
  have tag := (E1M1AimCacheCall.entry_registers s f table initial v heap frame h small).2.1
  simpa [tagRequested,tagCall,dispatched,branch,opened,saved,X86Routine.pushWord,put,write] using tag

/-- Ordered stores preserve the full zero image only after static separation.
This is a memory summary, never a replacement of the executable store ordering. -/
theorem zero_writes (ws : List (Word × Word)) (m : Memory) (base : Word) (n : Nat)
    (image : ∃ old, m=E1M1AimWordFill.zeros old base n)
    (safe : ∀ w∈ws, ∀ k<n, Apart w.1 (base+BitVec.ofNat 32 (4*k))) :
    ∃ old, HeapWrites.apply ws m=E1M1AimWordFill.zeros old base n := by
  induction ws generalizing m with
  | nil => exact image
  | cons w ws ih =>
    obtain ⟨old,hm⟩ := image
    have step : ∃ next, store32 m w.1 w.2=E1M1AimWordFill.zeros next base n := by
      rw [hm,E1M1AimWordAligned.zeros_store_comm _ _ _ _ _ (safe w (by simp))]
      exact ⟨_,rfl⟩
    exact ih _ step (fun z hz=>safe z (by simp [hz]))

theorem output_slot (s : X86Memory.State) (v : OriginalGroupHeap.View) (safe : Entry32Safe s v)
    (a : Word) (ha : a∈[s.regs 4-40,s.regs 4-44,s.regs 4-48,s.regs 4-52,s.regs 4-56,s.regs 4-60]) :
    ∀ k<2916, Apart a (v.block+24+BitVec.ofNat 32 (4*k)) := by
  intro k hk
  have h0 := safe ⟨0,by decide⟩ k hk
  have h1 := safe ⟨1,by decide⟩ k hk
  have h2 := safe ⟨2,by decide⟩ k hk
  have h3 := safe ⟨3,by decide⟩ k hk
  have h4 := safe ⟨4,by decide⟩ k hk
  have h5 := safe ⟨5,by decide⟩ k hk
  simp only [Fin.val_mk] at h0 h1 h2 h3 h4 h5
  simp [BitVec.sub_eq_add_neg,BitVec.add_assoc] at h0 h1 h2 h3 h4 h5 ha ⊢
  rcases ha with ha|ha|ha|ha|ha|ha <;> subst a
  · exact h5
  · exact h4
  · exact h3
  · exact h2
  · exact h1
  · exact h0

theorem output_preserved (s : X86Memory.State) (f : Option Flags) (table cache : Word)
    (initial : E1M1AimSideEntry.Initial s table) (v : OriginalGroupHeap.View)
    (heap : E1M1AimSideAllocate.HeapInitial s v) (frame : E1M1AimSidePublish.AllocationFrame s v)
    (h : Nat) (small : h<8) (safe : Entry32Safe s v) :
    (∀ j<11664, (dispatched s h cache).core.memory (v.block+24+BitVec.ofNat 32 j)=0) ∧
    (∀ j<11664, (requested s h cache).core.memory (v.block+24+BitVec.ofNat 32 j)=0) ∧
    (∀ j<11664, (tagRequested s h cache).core.memory (v.block+24+BitVec.ofNat 32 j)=0) := by
  have sp := (E1M1AimCacheCall.entry_registers s f table initial v heap frame h small).2.2.2.1
  have tag := (E1M1AimCacheCall.entry_registers s f table initial v heap frame h small).2.1
  let ws := [(s.regs 4-40,(entered s h).core.regs 3),(s.regs 4-44,(entered s h).core.regs 1),
    (s.regs 4-48,(entered s h).core.regs 6),(s.regs 4-52,(entered s h).core.regs 7)]
  have sm : (dispatched s h cache).core.memory=HeapWrites.apply ws (entered s h).core.memory := by
    simp [ws,dispatched,branch,opened,saved,HeapWrites.apply,X86Routine.pushWord,put,write,sp,
      BitVec.sub_eq_add_neg,BitVec.add_assoc]
  have guard : ∀ w∈ws, ∀ k<2916, Apart w.1 (v.block+24+BitVec.ofNat 32 (4*k)) := by
    intro w hw
    apply output_slot s v safe w.1
    simp [ws] at hw
    rcases hw with hw|hw|hw|hw <;> subst w <;> simp
  have zi := zero_writes ws (entered s h).core.memory (v.block+24) 2916
    (E1M1AimCacheCall.entry_memory s f table initial v heap frame h small safe) guard
  rw [←sm] at zi
  have ds : (dispatched s h cache).core.regs 4=s.regs 4-52 := by
    simp [dispatched,branch,opened,saved,X86Routine.pushWord,put,write,sp,BitVec.sub_eq_add_neg,BitVec.add_assoc]
  let mw := [(s.regs 4-56,(0x38d3c:Word)),(s.regs 4-60,(dispatched s h cache).core.regs 2),(s.regs 4-56,0x38d41)]
  have mm : (requested s h cache).core.memory=HeapWrites.apply mw (dispatched s h cache).core.memory := by
    simp [requested,request,measured,lengthSaved,lengthCalled,mw,HeapWrites.apply,X86Routine.pushWord,
      put,write,ds,BitVec.sub_eq_add_neg,BitVec.add_assoc]
  have mg : ∀ w∈mw, ∀ k<2916, Apart w.1 (v.block+24+BitVec.ofNat 32 (4*k)) := by
    intro w hw
    apply output_slot s v safe w.1
    simp [mw] at hw
    rcases hw with hw|hw|hw <;> subst w <;> simp
  have mi := zero_writes mw _ (v.block+24) 2916 zi mg
  rw [←mm] at mi
  have hm : (tagRequested s h cache).core.memory=HeapWrites.apply [(s.regs 4-56,0x38cd3)] (dispatched s h cache).core.memory := by
    simp [tagRequested,tagCall,HeapWrites.apply,X86Routine.pushWord,put,write,ds,BitVec.sub_eq_add_neg,BitVec.add_assoc]
  have hi := zero_writes [(s.regs 4-56,0x38cd3)] _ (v.block+24) 2916 zi (by
    intro w hw
    have eq : w=(s.regs 4-56,0x38cd3) := by simpa using hw
    subst w
    exact output_slot s v safe _ (by simp))
  rw [←hm] at hi
  obtain ⟨a,ha⟩ := zi
  obtain ⟨b,hb⟩ := mi
  obtain ⟨c,hc⟩ := hi
  exact ⟨fun j hj=>by rw [ha]; exact E1M1AimWordFill.zeros_byte _ _ 2916 j hj,
    fun j hj=>by rw [hb]; exact E1M1AimWordFill.zeros_byte _ _ 2916 j hj,
    fun j hj=>by rw [hc]; exact E1M1AimWordFill.zeros_byte _ _ 2916 j hj⟩

theorem request_frame (s : X86Memory.State) (a : Word) (safe : LengthSafe s a) :
    load32 (request s).core.memory a=load32 s.memory a := by
  apply (load_store_apart _ _ _ _ safe.1).trans
  exact length_frame s a safe

/-- Preserve the *produced* first-allocation metadata, not an invented next heap.
The next allocation view must be derived from this reached predecessor image. -/
theorem request_allocation_frame (s : X86Memory.State) (f : Option Flags) (table cache : Word)
    (initial : E1M1AimSideEntry.Initial s table) (v : OriginalGroupHeap.View)
    (heap : E1M1AimSideAllocate.HeapInitial s v) (frame : E1M1AimSidePublish.AllocationFrame s v)
    (h : Nat) (small : h<8) (safe : Entry32Safe s v) (a : Word)
    (nested : E1M1AimSideMemset.EntrySafe s a) (output : OutputSafe s v a) :
    load32 (requested s h cache).core.memory a=load32 (E1M1AimSideAllocate.allocated s).core.memory a := by
  have sp := (E1M1AimCacheCall.entry_registers s f table initial v heap frame h small).2.2.2.1
  have ds : (dispatched s h cache).core.regs 4=s.regs 4-52 := by
    simp [dispatched,branch,opened,saved,X86Routine.pushWord,put,write,sp,BitVec.sub_eq_add_neg,BitVec.add_assoc]
  have esafe : Safe (entered s h).core a := by
    unfold Safe
    rw [sp]
    intro b hb
    apply nested.2 b
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc,List.mem_cons,List.mem_singleton] at hb ⊢
    rcases hb with hb|hb|hb|hb <;> simp_all
  have msafe : LengthSafe (dispatched s h cache).core a := by
    have h56 := nested.2 (s.regs 4-56) (by simp)
    simpa [LengthSafe,ds,BitVec.sub_eq_add_neg,BitVec.add_assoc] using And.intro h56 output.1
  have fs := (E1M1AimWordAligned.entry_registers s f table initial v heap frame h small).2.2.2.2
  have callSafe : Apart a ((E1M1AimWordAligned.finished s h).core.regs 4-4) := by
    rw [fs]
    simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using nested.2 (s.regs 4-36) (by simp)
  exact (request_frame _ a msafe).trans ((saved_frame _ a esafe).trans
    ((E1M1AimCacheCall.call_frame _ a callSafe).trans
    ((E1M1AimWordAligned.entry_nested_frame s f table initial v heap frame h small safe a output.1 output.2).trans
      (E1M1AimSideMemset.allocation_frame s f table initial v heap a nested))))
end Doom.Proofs.E1M1AimCacheDispatch
