import Doom.Proofs.E1M1AimWordAligned
/-! The actual four-instruction cache caller after the completed memset.
The CALL overwrites originalESP-36. Its separation from all output words is
DERIVED from Entry32Safe slot six. No cache hit, miss or loaded image assumed. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1AimCacheCall
open Verification X86 X86Memory X86Control BlockSummary
open E1M1AimWordFill (zeros Entry32Safe OutputSafe)
open E1M1AimWordAligned (finished)
def program := E1M1AimWordFill.program
def listed : X86WordFillRoutine.Program
  | 0x2e437 => some (E1M1AimWordFill.op (.immediate 2 1),5)
  | 0x2e43c => some (E1M1AimWordFill.op (.control (.block (.legacy (.mov 0 1)))),2)
  | 0x2e43e => some (E1M1AimWordFill.op (.xorRegister 5 5),2)
  | 0x2e440 => some (E1M1AimWordFill.op (.call 43195),5)
  | _ => none
theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def called (s : X86Memory.State) : X86WordFillRoutine.State :=
  ⟨X86Routine.pushWord (put (put (put s 2 1) 0 (s.regs 1)) 5 0) 0x2e445,
    .legacy (some (logical32 0)),0x38d00⟩
def entered (s : X86Memory.State) (h : Nat) := called (finished s h).core

theorem call_execution (s : X86Memory.State) (f : X86WordFillRoutine.Knowledge) :
    X86WordFillRoutine.Prefix program [] 4 ⟨s,f,0x2e437⟩ (called s) := by
  have path : X86WordFillRoutine.Prefix listed [] 4 ⟨s,f,0x2e437⟩ (called s) := by
    cases f <;>
      (refine .step (by simp) rfl rfl ?_
       refine .step (by simp) rfl rfl ?_
       refine .step (by simp) rfl rfl ?_
       refine .step (middle:=called s) (by simp) rfl ?_ (.nil _)
       simp [called,X86WordFillRoutine.execute,X86WordFillRoutine.embed,X86WordFillRoutine.preserves,
         X86FillRoutine.execute,X86StartupRoutine.execute,X86ByteRoutine.execute,X86Routine.execute,
         X86Control.execute,X86Block.execute,X86Memory.execute,blockPreservesFlags,
         X86Routine.pushWord,put,write,logical32])
  exact path.transfer _ [] decoded (by simp)

theorem call_frame (s : X86Memory.State) (a : Word) (safe : Apart a (s.regs 4-4)) :
    load32 (called s).core.memory a=load32 s.memory a := by
  exact load_store_apart _ _ _ _ safe

theorem entry_registers (s : X86Memory.State) (f : Option Flags) (table : Word)
    (initial : E1M1AimSideEntry.Initial s table) (v : OriginalGroupHeap.View)
    (heap : E1M1AimSideAllocate.HeapInitial s v) (frame : E1M1AimSidePublish.AllocationFrame s v)
    (h : Nat) (small : h<8) :
    (entered s h).core.regs 0=9 ∧ (entered s h).core.regs 2=1 ∧
    (entered s h).core.regs 5=0 ∧ (entered s h).core.regs 4=s.regs 4-36 ∧
    load32 (entered s h).core.memory (s.regs 4-36)=0x2e445 := by
  have r := E1M1AimWordAligned.entry_registers s f table initial v heap frame h small
  have sp : (finished s h).core.regs 4-4=s.regs 4-36 := by
    rw [r.2.2.2.2]; simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  simp only [BitVec.ofNat_eq_ofNat] at sp
  simp only [entered,called,X86Routine.pushWord,put,write]
  simp only [ite_true,show (0:Reg)≠4 by decide,show (0:Reg)≠5 by decide,
    show (2:Reg)≠4 by decide,show (2:Reg)≠5 by decide,show (2:Reg)≠0 by decide,
    show (5:Reg)≠4 by decide,show (4:Reg)≠5 by decide,show (4:Reg)≠0 by decide,
    show (4:Reg)≠2 by decide,ite_false,r.2.1,sp]
  simp only [BitVec.ofNat_eq_ofNat,load_store,and_self]

theorem entry_memory (s : X86Memory.State) (f : Option Flags) (table : Word)
    (initial : E1M1AimSideEntry.Initial s table) (v : OriginalGroupHeap.View)
    (heap : E1M1AimSideAllocate.HeapInitial s v) (frame : E1M1AimSidePublish.AllocationFrame s v)
    (h : Nat) (small : h<8) (safe : Entry32Safe s v) :
    ∃ m, (entered s h).core.memory=zeros m (v.block+24) 2916 := by
  obtain ⟨_,_,base,_,_,_,sp,_⟩ := E1M1AimSidePublish.execution s f table initial v heap frame
  have ss : E1M1AimWordFill.Saved32Safe (E1M1AimSidePublish.published s).core := by
    simpa [E1M1AimWordFill.Saved32Safe,Entry32Safe,sp,base,BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe
  have bm := E1M1AimWordAligned.body_memory (E1M1AimSideMemset.wordsCalled
    (E1M1AimSidePublish.published s).core).core h small (E1M1AimWordAligned.nested_body_safe _ ss)
  have wz : (E1M1AimSideMemset.wordsCalled (E1M1AimSidePublish.published s).core).core.regs 0=v.block+24 := by
    simp [E1M1AimSideMemset.wordsCalled,E1M1AimSideMemset.callWords,E1M1AimSideMemset.fillCalled,
      X86Routine.pushWord,put,write,base]
  rw [wz] at bm
  have fm : (finished s h).core.memory=_ := bm
  have r := E1M1AimWordAligned.entry_registers s f table initial v heap frame h small
  have mem : (entered s h).core.memory=store32 (finished s h).core.memory (s.regs 4-36) 0x2e445 := by
    simp [entered,called,X86Routine.pushWord,put,write,r.2.2.2.2,BitVec.sub_eq_add_neg,BitVec.add_assoc]
  have sep : ∀ k<2916, Apart (s.regs 4-36) (v.block+24+BitVec.ofNat 32 (4*k)) := by
    intro k hk
    have q := safe (6 : Fin 7) k hk
    change Apart (s.regs 4-60+24) _ at q
    simpa only [BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd] using q
  rw [mem,fm,E1M1AimWordAligned.zeros_store_comm _ _ _ _ _ sep]
  exact ⟨_,rfl⟩

theorem entry_execution (s : X86Memory.State) (f : Option Flags) (table : Word)
    (initial : E1M1AimSideEntry.Initial s table) (v : OriginalGroupHeap.View)
    (heap : E1M1AimSideAllocate.HeapInitial s v) (frame : E1M1AimSidePublish.AllocationFrame s v)
    (aligned : (v.block+24).extractLsb' 0 8 &&& 3=0) (safe : Entry32Safe s v) :
    ∃ h<8, (∃ n≤5304, X86WordFillRoutine.Prefix program [] n
      (X86WordFillRoutine.embed ⟨s,f,0x2e3e0⟩) (entered s h)) ∧
      (entered s h).pc=0x38d00 ∧
      (entered s h).core.regs 0=9 ∧ (entered s h).core.regs 2=1 ∧
      (entered s h).core.regs 5=0 ∧ (entered s h).core.regs 4=s.regs 4-36 ∧
      load32 (entered s h).core.memory (s.regs 4-36)=0x2e445 ∧
      ∀ j<11664, (entered s h).core.memory (v.block+24+BitVec.ofNat 32 j)=0 := by
  obtain ⟨h,small,⟨n,b,path⟩,pc,_⟩ := E1M1AimWordAligned.entry_execution s f table initial v heap frame aligned safe
  have tail := call_execution (finished s h).core (finished s h).flags
  have seam : (⟨(finished s h).core,(finished s h).flags,0x2e437⟩ : X86WordFillRoutine.State)=finished s h := by rw [←pc]
  rw [seam] at tail
  obtain ⟨eax,edx,ebp,sp,ret⟩ := entry_registers s f table initial v heap frame h small
  refine ⟨h,small,⟨n+4,by omega,path.trans tail⟩,rfl,eax,edx,ebp,sp,ret,?_⟩
  obtain ⟨m,mem⟩ := entry_memory s f table initial v heap frame h small safe
  intro j hj
  rw [mem]
  exact E1M1AimWordFill.zeros_byte m (v.block+24) 2916 j hj
/-- Original-address guards only, shared by directory/cache/heap words. -/
structure ReadSafe (s : X86Memory.State) (v : OriginalGroupHeap.View) (a : Word) : Prop where
  allocation : E1M1AimSidePublish.InitialSafe s v a
  nested : E1M1AimSideMemset.EntrySafe s a
  output : OutputSafe s v a

theorem entry_frame (s : X86Memory.State) (f : Option Flags) (table : Word)
    (initial : E1M1AimSideEntry.Initial s table) (v : OriginalGroupHeap.View)
    (heap : E1M1AimSideAllocate.HeapInitial s v) (frame : E1M1AimSidePublish.AllocationFrame s v)
    (h : Nat) (small : h<8) (safe : Entry32Safe s v)
    (a : Word) (readSafe : ReadSafe s v a) :
    load32 (entered s h).core.memory a=load32 s.memory a := by
  have sp := (E1M1AimWordAligned.entry_registers s f table initial v heap frame h small).2.2.2.2
  have guard : Apart a ((finished s h).core.regs 4-4) := by
    rw [sp]
    simpa only [BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd] using
      readSafe.nested.2 (s.regs 4-36) (by simp)
  exact (call_frame _ a guard).trans
    ((E1M1AimWordAligned.entry_nested_frame s f table initial v heap frame h small safe a
      readSafe.output.1 readSafe.output.2).trans
    ((E1M1AimSideMemset.allocation_frame s f table initial v heap a readSafe.nested).trans
      (E1M1AimSidePublish.allocation_frame s v heap a readSafe.allocation)))
end Doom.Proofs.E1M1AimCacheCall
