import Doom.Proofs.E1M1AimSideAllocate
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1AimSidePublish
open Verification X86 X86Memory X86Control BlockSummary
open E1M1AimSideEntry (request Initial savedMemory)
open E1M1AimSideAllocate (allocated candidate selected HeapInitial)
open OriginalGroupHeap (View Separated splitWrites)
open OriginalGroupMallocEntry (saved prepared rounded)
/-! Static write frames for the actual selected allocation. These conditions refer
only to original addresses, never to a reached image or successful helper. -/
def MetadataSafe (v : View) (a : Word) : Prop :=
  Separated a (splitWrites v 11664) ∧
  Separated a [v.block+4,v.block+8,v.zone+28,v.block+12]
def SaveSafe (s : X86Memory.State) (a : Word) : Prop :=
  Separated a [s.regs 4-40,s.regs 4-44,s.regs 4-48,s.regs 4-52]
def InitialSafe (s : X86Memory.State) (v : View) (a : Word) : Prop :=
  E1M1AimSideAllocate.PrefixSafe s a ∧ MetadataSafe v a
/-- All six caller saves plus the original caller return. Scratch slots are not
mistaken for saved inputs; their eventual raw-pointer assignment is still open. -/
def upperWords (s : X86Memory.State) : List Word :=
  [s.regs 4-24,s.regs 4-20,s.regs 4-16,s.regs 4-12,s.regs 4-8,s.regs 4-4,s.regs 4]
structure AllocationFrame (s : X86Memory.State) (v : View) : Prop where
  countStack : SaveSafe s 0x2c11c
  countHeap : MetadataSafe v 0x2c11c
  registers : ∀ a∈[s.regs 4-40,s.regs 4-44,s.regs 4-48,s.regs 4-52], MetadataSafe v a
  upper : ∀ a∈upperWords s,
    Apart a 0x2c11c ∧ Apart a (s.regs 4-36) ∧ SaveSafe s a ∧ MetadataSafe v a

theorem metadata_frame (s : X86Memory.State) (v : View) (heap : HeapInitial s v)
    (a : Word) (safe : MetadataSafe v a) :
    load32 (allocated s).core.memory a=load32 (candidate s).core.memory a := by
  have cf := E1M1AimSideAllocate.fields s v heap
  have hf := v.fields _ cf.2.2.2
  have args := E1M1AimSideAllocate.arguments s
  generalize ht : (candidate s).core=t at cf hf args ⊢
  let p := OriginalGroupSelected.picked t
  have pb : p.regs 3=v.block := by simpa [p,OriginalGroupSelected.picked,put,write] using cf.2.2.1
  have pr : p.regs 1=rounded 11664 := by simpa [p,OriginalGroupSelected.picked,put,write] using args.1
  have pn : load32 p.memory (v.block+16)=v.next := hf.2.2.2.2.2.2.2
  have ns := OriginalGroupHeap.successor v p pb pr pn heap.successor
  have ss := OriginalGroupHeap.split_safe v p a pb pr ns safe.1
  have zs := OriginalGroupHeap.split_safe v p 0x74fe0 pb pr ns heap.zoneSplit
  have ab : (OriginalGroupSelected.allocated t).core.regs 3=v.block :=
    (OriginalGroupSelected.allocated_registers t 3 (by decide) (by decide)).trans cf.2.2.1
  have az : OriginalGroupAllocation.zone (OriginalGroupSelected.allocated t).core=v.zone := by
    unfold OriginalGroupAllocation.zone OriginalGroupAllocation.owned
    rw [ab,load_store_apart _ _ _ _ heap.zoneOwner]
    exact (OriginalGroupSelected.allocated_frame t 0x74fe0 zs).trans hf.1
  have tail : OriginalGroupAllocation.SafeWord a (OriginalGroupSelected.allocated t).core := by
    simpa [OriginalGroupAllocation.SafeWord,ab,az,Separated] using safe.2
  have result := (OriginalGroupAllocation.returned_frame (OriginalGroupSelected.allocated t).core a tail).trans
    (OriginalGroupSelected.allocated_frame t a ss)
  change load32 (OriginalGroupAllocation.returned (OriginalGroupSelected.allocated (candidate s).core).core).core.memory a=_
  rw [ht]; exact result

theorem request_frame (s : X86Memory.State) (v : View) (heap : HeapInitial s v)
    (a : Word) (stack : SaveSafe s a) (safe : MetadataSafe v a) :
    load32 (allocated s).core.memory a=load32 (request s).core.memory a := by
  apply (metadata_frame s v heap a safe).trans
  change load32 (saved (request s).core).memory a=_
  apply OriginalGroupMallocEntry.saved_frame
  simpa [OriginalGroupMallocEntry.SafeWord,SaveSafe,Separated,request,E1M1AimSideEntry.measured,
    E1M1AimSideEntry.called,X86Routine.pushWord,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc] using stack

theorem allocation_frame (s : X86Memory.State) (v : View) (heap : HeapInitial s v)
    (a : Word) (safe : InitialSafe s v a) :
    load32 (allocated s).core.memory a=load32 s.memory a := by
  exact (metadata_frame s v heap a safe.2).trans (E1M1AimSideAllocate.prefix_frame s a safe.1)

theorem allocation_upper (s : X86Memory.State) (v : View) (heap : HeapInitial s v)
    (frame : AllocationFrame s v) (a : Word) (ha : a∈upperWords s) :
    load32 (allocated s).core.memory a=load32 (savedMemory s) a := by
  obtain ⟨count,ret,stack,metadata⟩ := frame.upper a ha
  apply (request_frame s v heap a stack metadata).trans
  have mem : (request s).core.memory=store32 (store32 (savedMemory s) 0x2c11c 648) (s.regs 4-36) 0x2e415 := by
    simp [request,E1M1AimSideEntry.measured,E1M1AimSideEntry.called,savedMemory,
      E1M1AimSideEntry.saves,HeapWrites.apply,X86Routine.pushWord,put,write,
      BitVec.sub_eq_add_neg,BitVec.add_assoc]
  rw [mem]
  exact (load_store_apart _ _ _ _ ret).trans (load_store_apart _ _ _ _ count)

private theorem saved_registers (s : X86Memory.State) :
    load32 (saved s).memory (s.regs 4-4)=s.regs 1 ∧
    load32 (saved s).memory (s.regs 4-8)=s.regs 6 ∧
    load32 (saved s).memory (s.regs 4-12)=s.regs 7 ∧
    load32 (saved s).memory (s.regs 4-16)=s.regs 5 := by
  have sep (a b : Fin 8) (h : a≠b) :
      Apart (s.regs 4-16+BitVec.ofNat 32 (4*a.val)) (s.regs 4-16+BitVec.ofNat 32 (4*b.val)) :=
    PlayerHeight.slots_apart _ a b h
  have a := sep 3 2 (by decide); have b := sep 3 1 (by decide); have c := sep 3 0 (by decide)
  have d := sep 2 1 (by decide); have e := sep 2 0 (by decide); have f := sep 1 0 (by decide)
  change Apart (s.regs 4-16+12) (s.regs 4-16+8) at a
  change Apart (s.regs 4-16+12) (s.regs 4-16+4) at b
  change Apart (s.regs 4-16+12) (s.regs 4-16+0) at c
  simp [BitVec.sub_eq_add_neg,BitVec.add_assoc] at a b c d e f
  simp [saved,X86Routine.pushWord,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,
    load_store_apart _ _ _ _ a,load_store_apart _ _ _ _ b,load_store_apart _ _ _ _ c,
    load_store_apart _ _ _ _ d,load_store_apart _ _ _ _ e,load_store_apart _ _ _ _ f,load_store]

theorem allocation_inputs (s : X86Memory.State) (table : Word) (h : Initial s table)
    (v : View) (heap : HeapInitial s v) (frame : AllocationFrame s v) :
    load32 (allocated s).core.memory 0x2c11c=648 ∧
    (allocated s).core.regs 1=9 ∧ (allocated s).core.regs 5=s.regs 5 ∧
    (allocated s).core.regs 6=s.regs 6 ∧ (allocated s).core.regs 7=s.regs 7 := by
  have count := (request_frame s v heap 0x2c11c frame.countStack frame.countHeap).trans
    (E1M1AimSideEntry.request_observations s table h).2.2.2.2.2
  have regs := saved_registers (request s).core
  have rsp : (request s).core.regs 4=s.regs 4-36 := by
    simp [request,E1M1AimSideEntry.measured,E1M1AimSideEntry.called,X86Routine.pushWord,put,write,
      BitVec.sub_eq_add_neg,BitVec.add_assoc]
  have original : (request s).core.regs 1=9 ∧ (request s).core.regs 5=s.regs 5 ∧
      (request s).core.regs 6=s.regs 6 ∧ (request s).core.regs 7=s.regs 7 := by
    simp [request,E1M1AimSideEntry.measured,E1M1AimSideEntry.called,X86Routine.pushWord,put,write,h.index]
  rw [rsp] at regs
  simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc] at regs
  have keeps (a : Word) (ha : a∈[s.regs 4-40,s.regs 4-44,s.regs 4-48,s.regs 4-52]) :=
    metadata_frame s v heap a (frame.registers a ha)
  have k1 := keeps (s.regs 4-40) (by simp)
  have k6 := keeps (s.regs 4-44) (by simp)
  have k7 := keeps (s.regs 4-48) (by simp)
  have k5 := keeps (s.regs 4-52) (by simp)
  change load32 (allocated s).core.memory _=load32 (saved (request s).core).memory _ at k1 k6 k7 k5
  simp only [BitVec.sub_eq_add_neg] at k1 k6 k7 k5
  have v1 := k1.trans (regs.1.trans original.1)
  have v6 := k6.trans (regs.2.1.trans original.2.2.1)
  have v7 := k7.trans (regs.2.2.1.trans original.2.2.2)
  have v5 := k5.trans (regs.2.2.2.trans original.2.1)
  have sp : (selected s).core.regs 4=s.regs 4-52 :=
    (OriginalGroupSelected.allocated_registers (candidate s).core 4 (by decide) (by decide)).trans
      (E1M1AimSideAllocate.arguments s).2.2.2
  have restored (t : X86Memory.State) :
      (OriginalGroupAllocation.returned t).core.regs 1=load32 (OriginalGroupAllocation.returned t).core.memory (t.regs 4+12) ∧
      (OriginalGroupAllocation.returned t).core.regs 5=load32 (OriginalGroupAllocation.returned t).core.memory (t.regs 4) ∧
      (OriginalGroupAllocation.returned t).core.regs 6=load32 (OriginalGroupAllocation.returned t).core.memory (t.regs 4+8) ∧
      (OriginalGroupAllocation.returned t).core.regs 7=load32 (OriginalGroupAllocation.returned t).core.memory (t.regs 4+4) := by
    simp [OriginalGroupAllocation.returned,OriginalGroupAllocation.restored,OriginalGroupAllocation.pop,
      OriginalGroupAllocation.committed,put,write,BitVec.add_assoc]
  have rr := restored (selected s).core
  change (allocated s).core.regs 1=_ ∧ (allocated s).core.regs 5=_ ∧
    (allocated s).core.regs 6=_ ∧ (allocated s).core.regs 7=_ at rr
  rw [sp] at rr
  simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc] at rr
  exact ⟨count,rr.1.trans v1,rr.2.1.trans v5,rr.2.2.1.trans v6,rr.2.2.2.trans v7⟩

def publish (s : X86Memory.State) : X86Control.State :=
  ⟨X86Routine.pushWord (put (put (put
    {s with memory:=store32 s.memory 0x2c118 (s.regs 0)} 6 11664) 2 0) 3 11664) 0x2e437,
    none,0x3fe70⟩
def published (s : X86Memory.State) := publish (allocated s).core

def listed : X86StartupRoutine.Program
  | 0x2e415 => some (.base (.base (.control (.block (.legacy (.mov 3 0))))),2)
  | 0x2e417 => some (.base (.base (.control (.storeEax 0x2c118))),5)
  | 0x2e41c => some (.base (.base (.control (.block (.load 0 ⟨none,none,0,0x2c11c⟩)))),5)
  | 0x2e421 => some (.base (.base (.control (.block (.lea 6 ⟨none,some 0,3,0⟩)))),7)
  | 0x2e428 => some (.base (.base (.control (.block (.arithmetic (.add 6 0))))),2)
  | 0x2e42a => some (.base (.base (.xorRegister 2 2)),2)
  | 0x2e42c => some (.base (.base (.control (.block (.arithmetic (.add 6 6))))),2)
  | 0x2e42e => some (.base (.base (.control (.block (.legacy (.mov 0 3))))),2)
  | 0x2e430 => some (.base (.base (.control (.block (.legacy (.mov 3 6))))),2)
  | 0x2e432 => some (.base (.base (.call 72249)),5)
  | _ => none

theorem decoded (pc : Nat) (h : listed pc≠none) :
    E1M1AimSideAllocate.program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

theorem publish_execution (s : X86Memory.State) (f : Option Flags)
    (count : load32 s.memory 0x2c11c=648) :
    X86StartupRoutine.Prefix E1M1AimSideAllocate.program [] 10 ⟨s,f,0x2e415⟩ (publish s) := by
  have c : load32 (store32 s.memory 0x2c118 (s.regs 0)) 0x2c11c=648 :=
    (load_store_apart _ _ _ _ (by unfold Apart; decide +kernel)).trans count
  simp only [BitVec.ofNat_eq_ofNat] at c
  have path : X86StartupRoutine.Prefix listed [] 10 ⟨s,f,0x2e415⟩ (publish s) := by
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (middle:=publish s) (by simp) rfl ?_ (.nil _)
    simp [X86StartupRoutine.execute,X86ByteRoutine.execute,X86Routine.execute,
      X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,
      X86.execute,blockPreservesFlags,publish,X86Routine.pushWord,put,write,c]
    funext r
    by_cases a : r=0 <;> by_cases b : r=2 <;> by_cases c : r=3 <;>
      by_cases d : r=4 <;> by_cases e : r=6 <;> simp [write,a,b,c,d,e]
  exact path.transfer _ [] decoded (by simp)

theorem execution (s : X86Memory.State) (f : Option Flags) (table : Word)
    (h : Initial s table) (v : View) (heap : HeapInitial s v) (frame : AllocationFrame s v) :
    (∃ n≤100, X86StartupRoutine.Prefix E1M1AimSideAllocate.program [] n
      ⟨s,f,0x2e3e0⟩ (published s)) ∧ (published s).pc=0x3fe70 ∧
      (published s).core.regs 0=v.block+24 ∧ (published s).core.regs 1=9 ∧
      (published s).core.regs 2=0 ∧ (published s).core.regs 3=11664 ∧
      (published s).core.regs 4=s.regs 4-36 ∧
      load32 (published s).core.memory ((published s).core.regs 4)=0x2e437 := by
  obtain ⟨⟨n,hn,path⟩,pc,base,sp⟩ := E1M1AimSideAllocate.execution s f table h v heap
  have inputs := allocation_inputs s table h v heap frame
  have suffix := publish_execution (allocated s).core (allocated s).flags inputs.1
  have seam : (⟨(allocated s).core,(allocated s).flags,0x2e415⟩ : X86Control.State)=allocated s := by rw [←pc]
  rw [seam] at suffix
  refine ⟨⟨n+10,by omega,path.trans suffix⟩,rfl,?_,?_,rfl,rfl,?_,?_⟩
  · simpa [published,publish,X86Routine.pushWord,put,write] using base
  · simpa [published,publish,X86Routine.pushWord,put,write] using inputs.2.1
  · simp [published,publish,X86Routine.pushWord,put,write,sp,BitVec.sub_eq_add_neg,BitVec.add_assoc]
  · exact load_store _ _ _

theorem published_frame (s : X86Memory.State) (a : Word)
    (base : Apart a 0x2c118) (stack : Apart a ((allocated s).core.regs 4-4)) :
    load32 (published s).core.memory a=load32 (allocated s).core.memory a := by
  exact (load_store_apart _ _ _ _ stack).trans (load_store_apart _ _ _ _ base)

theorem published_count (s : X86Memory.State) (f : Option Flags) (table : Word)
    (h : Initial s table) (v : View) (heap : HeapInitial s v) (frame : AllocationFrame s v) :
    load32 (published s).core.memory 0x2c11c=648 := by
  have sp := (E1M1AimSideAllocate.execution s f table h v heap).2.2.2
  apply (published_frame s 0x2c11c (by unfold Apart; decide +kernel) ?_).trans (allocation_inputs s table h v heap frame).1
  rw [sp]; simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using h.countReturn

theorem published_base (s : X86Memory.State) (f : Option Flags) (table : Word)
    (h : Initial s table) (v : View) (heap : HeapInitial s v)
    (safe : Apart 0x2c118 (s.regs 4-36)) :
    load32 (published s).core.memory 0x2c118=v.block+24 := by
  have obs := E1M1AimSideAllocate.execution s f table h v heap
  have sep : Apart 0x2c118 ((allocated s).core.regs 4-4) := by
    rw [obs.2.2.2]; simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe
  exact (load_store_apart _ _ _ _ sep).trans ((load_store _ _ _).trans obs.2.2.1)
end Doom.Proofs.E1M1AimSidePublish
