import Doom.Proofs.E1M1AimSideEntry
import Doom.Proofs.OriginalGroupHeap
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1AimSideAllocate
open Verification X86 X86Memory X86Control BlockSummary
open E1M1AimSideEntry (request Initial)
open OriginalGroupHeap (View Separated headerWrites splitWrites)
open OriginalGroupMallocEntry (saved prepared rounded)
open X86StartupRoutine (Prefix)
/-! Actual first-free-candidate allocation, starting at the real side entry.
The initial heap view and static separation are boundary assumptions, not a
claim that earlier DOS startup produced this heap. Both split/no-split paths
are inherited. No reached allocator image or successful helper is supplied. -/
def opened (s : X86Memory.State) := prepared (saved (request s).core)
def candidate (s : X86Memory.State) := OriginalGroupMallocEntry.firstFree (opened s).core
def selected (s : X86Memory.State) := OriginalGroupSelected.allocated (candidate s).core
def allocated (s : X86Memory.State) := OriginalGroupAllocation.returned (selected s).core
def lift (p : X86Routine.Program) := X86StartupRoutine.liftProgram (X86ByteRoutine.liftProgram p)
def program : X86StartupRoutine.Program := fun pc =>
  if (0x2e3e0≤pc ∧ pc<0x2e445) ∨ (0x38bb0≤pc ∧ pc<0x38be4)
  then E1M1AimSideEntry.program pc else lift OriginalGroupMalloc.program pc

theorem entry_agrees (pc : Nat) (h : E1M1AimSideEntry.program pc≠none) :
    program pc=E1M1AimSideEntry.program pc := by
  by_cases yes : (0x2e3e0≤pc ∧ pc<0x2e445) ∨ (0x38bb0≤pc ∧ pc<0x38be4)
  · simp [program,yes]
  · have a : ¬(0x2e3e0≤pc ∧ pc<0x2e445) := by omega
    have b : ¬(0x38bb0≤pc ∧ pc<0x38be4) := by omega
    simp [E1M1AimSideEntry.program,E1M1AimSideEntry.bytesProgram,a,b] at h

theorem malloc_agrees (pc : Nat) (h : lift OriginalGroupMalloc.program pc≠none) :
    program pc=lift OriginalGroupMalloc.program pc := by
  by_cases yes : (0x2e3e0≤pc ∧ pc<0x2e445) ∨ (0x38bb0≤pc ∧ pc<0x38be4)
  · have a : ¬((0x2e639≤pc ∧ pc<0x2e63e) ∨ (0x39690≤pc ∧ pc<0x396f8)) := by omega
    have b : ¬(0x396f8≤pc ∧ pc<0x39731) := by omega
    have c : ¬(0x39731≤pc ∧ pc<0x39776) := by omega
    have d : ¬(0x2e63e≤pc ∧ pc<0x2e661) := by omega
    have e : ¬(0x241c0≤pc ∧ pc<0x241dc) := by omega
    simp [lift,X86StartupRoutine.liftProgram,X86ByteRoutine.liftProgram,
      OriginalGroupMalloc.program,OriginalGroupSelected.program,OriginalGroupHandoff.program,
      OriginalGroupEntry.program,OriginalGroupEntry.bytesProgram,a,b,c,d,e] at h
  · simp [program,yes]

private theorem embed {p exits n s t} (run : X86Routine.run p exits n s=some t)
    (agree : ∀ pc, p pc≠none → OriginalGroupMalloc.program pc=p pc) :
    ∃ k≤n, Prefix program [] k s t := by
  obtain ⟨k,hk,path,_⟩ := X86Routine.run_path run
  have path := path.transfer OriginalGroupMalloc.program [] agree (by simp)
  exact ⟨k,hk,(X86StartupRoutine.lift_routine_prefix path).transfer program [] malloc_agrees (by simp)⟩

/-- The real 16-instruction allocation tail, with arbitrary actual return slot.
The preceding split result is not reset and the POP/RET reads are not supplied. -/
theorem tail_execution (s : X86Memory.State) (f : Option Flags)
    (user : s.regs 7=0) (tag : s.regs 5=50) :
    X86Routine.Prefix OriginalGroupAllocation.program [] 16 ⟨s,f,0x39731⟩
      (OriginalGroupAllocation.returned s) := by
  have path : X86Routine.Prefix OriginalGroupAllocation.listed [] 16 ⟨s,f,0x39731⟩
      (OriginalGroupAllocation.returned s) := by
    refine .step (by simp) rfl rfl ?_
    refine .step (middle:=⟨s,some (logical32 0),0x3973f⟩) (by simp) rfl ?_ ?_
    · simp [X86Routine.execute,X86Control.execute,user,logical32]
    refine .step (by simp) rfl rfl ?_
    refine .step (middle:=⟨s,some (compare32 50 100),0x39751⟩) (by simp) rfl ?_ ?_
    · simp [X86Routine.execute,tag]; decide
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (middle:=OriginalGroupAllocation.returned s) (by simp) rfl ?_ (.nil _)
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      X86Block.Address.eval,blockPreservesFlags,OriginalGroupAllocation.returned,
      OriginalGroupAllocation.restored,OriginalGroupAllocation.pop,OriginalGroupAllocation.committed,
      OriginalGroupAllocation.advanced,OriginalGroupAllocation.tagged,OriginalGroupAllocation.owned,
      OriginalGroupAllocation.zone,OriginalGroupAllocation.next,put,write,tag,BitVec.add_assoc]
  exact path.transfer _ [] OriginalGroupAllocation.decoded (by simp)

def PrefixSafe (s : X86Memory.State) (a : Word) : Prop :=
  E1M1AimSideEntry.Safe s a ∧ Apart a 0x2c11c ∧
    ∀ b∈[s.regs 4-36,s.regs 4-40,s.regs 4-44,s.regs 4-48,s.regs 4-52], Apart a b
structure HeapInitial (s : X86Memory.State) (v : View) : Prop where
  image : v.Holds s.memory
  reads : ∀ w∈v.words, PrefixSafe s w.1
  more : v.block≠v.before
  fits : (rounded 11664).toInt≤v.size.toInt
  successor : Separated (v.block+16) (headerWrites v 11664)
  zoneSplit : Separated 0x74fe0 (splitWrites v 11664)
  zoneOwner : Apart 0x74fe0 (v.block+4)
  returnSplit : Separated (s.regs 4-36) (splitWrites v 11664)
  returnTail : Separated (s.regs 4-36) [v.block+4,v.block+8,v.zone+28,v.block+12]

theorem prefix_frame (s : X86Memory.State) (a : Word) (h : PrefixSafe s a) :
    load32 (saved (request s).core).memory a=load32 s.memory a := by
  have stack := h.2.2
  simp only [List.forall_mem_cons,List.not_mem_nil,false_implies,implies_true,and_true] at stack
  have reqSp : (request s).core.regs 4=s.regs 4-36 := by
    simp [request,E1M1AimSideEntry.measured,E1M1AimSideEntry.called,
      X86Routine.pushWord,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc]
  have frame := OriginalGroupMallocEntry.saved_frame (request s).core a (by
    simp only [OriginalGroupMallocEntry.SafeWord,reqSp,List.forall_mem_cons,List.not_mem_nil,
      false_implies,implies_true,and_true]
    simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using stack.2)
  apply frame.trans
  have mem : (request s).core.memory=store32
      (store32 (E1M1AimSideEntry.savedMemory s) 0x2c11c 648) (s.regs 4-36) 0x2e415 := by
    simp [request,E1M1AimSideEntry.measured,E1M1AimSideEntry.called,
      E1M1AimSideEntry.savedMemory,E1M1AimSideEntry.saves,HeapWrites.apply,
      X86Routine.pushWord,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc]
  rw [mem]
  exact (load_store_apart _ _ _ _ stack.1).trans
    ((load_store_apart _ _ _ _ h.2.1).trans (E1M1AimSideEntry.saved_frame s a h.1))

theorem fields (s : X86Memory.State) (v : View) (h : HeapInitial s v) :
    (opened s).core.regs 2=v.block ∧ (opened s).core.regs 6=v.before ∧
    (candidate s).core.regs 3=v.block ∧ v.Holds (candidate s).core.memory := by
  have hv : v.Holds (saved (request s).core).memory :=
    v.transport _ _ h.image (fun w hw => prefix_frame s _ (h.reads w hw))
  have hs := v.fields _ hv
  have hr : OriginalGroupMallocEntry.rover (saved (request s).core)=v.rover := by
    simp only [OriginalGroupMallocEntry.rover,hs.1,hs.2.1]
  have hp : OriginalGroupMallocEntry.previous (saved (request s).core)=v.previous := by
    simp only [OriginalGroupMallocEntry.previous,hr,hs.2.2.1]
  have ho : OriginalGroupMallocEntry.owner (saved (request s).core)=v.previousOwner := by
    simp only [OriginalGroupMallocEntry.owner,hp,hs.2.2.2.1]
  have hb : OriginalGroupMallocEntry.base (saved (request s).core)=v.block := by
    simp only [OriginalGroupMallocEntry.base,ho,hp,hr,View.block]
  refine ⟨?_,?_,?_,hv⟩
  · simp [opened,prepared,put,write,hb]
  · simpa [opened,prepared,put,write,hb] using hs.2.2.2.2.1
  · simp [candidate,OriginalGroupMallocEntry.firstFree,opened,prepared,put,write,hb]

theorem arguments (s : X86Memory.State) :
    (candidate s).core.regs 1=rounded 11664 ∧ (candidate s).core.regs 5=50 ∧
    (candidate s).core.regs 7=0 ∧ (candidate s).core.regs 4=s.regs 4-52 := by
  simp [candidate,opened,OriginalGroupMallocEntry.firstFree,prepared,saved,request,
    E1M1AimSideEntry.measured,E1M1AimSideEntry.called,X86Routine.pushWord,put,write,
    BitVec.sub_eq_add_neg,BitVec.add_assoc]

theorem return_slot (s : X86Memory.State) :
    load32 (candidate s).core.memory ((candidate s).core.regs 4+16)=0x2e415 := by
  have slot : (candidate s).core.regs 4+16=(request s).core.regs 4 := by
    simp [arguments,request,E1M1AimSideEntry.measured,E1M1AimSideEntry.called,
      X86Routine.pushWord,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc]
  change load32 (saved (request s).core).memory ((candidate s).core.regs 4+16)=_
  rw [slot,OriginalGroupMalloc.saved_top]
  exact load_store _ _ _

theorem ready (s : X86Memory.State) (v : View) (h : HeapInitial s v) :
    load32 (candidate s).core.memory ((candidate s).core.regs 3+4)=0 ∧
    ((candidate s).core.regs 1).toInt≤(OriginalGroupSplit.candidateSize (candidate s).core).toInt ∧
    OriginalGroupSelected.ReturnSafe (candidate s).core := by
  have cf := fields s v h
  have hf := v.fields _ cf.2.2.2
  have args := arguments s
  generalize ht : (candidate s).core=t at cf hf args ⊢
  let p := OriginalGroupSelected.picked t
  have pb : p.regs 3=v.block := by simpa [p,OriginalGroupSelected.picked,put,write] using cf.2.2.1
  have pr : p.regs 1=rounded 11664 := by simpa [p,OriginalGroupSelected.picked,put,write] using args.1
  have pn : load32 p.memory (v.block+16)=v.next := hf.2.2.2.2.2.2.2
  have ns := OriginalGroupHeap.successor v p pb pr pn h.successor
  have ss := OriginalGroupHeap.split_safe v p (s.regs 4-36) pb pr ns h.returnSplit
  have zs := OriginalGroupHeap.split_safe v p 0x74fe0 pb pr ns h.zoneSplit
  have ab : (OriginalGroupSelected.allocated t).core.regs 3=v.block :=
    (OriginalGroupSelected.allocated_registers t 3 (by decide) (by decide)).trans cf.2.2.1
  have az : OriginalGroupAllocation.zone (OriginalGroupSelected.allocated t).core=v.zone := by
    unfold OriginalGroupAllocation.zone OriginalGroupAllocation.owned
    rw [ab,load_store_apart _ _ _ _ h.zoneOwner]
    exact (OriginalGroupSelected.allocated_frame t 0x74fe0 zs).trans hf.1
  have slot : t.regs 4+16=s.regs 4-36 := by
    rw [args.2.2.2]; simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  refine ⟨?_,?_,?_⟩
  · rw [cf.2.2.1]; exact hf.2.2.2.2.2.1
  · simpa only [OriginalGroupSplit.candidateSize,cf.2.2.1,args.1,hf.2.2.2.2.2.2.1] using h.fits
  · change OriginalGroupSelected.ReturnSafe t
    unfold OriginalGroupSelected.ReturnSafe
    rw [slot]
    refine ⟨ss,?_⟩
    simpa [OriginalGroupAllocation.SafeWord,ab,az,Separated] using h.returnTail

theorem selected_execution (s : X86Memory.State) (f : Option Flags)
    (free : load32 s.memory (s.regs 3+4)=0)
    (fits : (s.regs 1).toInt≤(OriginalGroupSplit.candidateSize s).toInt)
    (user : s.regs 7=0) (tag : s.regs 5=50) :
    ∃ n≤35, Prefix program [] n ⟨s,f,0x396f8⟩
      (OriginalGroupAllocation.returned (OriginalGroupSelected.allocated s).core) := by
  obtain ⟨d,hd,pd⟩ := embed (OriginalGroupSelected.selected_execution s f free fits)
    (fun pc h => (OriginalGroupMalloc.selected_agrees pc (by
      rw [OriginalGroupSelected.split_agrees pc h]; exact h)).trans (OriginalGroupSelected.split_agrees pc h))
  have sr := OriginalGroupSelected.allocated_registers s
  have tail := tail_execution (OriginalGroupSelected.allocated s).core (OriginalGroupSelected.allocated s).flags
    ((sr 7 (by decide) (by decide)).trans user)
    ((sr 5 (by decide) (by decide)).trans tag)
  have tail := tail.transfer OriginalGroupMalloc.program [] (fun pc h =>
    (OriginalGroupMalloc.selected_agrees pc (by
      rw [OriginalGroupSelected.handoff_agrees pc (by rw [OriginalGroupHandoff.allocation_agrees pc h]; exact h),OriginalGroupHandoff.allocation_agrees pc h]; exact h)).trans
    ((OriginalGroupSelected.handoff_agrees pc (by rw [OriginalGroupHandoff.allocation_agrees pc h]; exact h)).trans (OriginalGroupHandoff.allocation_agrees pc h))) (by simp)
  have tail := (X86StartupRoutine.lift_routine_prefix tail).transfer program [] malloc_agrees (by simp)
  have seam : (⟨(OriginalGroupSelected.allocated s).core,(OriginalGroupSelected.allocated s).flags,0x39731⟩ : X86Control.State)=OriginalGroupSelected.allocated s := by
    rw [←OriginalGroupSplit.result_pc (OriginalGroupSelected.picked s)]; rfl
  rw [seam] at tail
  exact ⟨d+16,by omega,pd.trans tail⟩

theorem selected_return (s : X86Memory.State) (safe : OriginalGroupSelected.ReturnSafe s)
    (ret : load32 s.memory (s.regs 4+16)=0x2e415) :
    (OriginalGroupAllocation.returned (OriginalGroupSelected.allocated s).core).pc=0x2e415 ∧
    (OriginalGroupAllocation.returned (OriginalGroupSelected.allocated s).core).core.regs 0=s.regs 3+24 ∧
    (OriginalGroupAllocation.returned (OriginalGroupSelected.allocated s).core).core.regs 4=s.regs 4+20 := by
  have sr := OriginalGroupSelected.allocated_registers s
  have sp := sr 4 (by decide) (by decide)
  have kept := (OriginalGroupAllocation.returned_frame (OriginalGroupSelected.allocated s).core _ safe.2).trans
      ((OriginalGroupSelected.allocated_frame s _ safe.1).trans ret)
  have regs := OriginalGroupAllocation.returned_registers (OriginalGroupSelected.allocated s).core
  have block := sr 3 (by decide) (by decide)
  generalize ht : (OriginalGroupSelected.allocated s).core=t at sp kept regs block ⊢
  refine ⟨?_,?_,?_⟩
  · have addr : (OriginalGroupAllocation.restored t).regs 4=s.regs 4+16 := by
      simp [OriginalGroupAllocation.restored,OriginalGroupAllocation.pop,OriginalGroupAllocation.committed,put,write,BitVec.add_assoc,sp]
    change (load32 (OriginalGroupAllocation.returned t).core.memory
      ((OriginalGroupAllocation.restored t).regs 4)).toNat=0x2e415
    rw [addr]; exact congrArg BitVec.toNat kept
  · rw [regs.1,block]
  · rw [regs.2,sp]

theorem search_execution (s : X86Memory.State) (f : Option Flags)
    (more : (prepared (saved s)).core.regs 2≠(prepared (saved s)).core.regs 6)
    (free : load32 (prepared (saved s)).core.memory ((prepared (saved s)).core.regs 2+4)=0) :
    ∃ n≤24, Prefix program [] n ⟨s,f,0x39690⟩
      (OriginalGroupMallocEntry.firstFree (prepared (saved s)).core) := by
  obtain ⟨a,ha,pa⟩ := embed (OriginalGroupMallocEntry.save_execution s f) OriginalGroupMalloc.entry_agrees
  obtain ⟨b,hb,pb⟩ := embed (OriginalGroupMallocEntry.prepare_execution (saved s) f) OriginalGroupMalloc.entry_agrees
  have pos : (prepared (saved s)).pc=0x396bd := rfl
  generalize ht : prepared (saved s)=t at more free pb pos ⊢
  obtain ⟨c,hc,pc⟩ := embed (OriginalGroupMallocEntry.free_execution t.core t.flags more free) OriginalGroupMalloc.entry_agrees
  have seam : (⟨t.core,t.flags,0x396bd⟩ : X86Control.State)=t := by rw [←pos]
  rw [seam] at pc
  exact ⟨a+b+c,by omega,(pa.trans pb).trans pc⟩

theorem execution (s : X86Memory.State) (f : Option Flags) (table : Word)
    (initial : Initial s table) (v : View) (heap : HeapInitial s v) :
    (∃ n≤90, Prefix program [] n ⟨s,f,0x2e3e0⟩ (allocated s)) ∧
      (allocated s).pc=0x2e415 ∧ (allocated s).core.regs 0=v.block+24 ∧
      (allocated s).core.regs 4=s.regs 4-32 := by
  have entry := (E1M1AimSideEntry.execution s f table initial).transfer program [] entry_agrees (by simp)
  have cf := fields s v heap
  have hf := v.fields _ cf.2.2.2
  have more : (opened s).core.regs 2≠(opened s).core.regs 6 := by rw [cf.1,cf.2.1]; exact heap.more
  have free : load32 (opened s).core.memory ((opened s).core.regs 2+4)=0 := by
    rw [cf.1]
    simpa only [candidate,OriginalGroupMallocEntry.firstFree,put] using hf.2.2.2.2.2.1
  change (prepared (saved (request s).core)).core.regs 2≠(prepared (saved (request s).core)).core.regs 6 at more
  change load32 (prepared (saved (request s).core)).core.memory ((prepared (saved (request s).core)).core.regs 2+4)=0 at free
  generalize hr : (request s).core=r at more free
  obtain ⟨c,hc,pc⟩ := search_execution r none more free
  rw [←hr] at pc
  change Prefix program [] c (request s) (candidate s) at pc
  have rd := ready s v heap
  have args := arguments s
  have ret := return_slot s
  generalize ht : (candidate s).core=t at rd args ret
  have obs := selected_return t rd.2.2 ret
  obtain ⟨d,hd,pd⟩ := selected_execution t (candidate s).flags rd.1 rd.2.1 args.2.2.1 args.2.1
  rw [←ht] at obs pd args
  change Prefix program [] d (candidate s) (allocated s) at pd
  refine ⟨⟨30+c+d,by omega,?_⟩,obs.1,?_,?_⟩
  · exact (entry.trans pc).trans pd
  · change (OriginalGroupAllocation.returned (OriginalGroupSelected.allocated (candidate s).core).core).core.regs 0=_
    rw [obs.2.1,cf.2.2.1]
  · change (OriginalGroupAllocation.returned (OriginalGroupSelected.allocated (candidate s).core).core).core.regs 4=_
    rw [obs.2.2,args.2.2.2]
    simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
end Doom.Proofs.E1M1AimSideAllocate
