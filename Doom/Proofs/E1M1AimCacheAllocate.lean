import Doom.Proofs.E1M1AimCacheHeap
/-! Real owned raw-lump allocation from the produced heap. Both split decisions
remain executable. Capacity and separation are original-address assumptions. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1AimCacheAllocate
open Verification X86 X86Memory X86Control BlockSummary
open OriginalGroupHeap (View Separated)
open OriginalGroupMallocEntry (saved prepared rounded)
open E1M1AimCacheHeap (nextView)
def program := E1M1AimCacheDispatch.program
def opened (s : X86Memory.State) := prepared (saved s)
def candidate (s : X86Memory.State) := OriginalGroupMallocEntry.firstFree (opened s).core
def selected (s : X86Memory.State) := OriginalGroupSelected.allocated (candidate s).core
def restored (s : X86Memory.State) := OriginalGroupAllocation.pop
  (OriginalGroupAllocation.pop (OriginalGroupAllocation.pop (OriginalGroupAllocation.pop s 5) 7) 6) 1
def returned (s : X86Memory.State) : X86Control.State :=
  let t := restored (OriginalGroupOwned.committed s)
  ⟨put t 4 (t.regs 4+4),some (logical32 (s.regs 7)),(load32 t.memory (t.regs 4)).toNat⟩
def result (s : X86Memory.State) := returned (selected s).core
def allocated (s : X86Memory.State) (h : Nat) (cache : Word) :=
  X86WordFillRoutine.embed (result (E1M1AimCacheDispatch.requested s h cache).core)

theorem startup_prefix {n s t} (path : X86StartupRoutine.Prefix E1M1AimSideAllocate.program [] n s t) :
    X86WordFillRoutine.Prefix program [] n (X86WordFillRoutine.embed s) (X86WordFillRoutine.embed t) := by
  have p := (X86FillRoutine.lift_prefix path).transfer E1M1AimSideMemset.program [] E1M1AimSideMemset.startup_agrees (by simp)
  have p := (X86WordFillRoutine.lift_prefix p).transfer E1M1AimWordFill.program [] E1M1AimWordFill.previous_agrees (by simp)
  exact p.transfer _ [] E1M1AimCacheDispatch.previous_agrees (by simp)

theorem routine_prefix {p n s t} (path : X86Routine.Prefix p [] n s t)
    (agree : ∀ pc, p pc≠none → OriginalGroupMalloc.program pc=p pc) :
    X86WordFillRoutine.Prefix program [] n (X86WordFillRoutine.embed s) (X86WordFillRoutine.embed t) := by
  have p := X86StartupRoutine.lift_routine_prefix (path.transfer OriginalGroupMalloc.program [] agree (by simp))
  exact startup_prefix (p.transfer _ [] E1M1AimSideAllocate.malloc_agrees (by simp))

theorem allocation_agrees (pc : Nat) (h : OriginalGroupAllocation.program pc≠none) :
    OriginalGroupMalloc.program pc=OriginalGroupAllocation.program pc := by
  have a := OriginalGroupHandoff.allocation_agrees pc h
  have b := OriginalGroupSelected.handoff_agrees pc (by rw [a]; exact h)
  exact (OriginalGroupMalloc.selected_agrees pc (by rw [b,a]; exact h)).trans (b.trans a)

def epilogue : X86Routine.Program
  | 0x39771 => some (.pop 5,1)
  | 0x39772 => some (.pop 7,1)
  | 0x39773 => some (.pop 6,1)
  | 0x39774 => some (.pop 1,1)
  | 0x39775 => some (.ret,1)
  | _ => none
theorem epilogue_decoded (pc : Nat) (h : epilogue pc≠none) :
    OriginalGroupAllocation.program pc=epilogue pc := by
  fun_cases epilogue pc <;> simp_all [epilogue] <;> decide

theorem owned_execution (s : X86Memory.State) (f : Option Flags) (owner : s.regs 7≠0) :
    ∃ n≤17, X86WordFillRoutine.Prefix program [] n
      (X86WordFillRoutine.embed ⟨s,f,0x39731⟩) (X86WordFillRoutine.embed (returned s)) := by
  obtain ⟨k,hk,lead,_⟩ := X86Routine.run_path (OriginalGroupOwned.execution s f owner)
  have lead := routine_prefix (lead.transfer OriginalGroupAllocation.program [] (by intros; rfl) (by simp)) allocation_agrees
  have tail : X86Routine.Prefix epilogue [] 5 (OriginalGroupOwned.result s) (returned s) := by
    refine .step (by simp [OriginalGroupOwned.result]) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (middle:=returned s) (by simp) rfl ?_ (.nil _)
    simp [X86Routine.execute,returned,restored,OriginalGroupAllocation.pop,OriginalGroupOwned.result,
      OriginalGroupOwned.committed,put,write,BitVec.add_assoc]
  have tail := routine_prefix (tail.transfer OriginalGroupAllocation.program [] epilogue_decoded (by simp)) allocation_agrees
  exact ⟨k+5,by omega,lead.trans tail⟩

def rawPlan (v : View) (cache : Word) : OriginalGroupRemainder.Plan :=
  ⟨v.zone,v.block,v.next,v.size,rounded 19440,cache+36,1⟩
def rawSplit (v : View) (cache : Word) : List (Word × Word) :=
  if (v.size-rounded 19440).toInt≤64 then [] else (rawPlan v cache).splitWrites
def rawNext (v : View) : Word := if (v.size-rounded 19440).toInt≤64 then v.next else v.block+rounded 19440
def rawWrites (v : View) (cache : Word) : List (Word × Word) :=
  rawSplit v cache ++ [(v.block+4,cache+36),(cache+36,v.block+24),
    (v.block+8,1),(v.zone+28,rawNext v),(v.block+12,0x1d4a11)]
structure Local (s : X86Memory.State) (v : View) (cache : Word) : Prop where
  image : v.Holds s.memory
  request : s.regs 0=19440
  tag : s.regs 2=1
  owner : s.regs 3=cache+36
  nonzero : cache+36≠0
  more : v.block≠v.before
  fits : (rounded 19440).toInt≤v.size.toInt
  stack : ∀ w∈v.words, OriginalGroupMallocEntry.SafeWord w.1 s
  successor : Separated (v.block+16) (OriginalGroupHeap.headerWrites v 19440)
  disjoint : HeapWrites.Disjoint (rawWrites v cache)
  global : ∀ w∈rawWrites v cache, Apart 0x74fe0 w.1
  link : Apart (v.block+16) (v.block+4) ∧ Apart (v.block+16) (cache+36)
  returnSafe : ∀ w∈rawWrites v cache, Apart (s.regs 4) w.1

/-- Local helper facts are used only after the original-state theorem derives
this view by `requested_view`; this is not the startup boundary contract. -/
theorem fields (s : X86Memory.State) (v : View) (cache : Word) (c : Local s v cache) :
    (opened s).core.regs 2=v.block ∧ (opened s).core.regs 6=v.before ∧
    (candidate s).core.regs 3=v.block ∧ v.Holds (candidate s).core.memory := by
  have hv : v.Holds (saved s).memory := v.transport _ _ c.image
    (fun w hw=>OriginalGroupMallocEntry.saved_frame s _ (c.stack w hw))
  have hs := v.fields _ hv
  have hr : OriginalGroupMallocEntry.rover (saved s)=v.rover := by
    simp only [OriginalGroupMallocEntry.rover,hs.1,hs.2.1]
  have hp : OriginalGroupMallocEntry.previous (saved s)=v.previous := by
    simp only [OriginalGroupMallocEntry.previous,hr,hs.2.2.1]
  have ho : OriginalGroupMallocEntry.owner (saved s)=v.previousOwner := by
    simp only [OriginalGroupMallocEntry.owner,hp,hs.2.2.2.1]
  have hb : OriginalGroupMallocEntry.base (saved s)=v.block := by
    simp only [OriginalGroupMallocEntry.base,ho,hp,hr,View.block]
  refine ⟨?_,?_,?_,hv⟩
  · simp [opened,prepared,put,write,hb]
  · simpa [opened,prepared,put,write,hb] using hs.2.2.2.2.1
  · simp [candidate,OriginalGroupMallocEntry.firstFree,opened,prepared,put,write,hb]

theorem arguments (s : X86Memory.State) :
    (candidate s).core.regs 1=rounded (s.regs 0) ∧ (candidate s).core.regs 5=s.regs 2 ∧
    (candidate s).core.regs 7=s.regs 3 ∧ (candidate s).core.regs 4=s.regs 4-16 := by
  simp [candidate,opened,prepared,saved,OriginalGroupMallocEntry.firstFree,X86Routine.pushWord,
    put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc]

theorem split_memory (s : X86Memory.State) (v : View) (cache : Word) (c : Local s v cache) :
    (selected s).core.memory=HeapWrites.apply (rawSplit v cache) (candidate s).core.memory := by
  have cf := fields s v cache c
  have hf := v.fields _ cf.2.2.2
  have args := arguments s
  rw [c.request] at args
  change (OriginalGroupSplit.result (OriginalGroupSelected.picked (candidate s).core)).core.memory=_
  generalize ht : (candidate s).core=t at cf hf args ⊢
  have pb : (OriginalGroupSelected.picked t).regs 3=v.block := by simp [OriginalGroupSelected.picked,put,write,cf.2.2.1]
  have pr : (OriginalGroupSelected.picked t).regs 1=rounded 19440 := by simp [OriginalGroupSelected.picked,put,write,args.1]
  have ps : (OriginalGroupSelected.picked t).regs 0=v.size := by
    simp [OriginalGroupSelected.picked,OriginalGroupSplit.candidateSize,put,write,cf.2.2.1,hf.2.2.2.2.2.2.1]
  have ns := OriginalGroupHeap.successor v (OriginalGroupSelected.picked t) pb pr hf.2.2.2.2.2.2.2 c.successor
  simp only [OriginalGroupSplit.result,OriginalGroupSplit.extra,ps,pr]
  by_cases h : (v.size-rounded 19440).toInt≤64
  · simp only [rawSplit,if_pos h,HeapWrites.apply,List.foldl_nil]
    rfl
  · rw [if_neg h]
    simp only [rawSplit,if_neg h,OriginalGroupSplit.linked,ns,OriginalGroupSplit.freeHeader,
      OriginalGroupSplit.remainder,OriginalGroupSplit.extra,pb,pr,ps,rawPlan,
      OriginalGroupRemainder.Plan.splitWrites,OriginalGroupRemainder.Plan.header,
      OriginalGroupRemainder.Plan.remainder,OriginalGroupRemainder.Plan.extra,
      HeapWrites.apply,List.foldl_append,List.foldl_cons,List.foldl_nil]
    rfl

theorem result_memory (s : X86Memory.State) (v : View) (cache : Word) (c : Local s v cache) :
    (result s).core.memory=HeapWrites.apply (rawWrites v cache) (candidate s).core.memory := by
  have cf := fields s v cache c
  have hf := v.fields _ cf.2.2.2
  have args := arguments s
  have sm := split_memory s v cache c
  have sr := OriginalGroupSelected.allocated_registers (candidate s).core
  have block : (selected s).core.regs 3=v.block := (sr 3 (by decide) (by decide)).trans cf.2.2.1
  have tag : (selected s).core.regs 5=1 := (sr 5 (by decide) (by decide)).trans (args.2.1.trans c.tag)
  have owner : (selected s).core.regs 7=cache+36 := (sr 7 (by decide) (by decide)).trans (args.2.2.1.trans c.owner)
  have dis : HeapWrites.Disjoint (rawSplit v cache) := (List.pairwise_append.mp c.disjoint).1
  have zone : load32 (selected s).core.memory 0x74fe0=v.zone := by
    rw [sm]
    exact (HeapWrites.frame _ _ _ (fun w hw=>c.global w (by simp [rawWrites,hw]))).trans hf.1
  have next : load32 (selected s).core.memory (v.block+16)=rawNext v := by
    rw [sm]
    by_cases h : (v.size-rounded 19440).toInt≤64
    · simpa only [rawSplit,rawNext,if_pos h,HeapWrites.apply,List.foldl_nil] using hf.2.2.2.2.2.2.2
    · exact HeapWrites.assigned (rawSplit v cache) _ (v.block+16,rawNext v) dis (by
        simp only [rawSplit,rawNext,if_neg h,rawPlan,OriginalGroupRemainder.Plan.splitWrites,OriginalGroupRemainder.Plan.remainder]
        simp)
  have zo : OriginalGroupOwned.zone (selected s).core=v.zone := by
    unfold OriginalGroupOwned.zone OriginalGroupOwned.owned
    rw [block,owner,load_store_apart _ _ _ _ (c.global (cache+36,v.block+24) (by simp [rawWrites])),
      load_store_apart _ _ _ _ (c.global (v.block+4,cache+36) (by simp [rawWrites])),zone]
  have ne : OriginalGroupOwned.next (selected s).core=rawNext v := by
    unfold OriginalGroupOwned.next OriginalGroupOwned.owned
    rw [block,owner,load_store_apart _ _ _ _ c.link.2,load_store_apart _ _ _ _ c.link.1,next]
  change (OriginalGroupOwned.committed (selected s).core).memory=_
  unfold OriginalGroupOwned.committed OriginalGroupOwned.advanced OriginalGroupOwned.tagged
  rw [zo,ne]
  unfold OriginalGroupOwned.owned
  rw [block,owner,tag,sm]
  simp [rawWrites,HeapWrites.append,HeapWrites.apply]

theorem local_execution (s : X86Memory.State) (f : Option Flags) (v : View) (cache : Word)
    (c : Local s v cache) :
    ∃ n≤60, X86WordFillRoutine.Prefix program [] n
      (X86WordFillRoutine.embed ⟨s,f,0x39690⟩) (X86WordFillRoutine.embed (result s)) := by
  have cf := fields s v cache c
  have hf := v.fields _ cf.2.2.2
  have args := arguments s
  have more : (opened s).core.regs 2≠(opened s).core.regs 6 := by rw [cf.1,cf.2.1]; exact c.more
  have free : load32 (opened s).core.memory ((opened s).core.regs 2+4)=0 := by
    rw [cf.1]; exact hf.2.2.2.2.2.1
  obtain ⟨a,ha,pa⟩ := E1M1AimSideAllocate.search_execution s f more free
  have pa := startup_prefix pa
  have ready : load32 (candidate s).core.memory ((candidate s).core.regs 3+4)=0 := by rw [cf.2.2.1]; exact hf.2.2.2.2.2.1
  have fits : ((candidate s).core.regs 1).toInt≤(OriginalGroupSplit.candidateSize (candidate s).core).toInt := by
    simpa only [args.1,c.request,OriginalGroupSplit.candidateSize,cf.2.2.1,hf.2.2.2.2.2.2.1] using c.fits
  obtain ⟨b,hb,pb,_⟩ := X86Routine.run_path (OriginalGroupSelected.selected_execution (candidate s).core (candidate s).flags ready fits)
  have pb := routine_prefix (pb.transfer OriginalGroupSplit.program [] (by intros; rfl) (by simp))
    (fun pc h=>(OriginalGroupMalloc.selected_agrees pc (by rw [OriginalGroupSelected.split_agrees pc h]; exact h)).trans
      (OriginalGroupSelected.split_agrees pc h))
  have user : (selected s).core.regs 7≠0 := by
    rw [show (selected s).core.regs 7=(candidate s).core.regs 7 from OriginalGroupSelected.allocated_registers _ 7 (by decide) (by decide),args.2.2.1,c.owner]
    exact c.nonzero
  obtain ⟨d,hd,pd⟩ := owned_execution (selected s).core (selected s).flags user
  have seam : (⟨(selected s).core,(selected s).flags,0x39731⟩ : X86Control.State)=selected s := by
    rw [←OriginalGroupSplit.result_pc (OriginalGroupSelected.picked (candidate s).core)]; rfl
  rw [seam] at pd
  exact ⟨a+b+d,by omega,(pa.trans pb).trans pd⟩

theorem local_observations (s : X86Memory.State) (v : View) (cache : Word) (c : Local s v cache)
    (ret : load32 s.memory (s.regs 4)=0x38d41) :
    (result s).pc=0x38d41 ∧ (result s).core.regs 0=v.block+24 ∧
    (result s).core.regs 4=s.regs 4+4 ∧ load32 (result s).core.memory (cache+36)=v.block+24 := by
  have cf := fields s v cache c
  have args := arguments s
  have sr := OriginalGroupSelected.allocated_registers (candidate s).core
  have block : (selected s).core.regs 3=v.block := (sr 3 (by decide) (by decide)).trans cf.2.2.1
  have sp : (selected s).core.regs 4=s.regs 4-16 := (sr 4 (by decide) (by decide)).trans args.2.2.2
  have mem := result_memory s v cache c
  have top : load32 (candidate s).core.memory (s.regs 4)=0x38d41 := (OriginalGroupMalloc.saved_top s).trans ret
  have kept : load32 (result s).core.memory (s.regs 4)=0x38d41 := by
    rw [mem]; exact (HeapWrites.frame _ _ _ c.returnSafe).trans top
  have owner := HeapWrites.assigned (rawWrites v cache) (candidate s).core.memory (cache+36,v.block+24)
    c.disjoint (by simp [rawWrites])
  rw [←mem] at owner
  have regs (t : X86Memory.State) :
      (returned t).core.regs 0=t.regs 3+24 ∧ (returned t).core.regs 4=t.regs 4+20 ∧
      (returned t).pc=(load32 (returned t).core.memory (t.regs 4+16)).toNat := by
    simp [returned,restored,OriginalGroupAllocation.pop,OriginalGroupOwned.committed,put,write,BitVec.add_assoc]
  have rr := regs (selected s).core
  change (result s).core.regs 0=_ ∧ (result s).core.regs 4=_ ∧ (result s).pc=_ at rr
  rw [block,sp] at rr
  simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd,BitVec.add_zero] at rr
  exact ⟨rr.2.2.trans (congrArg BitVec.toNat kept),rr.1,rr.2.1,owner⟩

/-- Every address/number here is evaluated in the ORIGINAL state/view. In the
first-split case capacity is the remaining original block size; in the first
no-split case it is the explicitly supplied original free-successor size. -/
structure Conditions (s : X86Memory.State) (v : View) (cache nextSize nextNext : Word) : Prop where
  kept : ∀ w∈(nextView v nextSize nextNext).words,
    E1M1AimSideMemset.EntrySafe s w.1 ∧ E1M1AimWordFill.OutputSafe s v w.1
  stack : ∀ w∈(nextView v nextSize nextNext).words,
    Separated w.1 [s.regs 4-60,s.regs 4-64,s.regs 4-68,s.regs 4-72]
  nonzero : cache+36≠0
  more : (nextView v nextSize nextNext).block≠(nextView v nextSize nextNext).before
  fits : (rounded 19440).toInt≤(nextView v nextSize nextNext).size.toInt
  successor : Separated ((nextView v nextSize nextNext).block+16)
    (OriginalGroupHeap.headerWrites (nextView v nextSize nextNext) 19440)
  disjoint : HeapWrites.Disjoint (rawWrites (nextView v nextSize nextNext) cache)
  global : ∀ w∈rawWrites (nextView v nextSize nextNext) cache, Apart 0x74fe0 w.1
  link : Apart ((nextView v nextSize nextNext).block+16) ((nextView v nextSize nextNext).block+4) ∧
    Apart ((nextView v nextSize nextNext).block+16) (cache+36)
  returnSafe : ∀ w∈rawWrites (nextView v nextSize nextNext) cache, Apart (s.regs 4-56) w.1

theorem request_stack (s : X86Memory.State) (f : Option Flags) (table cache : Word)
    (initial : E1M1AimSideEntry.Initial s table) (v : View)
    (heap : E1M1AimSideAllocate.HeapInitial s v) (frame : E1M1AimSidePublish.AllocationFrame s v)
    (h : Nat) (small : h<8) :
    (E1M1AimCacheDispatch.requested s h cache).core.regs 4=s.regs 4-56 := by
  have sp := (E1M1AimCacheCall.entry_registers s f table initial v heap frame h small).2.2.2.1
  simp [E1M1AimCacheDispatch.requested,E1M1AimCacheDispatch.request,E1M1AimCacheDispatch.measured,
    E1M1AimCacheDispatch.lengthSaved,E1M1AimCacheDispatch.lengthCalled,E1M1AimCacheDispatch.dispatched,
    E1M1AimCacheDispatch.branch,E1M1AimCacheDispatch.opened,E1M1AimCacheDispatch.saved,
    X86Routine.pushWord,put,write,sp,BitVec.sub_eq_add_neg,BitVec.add_assoc]

theorem entry_execution (s : X86Memory.State) (f : Option Flags) (table cache : Word)
    (initial : E1M1AimSideEntry.Initial s table) (v : View)
    (heap : E1M1AimSideAllocate.HeapInitial s v) (frame : E1M1AimSidePublish.AllocationFrame s v)
    (aligned : (v.block+24).extractLsb' 0 8 &&& 3=0) (safe : E1M1AimWordFill.Entry32Safe s v)
    (inputs : E1M1AimCacheDispatch.CacheInitial s v cache) (miss : load32 s.memory (cache+36)=0)
    (pointerSafe : E1M1AimCacheCall.ReadSafe s v 0x74fa4)
    (lengthSafe : E1M1AimCacheCall.ReadSafe s v (180+table+16))
    (nextSize nextNext : Word) (history : E1M1AimCacheHeap.History s v nextSize nextNext)
    (conditions : Conditions s v cache nextSize nextNext) :
    ∃ h<8, (∃ n≤5400, X86WordFillRoutine.Prefix program [] n
      (X86WordFillRoutine.embed ⟨s,f,0x2e3e0⟩) (allocated s h cache)) ∧
      (allocated s h cache).pc=0x38d41 ∧
      (allocated s h cache).core.regs 0=(nextView v nextSize nextNext).block+24 ∧
      (allocated s h cache).core.regs 4=s.regs 4-52 ∧
      load32 (allocated s h cache).core.memory (cache+36)=(nextView v nextSize nextNext).block+24 := by
  obtain ⟨h,small,⟨a,ha,pa⟩,pc,req,tag,owner,ret⟩ := E1M1AimCacheDispatch.miss_entry_execution
    s f table cache initial v heap frame aligned safe inputs miss pointerSafe lengthSafe
  have view := E1M1AimCacheHeap.requested_view s f table cache initial v heap frame h small safe nextSize nextNext history conditions.kept
  have sp := request_stack s f table cache initial v heap frame h small
  have lc : Local (E1M1AimCacheDispatch.requested s h cache).core (nextView v nextSize nextNext) cache := by
    refine ⟨view,req,tag,owner,conditions.nonzero,conditions.more,conditions.fits,?_,conditions.successor,
      conditions.disjoint,conditions.global,conditions.link,?_⟩
    · intro w hw
      simpa [OriginalGroupMallocEntry.SafeWord,sp,Separated,BitVec.sub_eq_add_neg,BitVec.add_assoc] using conditions.stack w hw
    · simpa only [sp] using conditions.returnSafe
  have obs := local_observations _ _ _ lc ret
  obtain ⟨b,hb,pb⟩ := local_execution (E1M1AimCacheDispatch.requested s h cache).core none _ cache lc
  have seam : X86WordFillRoutine.embed ⟨(E1M1AimCacheDispatch.requested s h cache).core,none,0x39690⟩=
      E1M1AimCacheDispatch.requested s h cache := rfl
  rw [seam] at pb
  refine ⟨h,small,⟨a+b,by omega,pa.trans pb⟩,obs.1,obs.2.1,?_,obs.2.2.2⟩
  change (result (E1M1AimCacheDispatch.requested s h cache).core).core.regs 4=_
  rw [obs.2.2.1,sp]
  simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
end Doom.Proofs.E1M1AimCacheAllocate
