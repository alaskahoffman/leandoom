import Doom.Proofs.E1M1AimCacheAllocate
import Doom.Proofs.OriginalGroupCacheCall
/-! The actual read CALL after owned allocation. W_ReadLump itself and its disk
icon / filesystem calls are NOT successful-helper premises or executed here. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1AimCacheRead
open Verification X86 X86Memory X86Control BlockSummary
open OriginalGroupHeap (View Separated)
open E1M1AimCacheHeap (nextView)
open E1M1AimCacheAllocate (Local candidate selected result rawWrites)
def program := E1M1AimCacheAllocate.program

theorem result_frame (s : X86Memory.State) (v : View) (cache : Word) (c : Local s v cache)
    (a : Word) (stack : OriginalGroupMallocEntry.SafeWord a s)
    (metadata : ∀ w∈rawWrites v cache, Apart a w.1) :
    load32 (result s).core.memory a=load32 s.memory a := by
  rw [E1M1AimCacheAllocate.result_memory s v cache c]
  exact (HeapWrites.frame _ _ _ metadata).trans (OriginalGroupMallocEntry.saved_frame s a stack)

theorem saved_inputs (s : X86Memory.State) :
    load32 (OriginalGroupMallocEntry.saved s).memory (s.regs 4-4)=s.regs 1 ∧
    load32 (OriginalGroupMallocEntry.saved s).memory (s.regs 4-8)=s.regs 6 := by
  have sep (a b : Fin 8) (h : a≠b) :
      Apart (s.regs 4-16+BitVec.ofNat 32 (4*a.val)) (s.regs 4-16+BitVec.ofNat 32 (4*b.val)) :=
    PlayerHeight.slots_apart _ a b h
  have a := sep 3 2 (by decide); have b := sep 3 1 (by decide); have c := sep 3 0 (by decide)
  have d := sep 2 1 (by decide); have e := sep 2 0 (by decide)
  change Apart (s.regs 4-16+12) (s.regs 4-16+8) at a
  change Apart (s.regs 4-16+12) (s.regs 4-16+4) at b
  change Apart (s.regs 4-16+12) (s.regs 4-16+0) at c
  simp [BitVec.sub_eq_add_neg,BitVec.add_assoc] at a b c d e
  simp [OriginalGroupMallocEntry.saved,X86Routine.pushWord,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,
    load_store_apart _ _ _ _ a,load_store_apart _ _ _ _ b,load_store_apart _ _ _ _ c,
    load_store_apart _ _ _ _ d,load_store_apart _ _ _ _ e,load_store]

theorem restored_inputs (s : X86Memory.State) (v : View) (cache : Word) (c : Local s v cache)
    (savedSafe : ∀ a∈[s.regs 4-4,s.regs 4-8], ∀ w∈rawWrites v cache, Apart a w.1) :
    (result s).core.regs 1=s.regs 1 ∧ (result s).core.regs 6=s.regs 6 := by
  have mem := E1M1AimCacheAllocate.result_memory s v cache c
  have saved := saved_inputs s
  have k1 : load32 (result s).core.memory (s.regs 4-4)=s.regs 1 := by
    rw [mem]; exact (HeapWrites.frame _ _ _ (savedSafe _ (by simp))).trans saved.1
  have k6 : load32 (result s).core.memory (s.regs 4-8)=s.regs 6 := by
    rw [mem]; exact (HeapWrites.frame _ _ _ (savedSafe _ (by simp))).trans saved.2
  have sp : (selected s).core.regs 4=s.regs 4-16 :=
    (OriginalGroupSelected.allocated_registers _ 4 (by decide) (by decide)).trans
      (E1M1AimCacheAllocate.arguments s).2.2.2
  have regs (t : X86Memory.State) :
      (E1M1AimCacheAllocate.returned t).core.regs 1=load32 (E1M1AimCacheAllocate.returned t).core.memory (t.regs 4+12) ∧
      (E1M1AimCacheAllocate.returned t).core.regs 6=load32 (E1M1AimCacheAllocate.returned t).core.memory (t.regs 4+8) := by
    simp [E1M1AimCacheAllocate.returned,E1M1AimCacheAllocate.restored,OriginalGroupAllocation.pop,
      OriginalGroupOwned.committed,put,write,BitVec.add_assoc]
  have rr := regs (selected s).core
  rw [sp] at rr
  simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd] at rr k1 k6
  exact ⟨rr.1.trans k1,rr.2.trans k6⟩

theorem request_arguments (s : X86Memory.State) (f : Option Flags) (table cache : Word)
    (initial : E1M1AimSideEntry.Initial s table) (v : View)
    (heap : E1M1AimSideAllocate.HeapInitial s v) (frame : E1M1AimSidePublish.AllocationFrame s v)
    (h : Nat) (small : h<8) :
    (E1M1AimCacheDispatch.requested s h cache).core.regs 0=19440 ∧
    (E1M1AimCacheDispatch.requested s h cache).core.regs 2=1 ∧
    (E1M1AimCacheDispatch.requested s h cache).core.regs 3=cache+36 ∧
    (E1M1AimCacheDispatch.requested s h cache).core.regs 1=9 ∧
    (E1M1AimCacheDispatch.requested s h cache).core.regs 6=36 := by
  have tag := (E1M1AimCacheCall.entry_registers s f table initial v heap frame h small).2.1
  simp [E1M1AimCacheDispatch.requested,E1M1AimCacheDispatch.request,E1M1AimCacheDispatch.measured,
    E1M1AimCacheDispatch.lengthSaved,E1M1AimCacheDispatch.lengthCalled,E1M1AimCacheDispatch.dispatched,
    E1M1AimCacheDispatch.branch,E1M1AimCacheDispatch.opened,E1M1AimCacheDispatch.saved,
    X86Routine.pushWord,put,write,tag]

theorem request_local (s : X86Memory.State) (f : Option Flags) (table cache : Word)
    (initial : E1M1AimSideEntry.Initial s table) (v : View)
    (heap : E1M1AimSideAllocate.HeapInitial s v) (frame : E1M1AimSidePublish.AllocationFrame s v)
    (h : Nat) (small : h<8) (safe : E1M1AimWordFill.Entry32Safe s v)
    (nextSize nextNext : Word) (history : E1M1AimCacheHeap.History s v nextSize nextNext)
    (conditions : E1M1AimCacheAllocate.Conditions s v cache nextSize nextNext) :
    Local (E1M1AimCacheDispatch.requested s h cache).core (nextView v nextSize nextNext) cache := by
  have args := request_arguments s f table cache initial v heap frame h small
  have sp := E1M1AimCacheAllocate.request_stack s f table cache initial v heap frame h small
  refine ⟨E1M1AimCacheHeap.requested_view s f table cache initial v heap frame h small safe nextSize nextNext history conditions.kept,
    args.1,args.2.1,args.2.2.1,conditions.nonzero,conditions.more,conditions.fits,?_,conditions.successor,
    conditions.disjoint,conditions.global,conditions.link,?_⟩
  · intro w hw
    simpa [OriginalGroupMallocEntry.SafeWord,sp,Separated,BitVec.sub_eq_add_neg,BitVec.add_assoc] using conditions.stack w hw
  · simpa only [sp] using conditions.returnSafe

structure ReadConditions (s : X86Memory.State) (v : View) (cache nextSize nextNext : Word) : Prop where
  saved : ∀ a∈[s.regs 4-60,s.regs 4-64], ∀ w∈rawWrites (nextView v nextSize nextNext) cache, Apart a w.1
  pointerStack : Separated 0x74f94 [s.regs 4-60,s.regs 4-64,s.regs 4-68,s.regs 4-72]
  pointerHeap : ∀ w∈rawWrites (nextView v nextSize nextNext) cache, Apart 0x74f94 w.1

/-- The actual allocation leaves flags from TEST owner, not restored EDI. -/
def readCalled (s : X86Memory.State) (h : Nat) (cache : Word) :=
  X86WordFillRoutine.embed (OriginalGroupCacheCall.result
    (E1M1AimCacheAllocate.allocated s h cache).core (some (logical32 (cache+36))))
def listed : X86WordFillRoutine.Program
  | 0x38d41 => some (E1M1AimWordFill.op (.control (.block (.load 0 ⟨none,none,0,0x74f94⟩))),5)
  | 0x38d46 => some (E1M1AimWordFill.op (.control (.block (.load 2 ⟨some 6,some 0,0,0⟩))),3)
  | 0x38d49 => some (E1M1AimWordFill.op (.control (.block (.legacy (.mov 0 1)))),2)
  | 0x38d4b => some (E1M1AimWordFill.op (.call (-352)),5)
  | _ => none
theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

theorem call_execution (s : X86Memory.State) (f : Option Flags) :
    X86WordFillRoutine.Prefix program [] 4 (X86WordFillRoutine.embed ⟨s,f,0x38d41⟩)
      (X86WordFillRoutine.embed (OriginalGroupCacheCall.result s f)) := by
  have path : X86WordFillRoutine.Prefix listed [] 4 (X86WordFillRoutine.embed ⟨s,f,0x38d41⟩)
      (X86WordFillRoutine.embed (OriginalGroupCacheCall.result s f)) := by
    refine .step (by simp [X86WordFillRoutine.embed]) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (middle:=X86WordFillRoutine.embed (OriginalGroupCacheCall.result s f)) (by simp) rfl ?_ (.nil _)
    simp [X86WordFillRoutine.execute,X86WordFillRoutine.embed,X86FillRoutine.execute,X86StartupRoutine.execute,
      X86ByteRoutine.execute,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      X86Block.Address.eval,blockPreservesFlags,OriginalGroupCacheCall.result,OriginalGroupCacheCall.prepared,
      OriginalGroupCacheCall.payload,OriginalGroupCacheCall.cell,X86Routine.pushWord,put,write]
    funext r
    by_cases h : r=0 <;> simp [write,h]
  exact path.transfer _ [] decoded (by simp)

theorem entry_execution (s : X86Memory.State) (f : Option Flags) (table cache : Word)
    (initial : E1M1AimSideEntry.Initial s table) (v : View)
    (heap : E1M1AimSideAllocate.HeapInitial s v) (frame : E1M1AimSidePublish.AllocationFrame s v)
    (aligned : (v.block+24).extractLsb' 0 8 &&& 3=0) (safe : E1M1AimWordFill.Entry32Safe s v)
    (inputs : E1M1AimCacheDispatch.CacheInitial s v cache) (miss : load32 s.memory (cache+36)=0)
    (pointerSafe : E1M1AimCacheCall.ReadSafe s v 0x74fa4)
    (lengthSafe : E1M1AimCacheCall.ReadSafe s v (180+table+16))
    (nextSize nextNext : Word) (history : E1M1AimCacheHeap.History s v nextSize nextNext)
    (conditions : E1M1AimCacheAllocate.Conditions s v cache nextSize nextNext)
    (readSafe : ReadConditions s v cache nextSize nextNext) :
    ∃ h<8, (∃ n≤5404, X86WordFillRoutine.Prefix program [] n
      (X86WordFillRoutine.embed ⟨s,f,0x2e3e0⟩) (readCalled s h cache)) ∧
      (readCalled s h cache).pc=0x38bf0 ∧ (readCalled s h cache).core.regs 0=9 ∧
      (readCalled s h cache).core.regs 2=(nextView v nextSize nextNext).block+24 ∧
      (readCalled s h cache).core.regs 4=s.regs 4-56 ∧
      load32 (readCalled s h cache).core.memory (s.regs 4-56)=0x38d50 := by
  obtain ⟨h,small,⟨n,b,path⟩,pc,base,sp,owner⟩ := E1M1AimCacheAllocate.entry_execution
    s f table cache initial v heap frame aligned safe inputs miss pointerSafe lengthSafe nextSize nextNext history conditions
  have lc := request_local s f table cache initial v heap frame h small safe nextSize nextNext history conditions
  have rs := E1M1AimCacheAllocate.request_stack s f table cache initial v heap frame h small
  have args := request_arguments s f table cache initial v heap frame h small
  have restore := restored_inputs _ _ cache lc (by
    simpa [rs,BitVec.sub_eq_add_neg,BitVec.add_assoc] using readSafe.saved)
  have ptr := (E1M1AimCacheDispatch.request_allocation_frame s f table cache initial v heap frame h small safe
    0x74f94 inputs.pointerSafe.nested inputs.pointerSafe.output).trans
      ((E1M1AimSidePublish.allocation_frame s v heap _ inputs.pointerSafe.allocation).trans inputs.pointer)
  have pointer := (result_frame _ _ _ lc 0x74f94 (by
    simpa [OriginalGroupMallocEntry.SafeWord,Separated,rs,BitVec.sub_eq_add_neg,BitVec.add_assoc] using readSafe.pointerStack)
    readSafe.pointerHeap).trans ptr
  change load32 (E1M1AimCacheAllocate.allocated s h cache).core.memory 0x74f94=cache at pointer
  have idx : (E1M1AimCacheAllocate.allocated s h cache).core.regs 1=9 := restore.1.trans args.2.2.2.1
  have off : (E1M1AimCacheAllocate.allocated s h cache).core.regs 6=36 := restore.2.trans args.2.2.2.2
  have sr := OriginalGroupSelected.allocated_registers
    (candidate (E1M1AimCacheDispatch.requested s h cache).core).core 7 (by decide) (by decide)
  have own : (selected (E1M1AimCacheDispatch.requested s h cache).core).core.regs 7=cache+36 :=
    sr.trans ((E1M1AimCacheAllocate.arguments _).2.2.1.trans args.2.2.1)
  have flags : (E1M1AimCacheAllocate.allocated s h cache).flags=.legacy (some (logical32 (cache+36))) := by
    change X86WordFillRoutine.Knowledge.legacy (some (logical32 _))=_
    rw [own]
  have tail := call_execution (E1M1AimCacheAllocate.allocated s h cache).core (some (logical32 (cache+36)))
  have seam : X86WordFillRoutine.embed ⟨(E1M1AimCacheAllocate.allocated s h cache).core,
      some (logical32 (cache+36)),0x38d41⟩=E1M1AimCacheAllocate.allocated s h cache := by
    simp only [X86WordFillRoutine.embed]
    rw [←pc,←flags]
  rw [seam] at tail
  have vals := OriginalGroupCacheCall.arguments (E1M1AimCacheAllocate.allocated s h cache).core (some (logical32 (cache+36)))
  have payload : OriginalGroupCacheCall.payload (E1M1AimCacheAllocate.allocated s h cache).core=
      (nextView v nextSize nextNext).block+24 := by
    unfold OriginalGroupCacheCall.payload OriginalGroupCacheCall.cell
    rw [off,pointer,BitVec.add_comm 36 cache]
    exact owner
  have rsp : (readCalled s h cache).core.regs 4=s.regs 4-56 := by
    change (OriginalGroupCacheCall.result (E1M1AimCacheAllocate.allocated s h cache).core (some (logical32 (cache+36)))).core.regs 4=_
    rw [vals.2.2,sp]; simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  refine ⟨h,small,⟨n+4,by omega,path.trans tail⟩,rfl,vals.1.trans idx,vals.2.1.trans payload,rsp,?_⟩
  rw [←rsp]
  exact OriginalGroupCacheCall.return_address (E1M1AimCacheAllocate.allocated s h cache).core (some (logical32 (cache+36)))
def ByteSafe (a : Word) (writes : List Word) : Prop :=
  ∀ b∈writes, a≠b ∧ a≠b+1 ∧ a≠b+2 ∧ a≠b+3

theorem bytes_frame (ws : List (Word × Word)) (m : Memory) (a : Word)
    (safe : ByteSafe a (ws.map Prod.fst)) : HeapWrites.apply ws m a=m a := by
  induction ws generalizing m with
  | nil => rfl
  | cons w ws ih =>
    have h := safe w.1 (by simp)
    have tail : ByteSafe a (ws.map Prod.fst) := fun b hb=>safe b (by simp [hb])
    change HeapWrites.apply ws (store32 m w.1 w.2) a=m a
    rw [ih _ tail]
    simp only [store32,if_neg h.1,if_neg h.2.1,if_neg h.2.2.1,if_neg h.2.2.2]

def laterAddresses (s : X86Memory.State) (v : View) (cache : Word) : List Word :=
  [s.regs 4-60,s.regs 4-64,s.regs 4-68,s.regs 4-72] ++
    (rawWrites v cache).map Prod.fst ++ [s.regs 4-56]

theorem call_memory (s : X86Memory.State) (f : Option Flags) :
    (OriginalGroupCacheCall.result s f).core.memory=store32 s.memory (s.regs 4-4) 0x38d50 := by rfl

theorem output_preserved (s : X86Memory.State) (f : Option Flags) (table cache : Word)
    (initial : E1M1AimSideEntry.Initial s table) (v : View)
    (heap : E1M1AimSideAllocate.HeapInitial s v) (frame : E1M1AimSidePublish.AllocationFrame s v)
    (h : Nat) (small : h<8) (safe : E1M1AimWordFill.Entry32Safe s v)
    (nextSize nextNext : Word) (history : E1M1AimCacheHeap.History s v nextSize nextNext)
    (conditions : E1M1AimCacheAllocate.Conditions s v cache nextSize nextNext)
    (output : ∀ j<11664, ByteSafe (v.block+24+BitVec.ofNat 32 j)
      (laterAddresses s (nextView v nextSize nextNext) cache)) :
    ∀ j<11664, (readCalled s h cache).core.memory (v.block+24+BitVec.ofNat 32 j)=0 := by
  have lc := request_local s f table cache initial v heap frame h small safe nextSize nextNext history conditions
  have sp := E1M1AimCacheAllocate.request_stack s f table cache initial v heap frame h small
  have ret : load32 (E1M1AimCacheDispatch.requested s h cache).core.memory
      ((E1M1AimCacheDispatch.requested s h cache).core.regs 4)=0x38d41 := load_store _ _ _
  have obs := E1M1AimCacheAllocate.local_observations _ _ _ lc ret
  have rsp : (E1M1AimCacheAllocate.allocated s h cache).core.regs 4-4=s.regs 4-56 := by
    change (result (E1M1AimCacheDispatch.requested s h cache).core).core.regs 4-4=_
    rw [obs.2.2.1,sp]; simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  have mem := E1M1AimCacheAllocate.result_memory _ _ _ lc
  let req := (E1M1AimCacheDispatch.requested s h cache).core
  let saves : List (Word × Word) := [(s.regs 4-60,req.regs 1),(s.regs 4-64,req.regs 6),
    (s.regs 4-68,req.regs 7),(s.regs 4-72,req.regs 5)]
  have sm : (candidate req).core.memory=HeapWrites.apply saves req.memory := by
    simp [candidate,E1M1AimCacheAllocate.opened,OriginalGroupMallocEntry.firstFree,
      OriginalGroupMallocEntry.prepared,OriginalGroupMallocEntry.saved,saves,req,HeapWrites.apply,
      X86Routine.pushWord,put,write,sp,BitVec.sub_eq_add_neg,BitVec.add_assoc]
  have zm := (E1M1AimCacheDispatch.output_preserved s f table cache initial v heap frame h small safe).2.1
  intro j hj
  let a := v.block+24+BitVec.ofNat 32 j
  have keep := output j hj
  have callSafe := keep (s.regs 4-56) (by simp [laterAddresses])
  have callFrame : (readCalled s h cache).core.memory a=
      (E1M1AimCacheAllocate.allocated s h cache).core.memory a := by
    simp only [readCalled,X86WordFillRoutine.embed,call_memory]
    rw [rsp]
    simp only [a,store32,if_neg callSafe.1,if_neg callSafe.2.1,if_neg callSafe.2.2.1,if_neg callSafe.2.2.2]
  have heapFrame : ByteSafe a ((rawWrites (nextView v nextSize nextNext) cache).map Prod.fst) :=
    fun b hb=>keep b (by simp only [laterAddresses,List.mem_append]; exact Or.inl (Or.inr hb))
  have stackFrame : ByteSafe a (saves.map Prod.fst) := by
    intro b hb
    apply keep b
    simp only [laterAddresses,List.mem_append]
    apply Or.inl; apply Or.inl
    simpa only [saves,List.map_cons,List.map_nil,Prod.fst] using hb
  rw [callFrame]
  change (result req).core.memory a=0
  rw [mem,bytes_frame _ _ _ heapFrame,sm,bytes_frame _ _ _ stackFrame]
  exact zm j hj

/-- Preserve the PRODUCED first allocation, including its count and saved
caller words. Original memory is not substituted for that produced image. -/
theorem produced_frame (s : X86Memory.State) (f : Option Flags) (table cache : Word)
    (initial : E1M1AimSideEntry.Initial s table) (v : View)
    (heap : E1M1AimSideAllocate.HeapInitial s v) (frame : E1M1AimSidePublish.AllocationFrame s v)
    (h : Nat) (small : h<8) (safe : E1M1AimWordFill.Entry32Safe s v)
    (nextSize nextNext : Word) (history : E1M1AimCacheHeap.History s v nextSize nextNext)
    (conditions : E1M1AimCacheAllocate.Conditions s v cache nextSize nextNext)
    (a : Word) (nested : E1M1AimSideMemset.EntrySafe s a) (output : E1M1AimWordFill.OutputSafe s v a)
    (later : Separated a (laterAddresses s (nextView v nextSize nextNext) cache)) :
    load32 (readCalled s h cache).core.memory a=load32 (E1M1AimSideAllocate.allocated s).core.memory a := by
  have lc := request_local s f table cache initial v heap frame h small safe nextSize nextNext history conditions
  have sp := E1M1AimCacheAllocate.request_stack s f table cache initial v heap frame h small
  have obs := E1M1AimCacheAllocate.local_observations _ _ _ lc (load_store _ _ _)
  have rs : (E1M1AimCacheAllocate.allocated s h cache).core.regs 4-4=s.regs 4-56 := by
    change (result (E1M1AimCacheDispatch.requested s h cache).core).core.regs 4-4=_
    rw [obs.2.2.1,sp]; simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  have cf := OriginalGroupCacheCall.frame (E1M1AimCacheAllocate.allocated s h cache).core
    (some (logical32 (cache+36))) a (by rw [rs]; exact later _ (by simp [laterAddresses]))
  have rf := result_frame _ _ _ lc a (by
      rw [show OriginalGroupMallocEntry.SafeWord a (E1M1AimCacheDispatch.requested s h cache).core=
          Separated a [s.regs 4-60,s.regs 4-64,s.regs 4-68,s.regs 4-72] by
        simp [OriginalGroupMallocEntry.SafeWord,Separated,sp,BitVec.sub_eq_add_neg,BitVec.add_assoc]]
      exact fun b hb=>later b (by simp only [laterAddresses,List.mem_append]; exact Or.inl (Or.inl hb)))
    (fun w hw=>later w.1 (by simp only [laterAddresses,List.mem_append]; exact Or.inl (Or.inr (List.mem_map.mpr ⟨w,hw,rfl⟩))))
  exact cf.trans (rf.trans (E1M1AimCacheDispatch.request_allocation_frame s f table cache initial v heap frame h small safe
    a nested output))

/-- Every raw metadata write, including owner publication, tag1 and signature,
survives the actual read CALL. This does not assert raw payload contents. -/
theorem published_word (s : X86Memory.State) (f : Option Flags) (table cache : Word)
    (initial : E1M1AimSideEntry.Initial s table) (v : View)
    (heap : E1M1AimSideAllocate.HeapInitial s v) (frame : E1M1AimSidePublish.AllocationFrame s v)
    (h : Nat) (small : h<8) (safe : E1M1AimWordFill.Entry32Safe s v)
    (nextSize nextNext : Word) (history : E1M1AimCacheHeap.History s v nextSize nextNext)
    (conditions : E1M1AimCacheAllocate.Conditions s v cache nextSize nextNext)
    (w : Word × Word) (member : w∈rawWrites (nextView v nextSize nextNext) cache) :
    load32 (readCalled s h cache).core.memory w.1=w.2 := by
  have lc := request_local s f table cache initial v heap frame h small safe nextSize nextNext history conditions
  have sp := E1M1AimCacheAllocate.request_stack s f table cache initial v heap frame h small
  have obs := E1M1AimCacheAllocate.local_observations _ _ _ lc (load_store _ _ _)
  have rs : (E1M1AimCacheAllocate.allocated s h cache).core.regs 4-4=s.regs 4-56 := by
    change (result (E1M1AimCacheDispatch.requested s h cache).core).core.regs 4-4=_
    rw [obs.2.2.1,sp]; simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  have cf := OriginalGroupCacheCall.frame (E1M1AimCacheAllocate.allocated s h cache).core
    (some (logical32 (cache+36))) w.1 (by
      rw [rs]; exact fun i j=>(conditions.returnSafe w member j i).symm)
  apply cf.trans
  change load32 (result (E1M1AimCacheDispatch.requested s h cache).core).core.memory w.1=w.2
  rw [E1M1AimCacheAllocate.result_memory _ _ _ lc]
  exact HeapWrites.assigned _ _ w conditions.disjoint member
end Doom.Proofs.E1M1AimCacheRead
