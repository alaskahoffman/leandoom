import Doom.Proofs.E1M1AimCacheDispatch
import Doom.Proofs.OriginalGroupRemainder
/-! The cache-miss heap is derived from the original heap and the actual first
allocation. A first split uses its produced remainder; a first no-split needs
explicit ORIGINAL free-successor metadata. Capacity for raw19440 is additional,
not a consequence of capacity for side11664. No reached heap is supplied. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1AimCacheHeap
open Verification X86 X86Memory X86Control BlockSummary
open OriginalGroupHeap (View Separated)
open OriginalGroupMallocEntry (rounded)
def plan (v : View) : OriginalGroupRemainder.Plan :=
  ⟨v.zone,v.block,v.next,v.size,rounded 11664,2,50⟩
def noSplit (v : View) : Prop := ((plan v).extra).toInt≤64
instance (v : View) : Decidable (noSplit v) := inferInstanceAs (Decidable (_≤_))
def firstSplit (v : View) : List (Word × Word) := if noSplit v then [] else (plan v).splitWrites
def firstNext (v : View) : Word := if noSplit v then v.next else (plan v).remainder
def firstWrites (v : View) : List (Word × Word) :=
  firstSplit v ++ [(v.block+4,2),(v.block+8,50),(v.zone+28,firstNext v),(v.block+12,0x1d4a11)]
def nextView (v : View) (nextSize nextNext : Word) : View :=
  ⟨v.zone,firstNext v,v.block,2,v.block,
    if noSplit v then nextSize else (plan v).extra,
    if noSplit v then nextNext else v.next⟩
def oldNextWords (v : View) (nextSize nextNext : Word) : List (Word × Word) :=
  [(v.next+20,v.block),(v.next+4,0),(v.next,nextSize),(v.next+16,nextNext)]
structure History (s : X86Memory.State) (v : View) (nextSize nextNext : Word) : Prop where
  disjoint : HeapWrites.Disjoint (firstWrites v)
  global : ∀ w∈firstWrites v, Apart 0x74fe0 w.1
  link : Apart (v.block+16) (v.block+4)
  noSplitWords : noSplit v → ∀ w∈oldNextWords v nextSize nextNext,
    load32 s.memory w.1=w.2 ∧ E1M1AimSideAllocate.PrefixSafe s w.1 ∧
      (∀ z∈firstWrites v, Apart w.1 z.1)

/-- Exact split memory, keeping both actual signed threshold outcomes. -/
theorem split_memory (s : X86Memory.State) (v : View)
    (heap : E1M1AimSideAllocate.HeapInitial s v) :
    (E1M1AimSideAllocate.selected s).core.memory=
      HeapWrites.apply (firstSplit v) (E1M1AimSideAllocate.candidate s).core.memory := by
  have cf := E1M1AimSideAllocate.fields s v heap
  have hf := v.fields _ cf.2.2.2
  have args := E1M1AimSideAllocate.arguments s
  change (OriginalGroupSplit.result (OriginalGroupSelected.picked (E1M1AimSideAllocate.candidate s).core)).core.memory=_
  generalize ht : (E1M1AimSideAllocate.candidate s).core=t at cf hf args ⊢
  have pb : (OriginalGroupSelected.picked t).regs 3=v.block := by
    simp [OriginalGroupSelected.picked,put,write,cf.2.2.1]
  have pr : (OriginalGroupSelected.picked t).regs 1=rounded 11664 := by
    simp [OriginalGroupSelected.picked,put,write,args.1]
  have ps : (OriginalGroupSelected.picked t).regs 0=v.size := by
    simp [OriginalGroupSelected.picked,OriginalGroupSplit.candidateSize,put,write,cf.2.2.1,hf.2.2.2.2.2.2.1]
  have ns := OriginalGroupHeap.successor v (OriginalGroupSelected.picked t) pb pr
    hf.2.2.2.2.2.2.2 heap.successor
  change (OriginalGroupSplit.result (OriginalGroupSelected.picked t)).core.memory=_
  simp only [OriginalGroupSplit.result,OriginalGroupSplit.extra,ps,pr]
  by_cases h : noSplit v
  · simp [firstSplit,noSplit,plan,OriginalGroupRemainder.Plan.extra] at h ⊢
    simp [h,HeapWrites.apply,OriginalGroupSelected.picked,put]
  · have hn : ¬(v.size-rounded 11664).toInt≤64 := h
    rw [if_neg hn]
    simp only [firstSplit,if_neg h,OriginalGroupSplit.linked,ns,OriginalGroupSplit.freeHeader,
      OriginalGroupSplit.remainder,OriginalGroupSplit.extra,pb,pr,ps,
      plan,OriginalGroupRemainder.Plan.splitWrites,OriginalGroupRemainder.Plan.header,
      OriginalGroupRemainder.Plan.remainder,OriginalGroupRemainder.Plan.extra,
      HeapWrites.apply,List.append_assoc,List.foldl_append,List.foldl_cons,List.foldl_nil]
    rfl

/-- The twelve-or-four real writes of the unowned side allocation, before fill. -/
theorem first_memory (s : X86Memory.State) (v : View)
    (heap : E1M1AimSideAllocate.HeapInitial s v) (nextSize nextNext : Word)
    (history : History s v nextSize nextNext) :
    (E1M1AimSideAllocate.allocated s).core.memory=
      HeapWrites.apply (firstWrites v) (E1M1AimSideAllocate.candidate s).core.memory := by
  have cf := E1M1AimSideAllocate.fields s v heap
  have hf := v.fields _ cf.2.2.2
  have args := E1M1AimSideAllocate.arguments s
  have sm := split_memory s v heap
  have sr := OriginalGroupSelected.allocated_registers (E1M1AimSideAllocate.candidate s).core
  have block : (E1M1AimSideAllocate.selected s).core.regs 3=v.block := (sr 3 (by decide) (by decide)).trans cf.2.2.1
  have tag : (E1M1AimSideAllocate.selected s).core.regs 5=50 := (sr 5 (by decide) (by decide)).trans args.2.1
  have dis : HeapWrites.Disjoint (firstSplit v) := (List.pairwise_append.mp history.disjoint).1
  have zone : load32 (E1M1AimSideAllocate.selected s).core.memory 0x74fe0=v.zone := by
    rw [sm]
    exact (HeapWrites.frame _ _ _ (fun w hw=>history.global w (by simp [firstWrites,hw]))).trans hf.1
  have next : load32 (E1M1AimSideAllocate.selected s).core.memory (v.block+16)=firstNext v := by
    rw [sm]
    by_cases h : noSplit v
    · simpa [firstSplit,firstNext,h,HeapWrites.apply] using hf.2.2.2.2.2.2.2
    · apply (HeapWrites.assigned (firstSplit v) _ (v.block+16,firstNext v) dis ?_)
      simp [firstSplit,firstNext,h,plan,OriginalGroupRemainder.Plan.splitWrites]
  have zo : OriginalGroupAllocation.zone (E1M1AimSideAllocate.selected s).core=v.zone := by
    unfold OriginalGroupAllocation.zone OriginalGroupAllocation.owned
    rw [block,load_store_apart _ _ _ _ heap.zoneOwner,zone]
  have ne : OriginalGroupAllocation.next (E1M1AimSideAllocate.selected s).core=firstNext v := by
    unfold OriginalGroupAllocation.next OriginalGroupAllocation.owned
    rw [block,load_store_apart _ _ _ _ history.link,next]
  change (OriginalGroupAllocation.committed (E1M1AimSideAllocate.selected s).core).memory=_
  unfold OriginalGroupAllocation.committed OriginalGroupAllocation.advanced OriginalGroupAllocation.tagged
  rw [zo,ne]
  unfold OriginalGroupAllocation.owned
  rw [block,tag,sm]
  simp [firstWrites,HeapWrites.append,HeapWrites.apply]

/-- No original successor facts are needed on the split branch: its free header
is produced. On no-split they are required explicitly and transported. -/
theorem allocated_view (s : X86Memory.State) (v : View)
    (heap : E1M1AimSideAllocate.HeapInitial s v) (nextSize nextNext : Word)
    (history : History s v nextSize nextNext) :
    (nextView v nextSize nextNext).Holds (E1M1AimSideAllocate.allocated s).core.memory := by
  rw [first_memory s v heap nextSize nextNext history]
  have hf := v.fields _ (E1M1AimSideAllocate.fields s v heap).2.2.2
  have global := (HeapWrites.frame (firstWrites v) _ 0x74fe0 history.global).trans hf.1
  have assigned := HeapWrites.assigned (firstWrites v) (E1M1AimSideAllocate.candidate s).core.memory
  have preserved (a : Word) (sep : E1M1AimSideAllocate.PrefixSafe s a) :
      load32 (E1M1AimSideAllocate.candidate s).core.memory a=load32 s.memory a :=
    E1M1AimSideAllocate.prefix_frame s a sep
  have nb : (nextView v nextSize nextNext).block=firstNext v := rfl
  simp only [View.Holds,View.words,nb,List.forall_mem_cons,List.not_mem_nil,
    false_implies,implies_true,and_true]
  refine ⟨global,?_,?_,?_,?_,?_,?_,?_⟩
  · exact assigned (v.zone+28,firstNext v) history.disjoint (by simp [firstWrites])
  · by_cases h : noSplit v
    · have old := history.noSplitWords h (v.next+20,v.block) (by simp [oldNextWords])
      simpa [nextView,firstNext,h] using (HeapWrites.frame _ _ _ old.2.2).trans ((preserved _ old.2.1).trans old.1)
    · simpa [nextView,firstNext,h] using assigned ((plan v).remainder+20,v.block) history.disjoint (by
        simp [firstWrites,firstSplit,h,plan,OriginalGroupRemainder.Plan.splitWrites,OriginalGroupRemainder.Plan.header])
  · exact assigned (v.block+4,2) history.disjoint (by simp [firstWrites])
  · by_cases h : noSplit v
    · have old := history.noSplitWords h (v.next+20,v.block) (by simp [oldNextWords])
      simpa [nextView,firstNext,h] using (HeapWrites.frame _ _ _ old.2.2).trans
        ((preserved _ old.2.1).trans old.1)
    · simpa [nextView,firstNext,h] using assigned ((plan v).remainder+20,v.block) history.disjoint (by
        simp [firstWrites,firstSplit,h,plan,OriginalGroupRemainder.Plan.splitWrites,OriginalGroupRemainder.Plan.header])
  · by_cases h : noSplit v
    · have old := history.noSplitWords h (v.next+4,0) (by simp [oldNextWords])
      simpa [firstNext,h] using (HeapWrites.frame _ _ _ old.2.2).trans
        ((preserved _ old.2.1).trans old.1)
    · simpa [firstNext,h] using assigned ((plan v).remainder+4,0) history.disjoint (by
        simp [firstWrites,firstSplit,h,plan,OriginalGroupRemainder.Plan.splitWrites,OriginalGroupRemainder.Plan.header])
  · by_cases h : noSplit v
    · have old := history.noSplitWords h (v.next,nextSize) (by simp [oldNextWords])
      simpa [nextView,firstNext,h] using (HeapWrites.frame _ _ _ old.2.2).trans
        ((preserved _ old.2.1).trans old.1)
    · simpa [nextView,firstNext,h] using assigned ((plan v).remainder,(plan v).extra) history.disjoint (by
        simp [firstWrites,firstSplit,h,plan,OriginalGroupRemainder.Plan.splitWrites,OriginalGroupRemainder.Plan.header])
  · by_cases h : noSplit v
    · have old := history.noSplitWords h (v.next+16,nextNext) (by simp [oldNextWords])
      simpa [nextView,firstNext,h] using (HeapWrites.frame _ _ _ old.2.2).trans
        ((preserved _ old.2.1).trans old.1)
    · simpa [nextView,firstNext,h] using assigned ((plan v).remainder+16,v.next) history.disjoint (by
        simp [firstWrites,firstSplit,h,plan,OriginalGroupRemainder.Plan.splitWrites])

theorem requested_view (s : X86Memory.State) (f : Option Flags) (table cache : Word)
    (initial : E1M1AimSideEntry.Initial s table) (v : View)
    (heap : E1M1AimSideAllocate.HeapInitial s v) (frame : E1M1AimSidePublish.AllocationFrame s v)
    (h : Nat) (small : h<8) (safe : E1M1AimWordFill.Entry32Safe s v)
    (nextSize nextNext : Word) (history : History s v nextSize nextNext)
    (kept : ∀ w∈(nextView v nextSize nextNext).words,
      E1M1AimSideMemset.EntrySafe s w.1 ∧ E1M1AimWordFill.OutputSafe s v w.1) :
    (nextView v nextSize nextNext).Holds (E1M1AimCacheDispatch.requested s h cache).core.memory := by
  exact (nextView v nextSize nextNext).transport _ _ (allocated_view s v heap nextSize nextNext history)
    (fun w hw=>E1M1AimCacheDispatch.request_allocation_frame s f table cache initial v heap frame h small safe
      w.1 (kept w hw).1 (kept w hw).2)
end Doom.Proofs.E1M1AimCacheHeap
