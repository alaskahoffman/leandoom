import Doom.Proofs.OriginalGroupStartup
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000
namespace Doom.Proofs.OriginalGroupHeap
open Verification X86 X86Memory X86Control BlockSummary
open OriginalGroupMallocEntry (called saved rounded)

/-- A local header view, not a global heap invariant or reachability claim. -/
structure View where
  zone : Word
  rover : Word
  previous : Word
  previousOwner : Word
  before : Word
  size : Word
  next : Word

def View.block (v : View) : Word := if v.previousOwner=0 then v.previous else v.rover

def View.words (v : View) : List (Word × Word) :=
  [(0x74fe0,v.zone),(v.zone+28,v.rover),(v.rover+20,v.previous),
   (v.previous+4,v.previousOwner),(v.block+20,v.before),(v.block+4,0),
   (v.block,v.size),(v.block+16,v.next)]

def View.Holds (v : View) (m : Memory) : Prop :=
  ∀ w∈v.words, load32 m w.1=w.2

theorem View.transport (v : View) (m n : Memory) (h : v.Holds m)
    (frame : ∀ w∈v.words, load32 n w.1=load32 m w.1) : v.Holds n :=
  fun w hw => (frame w hw).trans (h w hw)

theorem View.fields (v : View) (m : Memory) (h : v.Holds m) :
    load32 m 0x74fe0=v.zone ∧ load32 m (v.zone+28)=v.rover ∧
    load32 m (v.rover+20)=v.previous ∧ load32 m (v.previous+4)=v.previousOwner ∧
    load32 m (v.block+20)=v.before ∧ load32 m (v.block+4)=0 ∧
    load32 m v.block=v.size ∧ load32 m (v.block+16)=v.next := by
  simpa only [View.Holds,View.words,List.forall_mem_cons,List.not_mem_nil,
    false_implies,implies_true,and_true] using h

/-- The five writes of CALL plus prologue, expressed before either executes. -/
def StackSafe (a sp : Word) : Prop :=
  ∀ b∈[sp-4,sp-8,sp-12,sp-16,sp-20], Apart a b

theorem prefix_frame (s : X86Memory.State) (a : Word) (safe : StackSafe a (s.regs 4)) :
    load32 (saved (called s)).memory a=load32 s.memory a := by
  simp only [StackSafe,List.forall_mem_cons,List.not_mem_nil,false_implies,implies_true,and_true] at safe
  apply Eq.trans (OriginalGroupMallocEntry.saved_frame (called s) a ?_)
  · exact load_store_apart _ _ _ _ safe.1
  · simpa [OriginalGroupMallocEntry.SafeWord,called,X86Routine.pushWord,write,
      BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe.2

theorem saved_view (v : View) (s : X86Memory.State) (h : v.Holds s.memory)
    (safe : ∀ w∈v.words, StackSafe w.1 (s.regs 4)) : v.Holds (saved (called s)).memory :=
  v.transport _ _ h (fun w hw => prefix_frame s w.1 (safe w hw))

/-- Normalize the candidate using only raw header reads and stack separation. -/
theorem candidate_fields (v : View) (s : X86Memory.State) (h : v.Holds s.memory)
    (safe : ∀ w∈v.words, StackSafe w.1 (s.regs 4)) :
    (OriginalGroupMalloc.opened s).core.regs 2=v.block ∧
    (OriginalGroupMalloc.opened s).core.regs 6=v.before ∧
    (OriginalGroupMalloc.candidate s).core.regs 3=v.block ∧
    v.Holds (OriginalGroupMalloc.candidate s).core.memory := by
  have hv := saved_view v s h safe
  have hs := v.fields _ hv
  have hr : OriginalGroupMallocEntry.rover (saved (called s))=v.rover := by
    simp only [OriginalGroupMallocEntry.rover,hs.1,hs.2.1]
  have hp : OriginalGroupMallocEntry.previous (saved (called s))=v.previous := by
    simp only [OriginalGroupMallocEntry.previous,hr,hs.2.2.1]
  have ho : OriginalGroupMallocEntry.owner (saved (called s))=v.previousOwner := by
    simp only [OriginalGroupMallocEntry.owner,hp,hs.2.2.2.1]
  have hb : OriginalGroupMallocEntry.base (saved (called s))=v.block := by
    simp only [OriginalGroupMallocEntry.base,ho,hp,hr,View.block]
  refine ⟨?_,?_,?_,hv⟩
  · simp [OriginalGroupMalloc.opened,OriginalGroupMallocEntry.prepared,put,write,hb]
  · simpa [OriginalGroupMalloc.opened,OriginalGroupMallocEntry.prepared,put,write,hb] using hs.2.2.2.2.1
  · simp [OriginalGroupMalloc.candidate,OriginalGroupMallocEntry.firstFree,
      OriginalGroupMalloc.opened,OriginalGroupMallocEntry.prepared,put,write,hb]

def headerWrites (v : View) (request : Word) : List Word :=
  [v.block+rounded request+4,v.block+rounded request+8,
   v.block+rounded request,v.block+rounded request+20]
def splitWrites (v : View) (request : Word) : List Word :=
  headerWrites v request ++ [v.block+rounded request+16,v.next+20,v.block+16,v.block]
def Separated (a : Word) (writes : List Word) : Prop := ∀ b∈writes, Apart a b

/-- All conditions use initial addresses and values, not computed machine states.
Separation is conservative: it also covers the unused split footprint. -/
structure Conditions (v : View) (request sp : Word) : Prop where
  more : v.block≠v.before
  fits : (rounded request).toInt≤v.size.toInt
  stack : ∀ w∈v.words, StackSafe w.1 sp
  successor : Separated (v.block+16) (headerWrites v request)
  zoneSplit : Separated 0x74fe0 (splitWrites v request)
  zoneOwner : Apart 0x74fe0 (v.block+4)
  returnSplit : Separated (sp-4) (splitWrites v request)
  returnTail : Separated (sp-4) [v.block+4,v.block+8,v.zone+28,v.block+12]

/-- The successor read after four stores still reads the initial next link. -/
theorem successor (v : View) (s : X86Memory.State)
    (block : s.regs 3=v.block) (request : s.regs 1=rounded n)
    (next : load32 s.memory (v.block+16)=v.next)
    (safe : Separated (v.block+16) (headerWrites v n)) :
    OriginalGroupSplit.successor s=v.next := by
  simp only [Separated,headerWrites,List.forall_mem_cons,List.not_mem_nil,
    false_implies,implies_true,and_true] at safe
  unfold OriginalGroupSplit.successor OriginalGroupSplit.freeHeader OriginalGroupSplit.remainder
  rw [block,request,load_store_apart _ _ _ _ safe.2.2.2,
    load_store_apart _ _ _ _ safe.2.2.1,load_store_apart _ _ _ _ safe.2.1,
    load_store_apart _ _ _ _ safe.1]
  exact next

theorem split_safe (v : View) (s : X86Memory.State) (a : Word)
    (block : s.regs 3=v.block) (request : s.regs 1=rounded n)
    (next : OriginalGroupSplit.successor s=v.next)
    (safe : Separated a (splitWrites v n)) : OriginalGroupSplit.SafeWord a s := by
  simpa [OriginalGroupSplit.SafeWord,OriginalGroupSplit.remainder,block,request,next,
    Separated,splitWrites,headerWrites] using safe

/-- Discharge the old computed-state Ready contract from raw initial heap facts. -/
theorem ready (v : View) (s : X86Memory.State) (h : v.Holds s.memory)
    (c : Conditions v (s.regs 0) (s.regs 4)) : OriginalGroupMalloc.Ready s := by
  have cf := candidate_fields v s h c.stack
  have hf := v.fields _ cf.2.2.2
  have args := OriginalGroupMalloc.candidate_arguments s
  let t := (OriginalGroupMalloc.candidate s).core
  let p := OriginalGroupSelected.picked t
  have pb : p.regs 3=v.block := by simpa [p,OriginalGroupSelected.picked,put,write] using cf.2.2.1
  have pr : p.regs 1=rounded (s.regs 0) := by simpa [p,OriginalGroupSelected.picked,put,write] using args.1
  have pn : load32 p.memory (v.block+16)=v.next := hf.2.2.2.2.2.2.2
  have ns := successor v p pb pr pn c.successor
  have ss := split_safe v p (s.regs 4-4) pb pr ns c.returnSplit
  have zs := split_safe v p 0x74fe0 pb pr ns c.zoneSplit
  have ab : (OriginalGroupSelected.allocated t).core.regs 3=v.block :=
    (OriginalGroupSelected.allocated_registers t 3 (by decide) (by decide)).trans cf.2.2.1
  have az : OriginalGroupAllocation.zone (OriginalGroupSelected.allocated t).core=v.zone := by
    unfold OriginalGroupAllocation.zone OriginalGroupAllocation.owned
    rw [ab,load_store_apart _ _ _ _ c.zoneOwner]
    exact (OriginalGroupSelected.allocated_frame t 0x74fe0 zs).trans hf.1
  have slot : t.regs 4+16=s.regs 4-4 := by
    rw [args.2.2.2]
    simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  refine {more := ?_,free := ?_,fits := ?_,safe := ?_}
  · rw [cf.1,cf.2.1]; exact c.more
  · change load32 (saved (called s)).memory ((OriginalGroupMalloc.opened s).core.regs 2+4)=0
    rw [cf.1]; exact hf.2.2.2.2.2.1
  · simpa only [OriginalGroupSplit.candidateSize,cf.2.2.1,args.1,hf.2.2.2.2.2.2.1] using c.fits
  · change OriginalGroupSelected.ReturnSafe t
    unfold OriginalGroupSelected.ReturnSafe
    rw [slot]
    refine ⟨ss,?_⟩
    simpa [OriginalGroupAllocation.SafeWord,ab,az,Separated] using c.returnTail

/-- Counting changes counters, not the separated allocator header view. -/
theorem count_view (v : View) (es : List OriginalGroupOutput.Line) (s : X86Memory.State)
    (layout : OriginalGroupCountScan.Layout es) (inputs : OriginalGroupOutput.Inputs es s.memory)
    (linked : OriginalGroupOutput.Linked es (load32 s.memory 0x2c120))
    (heap : v.Holds s.memory)
    (safe : ∀ w∈v.words, OriginalGroupCountScan.SafeWord w.1 es) :
    v.Holds (OriginalGroupCountScan.final es s).core.memory :=
  v.transport _ _ heap (fun w hw => OriginalGroupCountScan.final_frame es s _ layout inputs linked (safe w hw))

def request (es : List OriginalGroupOutput.Line) : Word := BitVec.ofNat 32 (OriginalGroupCountScan.references es) <<< 2

theorem count_ready (v : View) (es : List OriginalGroupOutput.Line) (s : X86Memory.State)
    (layout : OriginalGroupCountScan.Layout es) (inputs : OriginalGroupOutput.Inputs es s.memory)
    (linked : OriginalGroupOutput.Linked es (load32 s.memory 0x2c120))
    (heap : v.Holds s.memory) (safe : ∀ w∈v.words, OriginalGroupCountScan.SafeWord w.1 es)
    (conditions : Conditions v (request es) (s.regs 4)) :
    OriginalGroupMalloc.Ready (OriginalGroupCountScan.final es s).core := by
  apply ready v _ (count_view v es s layout inputs linked heap safe)
  rw [(OriginalGroupCountScan.final_arguments es s layout inputs linked).1,
    OriginalGroupCountScan.final_stack]
  exact conditions

theorem execution (v : View) (es : List OriginalGroupOutput.Line) (s : X86Memory.State) (f : Option Flags)
    (small : es.length<2147483648) (layout : OriginalGroupCountScan.Layout es)
    (inputs : OriginalGroupOutput.Inputs es s.memory)
    (linked : OriginalGroupOutput.Linked es (load32 s.memory 0x2c120))
    (count : (load32 s.memory 0x2c134).toNat=es.length)
    (heap : v.Holds s.memory) (safe : ∀ w∈v.words, OriginalGroupCountScan.SafeWord w.1 es)
    (conditions : Conditions v (request es) (s.regs 4)) :
    X86Routine.run OriginalGroupStartup.program [0x2e661,0x2e791] (87+17*es.length)
      ⟨s,f,0x2e5ef⟩=some (OriginalGroupStartup.result es s) :=
  OriginalGroupStartup.execution es s f small layout inputs linked count
    (count_ready v es s layout inputs linked heap safe conditions)
end Doom.Proofs.OriginalGroupHeap
