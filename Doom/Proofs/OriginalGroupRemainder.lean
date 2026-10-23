import Doom.Proofs.OriginalGroupOwned
import Doom.Proofs.HeapWrites
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalGroupRemainder
open Verification X86 X86Memory X86Control BlockSummary

/-- Values before splitting; request already includes rounding and header. -/
structure Plan where
  zone : Word
  block : Word
  next : Word
  size : Word
  request : Word
  owner : Word
  tag : Word

def Plan.remainder (p : Plan) := p.block+p.request
def Plan.extra (p : Plan) := p.size-p.request
def Plan.header (p : Plan) : List (Word × Word) :=
  [(p.remainder+4,0),(p.remainder+8,0),(p.remainder,p.extra),(p.remainder+20,p.block)]
def Plan.splitWrites (p : Plan) : List (Word × Word) :=
  p.header++[(p.remainder+16,p.next),(p.next+20,p.remainder),(p.block+16,p.remainder),(p.block,p.request)]
def Plan.published (p : Plan) : List (Word × Word) :=
  p.splitWrites++[(p.block+4,p.owner),(p.owner,p.block+24)]
def Plan.writes (p : Plan) : List (Word × Word) :=
  p.published++[(p.block+8,p.tag),(p.zone+28,p.remainder),(p.block+12,0x1d4a11)]
def Plan.input (p : Plan) (s : X86Memory.State) :=
  put (put (put (put (put s 0 p.size) 1 p.request) 3 p.block) 5 p.tag) 7 p.owner
def Plan.split (p : Plan) (s : X86Memory.State) := OriginalGroupSplit.result (p.input s)
def Plan.result (p : Plan) (s : X86Memory.State) := OriginalGroupOwned.result (p.split s).core
def Plan.view (p : Plan) : OriginalGroupHeap.View :=
  ⟨p.zone,p.remainder,p.block,p.owner,p.block,p.extra,p.next⟩

structure Conditions (p : Plan) (m : Memory) : Prop where
  owner : p.owner≠0
  splits : 64<p.extra.toInt
  zone : load32 m 0x74fe0=p.zone
  next : load32 m (p.block+16)=p.next
  header : ∀ w∈p.header, Apart (p.block+16) w.1
  disjoint : HeapWrites.Disjoint p.writes
  global : ∀ w∈p.writes, Apart 0x74fe0 w.1

theorem split_memory (p : Plan) (s : X86Memory.State) (c : Conditions p s.memory) :
    (p.split s).core.memory=HeapWrites.apply p.splitWrites s.memory := by
  have ns : OriginalGroupSplit.successor (p.input s)=p.next := by
    change load32 (HeapWrites.apply p.header s.memory) (p.block+16)=p.next
    exact (HeapWrites.frame p.header s.memory _ c.header).trans c.next
  have no : ¬(OriginalGroupSplit.extra (p.input s)).toInt≤64 := by
    change ¬p.extra.toInt≤64
    have h := c.splits
    omega
  simp only [Plan.split,OriginalGroupSplit.result,if_neg no]
  simp only [OriginalGroupSplit.linked,ns]
  simp [OriginalGroupSplit.freeHeader,OriginalGroupSplit.remainder,
    OriginalGroupSplit.extra,ns,Plan.input,Plan.splitWrites,Plan.header,Plan.remainder,Plan.extra,
    HeapWrites.apply,put,write,List.foldl_append]

theorem split_register (p : Plan) (s : X86Memory.State) (r : Reg) (h0 : r≠0) (h2 : r≠2) :
    (p.split s).core.regs r=(p.input s).regs r := OriginalGroupSplit.registers _ r h0 h2

theorem published_memory (p : Plan) (s : X86Memory.State) (c : Conditions p s.memory) :
    OriginalGroupOwned.owned (p.split s).core=HeapWrites.apply p.published s.memory := by
  unfold OriginalGroupOwned.owned
  rw [split_memory p s c,split_register p s 3 (by decide) (by decide),
    split_register p s 7 (by decide) (by decide)]
  simp [Plan.published,Plan.input,HeapWrites.append,HeapWrites.apply,put,write,List.foldl_append]

theorem published_reads (p : Plan) (s : X86Memory.State) (c : Conditions p s.memory) :
    OriginalGroupOwned.zone (p.split s).core=p.zone ∧
    OriginalGroupOwned.next (p.split s).core=p.remainder := by
  have disjoint : HeapWrites.Disjoint p.published := (List.pairwise_append.mp c.disjoint).1
  have safe : ∀ w∈p.published, Apart 0x74fe0 w.1 := fun w hw => c.global w (by simp [Plan.writes,hw])
  constructor
  · unfold OriginalGroupOwned.zone
    rw [published_memory p s c]
    exact (HeapWrites.frame _ _ _ safe).trans c.zone
  · unfold OriginalGroupOwned.next
    rw [published_memory p s c,split_register p s 3 (by decide) (by decide)]
    change load32 (HeapWrites.apply p.published s.memory) (p.block+16)=p.remainder
    exact HeapWrites.assigned p.published s.memory (p.block+16,p.remainder) disjoint
      (by simp [Plan.published,Plan.splitWrites])

/-- Exact final memory is a list of thirteen ordered metadata writes. -/
theorem result_memory (p : Plan) (s : X86Memory.State) (c : Conditions p s.memory) :
    (p.result s).core.memory=HeapWrites.apply p.writes s.memory := by
  have reads := published_reads p s c
  change (OriginalGroupOwned.committed (p.split s).core).memory=_
  unfold OriginalGroupOwned.committed OriginalGroupOwned.advanced OriginalGroupOwned.tagged
  rw [reads.1,reads.2,published_memory p s c,
    split_register p s 3 (by decide) (by decide),split_register p s 5 (by decide) (by decide)]
  simp [Plan.writes,HeapWrites.apply,Plan.input,put,write,List.foldl_append]

/-- The newly allocated block becomes the occupied predecessor of the free rover. -/
theorem establishes_view (p : Plan) (s : X86Memory.State) (c : Conditions p s.memory) :
    p.view.Holds (p.result s).core.memory := by
  rw [result_memory p s c]
  have global := (HeapWrites.frame p.writes s.memory 0x74fe0 c.global).trans c.zone
  have assigned := HeapWrites.assigned p.writes s.memory
  have block : p.view.block=p.remainder := by
    change (if p.owner=(0#32) then p.block else p.remainder)=p.remainder
    exact if_neg c.owner
  simp only [OriginalGroupHeap.View.Holds,OriginalGroupHeap.View.words,block,
    List.forall_mem_cons,List.not_mem_nil,false_implies,implies_true,and_true]
  refine ⟨global,?_,?_,?_,?_,?_,?_,?_⟩
  · exact assigned (p.zone+28,p.remainder) c.disjoint (by simp [Plan.writes,Plan.published,Plan.splitWrites,Plan.header])
  · exact assigned (p.remainder+20,p.block) c.disjoint (by simp [Plan.writes,Plan.published,Plan.splitWrites,Plan.header])
  · exact assigned (p.block+4,p.owner) c.disjoint (by simp [Plan.writes,Plan.published,Plan.splitWrites,Plan.header])
  · exact assigned (p.remainder+20,p.block) c.disjoint (by simp [Plan.writes,Plan.published,Plan.splitWrites,Plan.header])
  · exact assigned (p.remainder+4,0) c.disjoint (by simp [Plan.writes,Plan.published,Plan.splitWrites,Plan.header])
  · exact assigned (p.remainder,p.extra) c.disjoint (by simp [Plan.writes,Plan.published,Plan.splitWrites,Plan.header])
  · exact assigned (p.remainder+16,p.next) c.disjoint (by simp [Plan.writes,Plan.published,Plan.splitWrites,Plan.header])

theorem owner_published (p : Plan) (s : X86Memory.State) (c : Conditions p s.memory) :
    load32 (p.result s).core.memory p.owner=p.block+24 := by
  rw [result_memory p s c]
  exact HeapWrites.assigned _ _ (p.owner,p.block+24) c.disjoint
    (by simp [Plan.writes,Plan.published])

/-- Same original program; joins the split decision to nonzero-owner commit. -/
abbrev program := OriginalGroupSelected.program

theorem execution (p : Plan) (s : X86Memory.State) (f : Option Flags) (owner : p.owner≠0) :
    X86Routine.run program [0x39771] 26 ⟨p.input s,f,0x39704⟩=some (p.result s) := by
  obtain ⟨n,hn,path,_⟩ := X86Routine.run_path (OriginalGroupSplit.execution (p.input s) f)
  have path := path.transfer program [0x39771] OriginalGroupSelected.split_agrees (by
    intro pc h member
    simp only [List.mem_singleton] at member
    subst pc
    exact h (by decide))
  have user : (p.split s).core.regs 7≠(0#32) := by
    rw [split_register p s 7 (by decide) (by decide)]
    simpa [Plan.input,put,write] using owner
  have tail := OriginalGroupOwned.execution (p.split s).core (p.split s).flags user
  have eta : (⟨(p.split s).core,(p.split s).flags,0x39731⟩ : X86Control.State)=p.split s := by
    rw [←OriginalGroupSplit.result_pc (p.input s)]; rfl
  rw [eta] at tail
  have agrees (pc : Nat) (h : OriginalGroupOwned.program pc≠none) : program pc=OriginalGroupOwned.program pc :=
    (OriginalGroupSelected.handoff_agrees pc (by
      rw [OriginalGroupHandoff.allocation_agrees pc h]; exact h)).trans
      (OriginalGroupHandoff.allocation_agrees pc h)
  rw [←X86Routine.run_sound program OriginalGroupOwned.program agrees _ _ _ (by rw [tail]; simp)] at tail
  exact path.finish tail 26 (by omega)
end Doom.Proofs.OriginalGroupRemainder
