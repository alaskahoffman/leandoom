import Doom.Proofs.E1M1FiringNextObjects
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1ObjectBoundary
open Verification X86 X86Memory X86Control BlockSummary
open E1M1ThingList (head collect Image Layout)
open E1M1NextObjectTraversal (result)
attribute [local irreducible] load32

/-- Observe grid locals at the caller's stack position, even while a nonempty
object iterator has its callback word on the stack. This does not execute code. -/
def callerView (s : X86Control.State) (sp : Word) := put s.core 4 (sp-(112#32))

section Objects
variable (s : X86Control.State) (sp lines : Word) (objects : Nat → Word)
    (trace : Collision.Divline) (nodes : List E1M1ThingList.Node)
    (r : Collision.PathResult)
    (nonzero : ∀ node∈nodes, node.pointer≠(0#32))
    (empty : head nodes=0 → s.core.regs 0=(1#32) ∧ s.core.regs 4=sp-(112#32) ∧ s.pc=0x2cab1)
    (nonempty : head nodes≠0 → s.pc=0x2c5d2 ∧ s.core.regs 2=head nodes ∧ s.core.regs 4=sp-(120#32) ∧
      load32 s.core.memory (s.core.regs 4)=(0x2c720#32))
    (ready : head nodes≠0 → Image s.core.memory (s.core.regs 4) trace nodes (0x2cab1#32) ∧
      Layout (s.core.regs 4) trace (E1M1ThingFinish.resolve lines objects) nodes)
    (tracked : OriginalLineCollection.Tracks s.core 0x2ba20 (E1M1ThingFinish.resolve lines objects) r.collected 0)
    (capacity : r.collected.size+nodes.length≤128)

include nonzero empty nonempty ready tracked capacity

/-- Complete object traversal preserves all four live grid registers and every
protected word, while restoring the caller stack. Empty lists need no callback. -/
theorem preserved :
    let out := result s nodes
    out.core.regs 4=sp-(112#32) ∧
    (∀ reg∈([1,5,6,7] : List (Fin 8)), out.core.regs reg=s.core.regs reg) ∧
    (∀ a, E1M1ThingVisit.ReadSafe (sp-(120#32)) a → load32 out.core.memory a=load32 s.core.memory a) := by
  cases nodes with
  | nil => exact ⟨(empty rfl).2.1,fun _ _ => rfl,fun _ _ => rfl⟩
  | cons node rest =>
    have present : head (node::rest)≠(0#32) := nonzero node (by simp)
    obtain ⟨pc,cursor,stack,_⟩ := nonempty present
    obtain ⟨image,layout⟩ := ready present
    have pc' : s.pc=if head (node::rest)=(0#32) then 0x2c5e2 else 0x2c5d2 := by
      rw [if_neg present]; exact pc
    have ret := E1M1ThingTraversal.execution s trace (E1M1ThingFinish.resolve lines objects) (node::rest) 0x2cab1
      layout image cursor pc' r tracked capacity
    have coord (axis : Bool) := E1M1ThingPreservation.traversal_coordinate s trace
      (E1M1ThingFinish.resolve lines objects) (node::rest) 0x2cab1 layout image cursor pc' r tracked capacity axis
    have grid (axis : Bool) := E1M1ThingGridRegisters.traversal_register s trace
      (E1M1ThingFinish.resolve lines objects) (node::rest) 0x2cab1 layout image cursor pc' r tracked capacity axis
    refine ⟨ret.2.2.1.trans (by rw [stack]; simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]),?_,?_⟩
    · intro reg member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl|rfl|rfl
      · exact coord false
      · exact grid false
      · exact coord true
      · exact grid true
    · intro a safe
      exact E1M1ThingListFrame.traversal_frame s trace (E1M1ThingFinish.resolve lines objects) (node::rest) 0x2cab1
        layout image cursor pc' r tracked capacity a (by rw [stack]; exact safe)

/-- All eleven numeric grid fields survive the object scan. The stack-relative
locals are compared at the caller position, not the iterator's temporary SP. -/
theorem observe (locals : E1M1GridLocals.Safe sp lines) :
    E1M1PathAdvance.observe (result s nodes).core=E1M1PathAdvance.observe (callerView s sp) := by
  have keep := preserved s sp lines objects trace nodes r nonzero empty nonempty ready tracked capacity
  apply E1M1FiringGridState.transport
  · intro reg member
    have neq : reg≠4 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl|rfl|rfl <;> decide
    simpa [callerView,put,write,neq] using keep.2.1 reg member
  · intro off member
    change load32 (result s nodes).core.memory ((result s nodes).core.regs 4+off)=
      load32 (callerView s sp).memory ((callerView s sp).regs 4+off)
    rw [keep.1]
    exact keep.2.2 (E1M1GridLocals.address sp off) (E1M1GridLocals.thing_safe sp lines off member locals)
end Objects
end Doom.Proofs.E1M1ObjectBoundary
