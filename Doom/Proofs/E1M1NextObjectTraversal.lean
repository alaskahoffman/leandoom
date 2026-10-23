import Doom.Proofs.E1M1FiringNextObjectImage
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1NextObjectTraversal
open Verification X86 X86Memory X86Control BlockSummary
open OriginalLineVisits (Represents stamp)
open E1M1ThingList (head collect Image Layout)
attribute [local irreducible] load32

/-- Empty lookups have already returned; nonempty ones run the existing list
traversal and its epilogue. This wrapper applies at any cell lookup boundary. -/
def result (s : X86Control.State) : List E1M1ThingList.Node → X86Control.State
  | [] => s
  | nodes@(_::_) => E1M1ThingTraversal.result s nodes.length

/-- Reuse the complete finite-list proof on a mixed input collection, retaining
visited history for the next grid iteration. Capacity is supplied before any
object callback executes. -/
theorem execution (s : X86Control.State) (sp lines epoch : Word) (objects : Nat → Word)
    (trace : Collision.Divline) (nodes : List E1M1ThingList.Node)
    (r : Collision.PathResult) (seen : Array Bool)
    (nonzero : ∀ node∈nodes, node.pointer≠(0#32))
    (empty : head nodes=0 → s.core.regs 0=(1#32) ∧ s.core.regs 4=sp-(112#32) ∧ s.pc=0x2cab1)
    (nonempty : head nodes≠0 → s.pc=0x2c5d2 ∧ s.core.regs 2=head nodes ∧ s.core.regs 4=sp-(120#32) ∧
      load32 s.core.memory (s.core.regs 4)=(0x2c720#32))
    (ready : head nodes≠0 → Image s.core.memory (s.core.regs 4) trace nodes (0x2cab1#32) ∧
      Layout (s.core.regs 4) trace (E1M1ThingFinish.resolve lines objects) nodes)
    (tracked : OriginalLineCollection.Tracks s.core 0x2ba20 (E1M1ThingFinish.resolve lines objects) r.collected 0)
    (capacity : r.collected.size+nodes.length≤128)
    (represented : Represents s.core.memory lines epoch seen)
    (epochSafe : E1M1ThingVisit.ReadSafe (sp-(120#32)) (0x13580#32))
    (stampSafe : ∀ j<seen.size, E1M1ThingVisit.ReadSafe (sp-(120#32)) (stamp lines j)) :
    let out := result s nodes
    (∃ n≤230*nodes.length+3, X86CodeMemory.Prefix FloorCaller.cm E1M1FiringAdvance.program [] n s out) ∧
    out.core.regs 0=(1#32) ∧ out.core.regs 4=sp-(112#32) ∧ out.pc=0x2cab1 ∧
    (∃ after, collect trace nodes r=.ok after ∧
      OriginalLineCollection.Tracks out.core 0x2ba20 (E1M1ThingFinish.resolve lines objects) after.collected 0) ∧
    Represents out.core.memory lines epoch seen := by
  cases nodes with
  | nil =>
    exact ⟨⟨0,by simp,X86CodeMemory.lift_success (X86Routine.Prefix.nil s) FloorCaller.cm⟩,
      (empty rfl).1,(empty rfl).2.1,(empty rfl).2.2,⟨r,rfl,tracked⟩,represented⟩
  | cons node rest =>
    have present : head (node::rest)≠(0#32) := nonzero node (by simp)
    obtain ⟨pc,cursor,stack,callback⟩ := nonempty present
    obtain ⟨image,layout⟩ := ready present
    have pc' : s.pc=if head (node::rest)=(0#32) then 0x2c5e2 else 0x2c5d2 := by
      rw [if_neg present]; exact pc
    obtain ⟨⟨n,hn,run⟩,success,finalSP,finalPC,after,production,collected⟩ :=
      E1M1ThingTraversal.execution s trace (E1M1ThingFinish.resolve lines objects) (node::rest) 0x2cab1
        layout image cursor pc' r tracked capacity
    have read (a : Word) (safe : E1M1ThingVisit.ReadSafe (sp-(120#32)) a) :=
      E1M1ThingListFrame.traversal_frame s trace (E1M1ThingFinish.resolve lines objects) (node::rest) 0x2cab1
        layout image cursor pc' r tracked capacity a (by rw [stack]; exact safe)
    refine ⟨⟨n,hn,run.transfer E1M1FiringAdvance.program [] E1M1FiringAdvance.contains_prior (by simp)⟩,
      success,?_,finalPC,⟨after,production,collected⟩,
      ⟨(read _ epochSafe).trans represented.1,fun j hj => ?_⟩⟩
    · exact finalSP.trans (by rw [stack]; simp [BitVec.sub_eq_add_neg,BitVec.add_assoc])
    · change load32 (E1M1ThingTraversal.result s (node::rest).length).core.memory (stamp lines j)=epoch ↔ seen[j]! =true
      rw [read _ (stampSafe j hj)]; exact represented.2 j hj
end Doom.Proofs.E1M1NextObjectTraversal
