import Doom.Proofs.E1M1ThingPreservation
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace Doom.Proofs.E1M1ThingListFrame
open Verification X86 X86Memory X86Control BlockSummary
open E1M1ThingList (Layout Image head run)
open E1M1ThingVisit (result)
/-- An arbitrary protected word survives the entire finite object list. The
initial read separation is rebased with the proved per-visit stack restoration. -/
theorem run_frame (s : X86Control.State) (trace : Collision.Divline)
    (resolve : Collision.Intercept → Word) (nodes : List E1M1ThingList.Node) (ret : Word)
    (layout : Layout (s.core.regs 4) trace resolve nodes)
    (image : Image s.core.memory (s.core.regs 4) trace nodes ret)
    (cursor : s.core.regs 2=head nodes)
    (pc : s.pc=if head nodes=(0#32) then 0x2c5e2 else 0x2c5d2)
    (r : Collision.PathResult) (tracked : OriginalLineCollection.Tracks s.core 0x2ba20 resolve r.collected 0)
    (capacity : r.collected.size+nodes.length≤128)
    (a : Word) (safe : E1M1ThingVisit.ReadSafe (s.core.regs 4) a) :
    load32 (run nodes.length s).core.memory a=load32 s.core.memory a := by
  induction nodes generalizing s r with
  | nil => rfl
  | cons node rest ih =>
    have nonzero := layout.nonzero node (by simp)
    have cursor' : s.core.regs 2=node.pointer := cursor
    have pc' : s.pc=0x2c5d2 := by simpa [head,nonzero] using pc
    have room : r.collected.size<128 := by simp only [List.length_cons] at capacity; omega
    have h := E1M1ThingList.visit_inputs s trace resolve node rest ret layout image cursor'
    have pointer (frac : Fixed) : resolve ⟨frac,false,node.id⟩=s.core.regs 2 := (layout.pointer node (by simp) frac).trans cursor'.symm
    obtain ⟨_,sp,next,pcNext,after,produced,encoded⟩ :=
      E1M1ThingVisit.execution s trace node.target h pc' resolve node.id r pointer tracked room
    obtain ⟨imageNext,link⟩ := E1M1ThingList.image_tail s trace resolve node rest ret layout image cursor' r tracked room
    have cursorNext : (result s).core.regs 2=head rest := by rw [cursor'] at next; exact next.trans link
    have space : after.collected.size+rest.length≤128 := by
      have size := E1M1ThingList.collect_size trace node.target node.id r after produced
      simp only [List.length_cons] at capacity
      omega
    have tail := ih (result s) (by rw [sp]; exact E1M1ThingList.layout_tail _ _ _ _ _ layout)
      (by rw [sp]; exact imageNext) cursorNext (by rw [cursorNext] at pcNext; exact pcNext) after encoded space (by rw [sp]; exact safe)
    exact tail.trans (E1M1ThingVisit.frame s trace node.target h resolve r tracked room a safe)

/-- The real iterator return performs no further memory writes. -/
theorem traversal_frame (s : X86Control.State) (trace : Collision.Divline)
    (resolve : Collision.Intercept → Word) (nodes : List E1M1ThingList.Node) (ret : Word)
    (layout : Layout (s.core.regs 4) trace resolve nodes)
    (image : Image s.core.memory (s.core.regs 4) trace nodes ret)
    (cursor : s.core.regs 2=head nodes)
    (pc : s.pc=if head nodes=(0#32) then 0x2c5e2 else 0x2c5d2)
    (r : Collision.PathResult) (tracked : OriginalLineCollection.Tracks s.core 0x2ba20 resolve r.collected 0)
    (capacity : r.collected.size+nodes.length≤128)
    (a : Word) (safe : E1M1ThingVisit.ReadSafe (s.core.regs 4) a) :
    load32 (E1M1ThingTraversal.result s nodes.length).core.memory a=load32 s.core.memory a := by
  rw [E1M1ThingTraversal.result,(E1M1ThingTraversal.return_observe _).1]
  exact run_frame s trace resolve nodes ret layout image cursor pc r tracked capacity a safe

end Doom.Proofs.E1M1ThingListFrame
