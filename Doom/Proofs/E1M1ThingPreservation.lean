import Doom.Proofs.E1M1FiringThings
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1ThingPreservation
open Verification X86 X86Memory X86Control BlockSummary
open OriginalLineCoordinates (register)
open E1M1ThingVisit (entry result)

/-- Offsets relative to the iterator's stack and callback body stack. -/
def savedOffset (x : Bool) : Word := if x then 20 else 12
def popOffset (x : Bool) : Word := if x then 32 else 40

theorem slot_address (sp : Word) (x : Bool) :
    sp-(52#32)+popOffset x=sp-savedOffset x := by
  cases x <;> simp [popOffset,savedOffset,BitVec.sub_eq_add_neg,BitVec.add_assoc]

theorem saved_prologue (s : X86Memory.State) (x : Bool) :
    load32 (OriginalThingCallback.prepared s).memory
      (s.regs 4-(savedOffset x-(4#32)))=s.regs (register x) := by
  rw [(OriginalThingCallback.prepare_observe s).2.2.2]
  have apart (a b : Word) (h : Apart (-a) (-b)) := OriginalThingCallback.slots_apart (s.regs 4) a b h
  cases x
  · change load32 (store32 (store32 (store32 (store32 (store32 _ (s.regs 4-(8#32)) (s.regs 1))
      (s.regs 4-(12#32)) _) (s.regs 4-(16#32)) _) (s.regs 4-(20#32)) _) (s.regs 4-(24#32)) _) (s.regs 4-(8#32))=s.regs 1
    rw [load_store_apart _ _ _ _ (apart (8#32) (24#32) (by unfold Apart; decide)),
      load_store_apart _ _ _ _ (apart (8#32) (20#32) (by unfold Apart; decide)),
      load_store_apart _ _ _ _ (apart (8#32) (16#32) (by unfold Apart; decide)),
      load_store_apart _ _ _ _ (apart (8#32) (12#32) (by unfold Apart; decide)),load_store]
  · change load32 (store32 (store32 (store32 _ (s.regs 4-(16#32)) (s.regs 6))
      (s.regs 4-(20#32)) _) (s.regs 4-(24#32)) _) (s.regs 4-(16#32))=s.regs 6
    rw [load_store_apart _ _ _ _ (apart (16#32) (24#32) (by unfold Apart; decide)),
      load_store_apart _ _ _ _ (apart (16#32) (20#32) (by unfold Apart; decide)),load_store]

theorem entry_saved (s : X86Control.State) (x : Bool) :
    load32 (entry s).core.memory ((entry s).core.regs 4+popOffset x)=s.core.regs (register x) := by
  have sp : (entry s).core.regs 4=s.core.regs 4-(52#32) := (OriginalThingCallback.enter_observe s.core s.flags).2.2.1
  rw [sp,slot_address]
  have saved := saved_prologue (OriginalThingCallback.called s.core s.flags).core x
  change load32 (OriginalThingCallback.prepared (OriginalThingCallback.called s.core s.flags).core).memory _=_
  rw [show s.core.regs 4-savedOffset x=(OriginalThingCallback.called s.core s.flags).core.regs 4-(savedOffset x-(4#32)) by
    rw [(OriginalThingCallback.call_observe s.core s.flags).2.2.1]
    cases x <;> simp [savedOffset,BitVec.sub_eq_add_neg,BitVec.add_assoc]]
  apply saved.trans
  cases x <;> simp [OriginalThingCallback.called,OriginalThingCallback.argument,X86Routine.pushWord,put,write,register]

theorem finish_coordinate (s : X86Control.State) (x : Bool) :
    (OriginalThingFinish.result s).core.regs (register x)=
      load32 (OriginalThingFinish.result s).core.memory (s.core.regs 4+popOffset x) := by
  unfold OriginalThingFinish.result
  split <;> cases x <;> simp [register,popOffset,
    (OriginalThingFinish.unwind_observe _).2.2.2.2.2.1,
    (OriginalThingFinish.unwind_observe _).2.2.2.2.2.2.2.1,
    (OriginalThingFinish.unwind_observe _).1,(OriginalThingFinish.inserted_regs _).2]

theorem resume_coordinate (s : X86Memory.State) (x : Bool) :
    (OriginalThingCallback.resumed s).core.regs (register x)=s.regs (register x) := by
  unfold OriginalThingCallback.resumed
  split <;> cases x <;> simp [register,OriginalThingCallback.advanced,put,write]

set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] load32 OriginalDivlineSide.result OriginalThingSecondSide.result OriginalThingFraction.result

/-- Both grid coordinates survive the full object callback. Existing stack
separation supplies protection for the saved words, including insertion writes. -/
theorem visit_coordinate (s : X86Control.State) (trace : Collision.Divline)
    (target : Collision.SolidThing) (h : E1M1ThingVisit.Inputs s trace target)
    (resolve : Collision.Intercept → Word) (r : Collision.PathResult)
    (tracked : OriginalLineCollection.Tracks s.core 0x2ba20 resolve r.collected 0)
    (capacity : r.collected.size<128) (x : Bool) :
    (result s).core.regs (register x)=s.core.regs (register x) := by
  have sp : (entry s).core.regs 4=s.core.regs 4-(52#32) := (OriginalThingCallback.enter_observe s.core s.flags).2.2.1
  have collection := E1M1ThingVisit.body_collection s trace target h resolve r tracked
  have cursor : OriginalThingFinish.cursor (E1M1ThingReturn.view (entry s).core).core=
      0x2ba20+BitVec.ofNat 32 (12*r.collected.size) := collection.cursor
  have savedSafe : OriginalLineMixedInvariant.ArraySafe 0x2ba20
      ((entry s).core.regs 4+popOffset x) := by
    rw [sp,slot_address]
    exact h.stack.enter (savedOffset x) (by cases x <;> decide)
  have keep := OriginalThingFinish.frame (E1M1ThingReturn.view (entry s).core)
    ((entry s).core.regs 4+popOffset x) (by
      intro w hw
      rw [cursor] at hw
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with rfl|rfl|rfl|rfl
      · simpa only [OriginalLineCollection.slot,BitVec.add_zero] using savedSafe.1 r.collected.size capacity (0#32) (by simp)
      · exact savedSafe.1 r.collected.size capacity (4#32) (by simp)
      · exact savedSafe.1 r.collected.size capacity (8#32) (by simp)
      · exact savedSafe.2)
  change (OriginalThingCallback.resumed (E1M1ThingReturn.finished (entry s).core).core).core.regs (register x)=_
  rw [resume_coordinate,E1M1ThingReturn.finished,finish_coordinate,(E1M1ThingReturn.view_regs _).1]
  exact keep.trans ((E1M1ThingReturn.view_saved (entry s).core (popOffset x)
    (by cases x <;> simp [popOffset])).trans (entry_saved s x))
open E1M1ThingList (Layout Image head run)

/-- Reuse list-image transport to preserve coordinates across every node. -/
theorem run_coordinate (s : X86Control.State) (trace : Collision.Divline)
    (resolve : Collision.Intercept → Word) (nodes : List E1M1ThingList.Node) (ret : Word)
    (layout : Layout (s.core.regs 4) trace resolve nodes)
    (image : Image s.core.memory (s.core.regs 4) trace nodes ret)
    (cursor : s.core.regs 2=head nodes)
    (pc : s.pc=if head nodes=(0#32) then 0x2c5e2 else 0x2c5d2)
    (r : Collision.PathResult) (tracked : OriginalLineCollection.Tracks s.core 0x2ba20 resolve r.collected 0)
    (capacity : r.collected.size+nodes.length≤128) (x : Bool) :
    (run nodes.length s).core.regs (register x)=s.core.regs (register x) := by
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
      (by rw [sp]; exact imageNext) cursorNext (by rw [cursorNext] at pcNext; exact pcNext) after encoded space
    exact tail.trans (visit_coordinate s trace node.target h resolve r tracked room x)

theorem return_coordinate (s : X86Memory.State) (x : Bool) :
    (OriginalThingEntry.returned s).core.regs (register x)=s.regs (register x) := by
  cases x <;> simp [OriginalThingEntry.returned,OriginalThingEntry.r2,OriginalThingEntry.r1,register,put,write]

/-- Complete finite traversal and iterator epilogue preserve the caller's cell. -/
theorem traversal_coordinate (s : X86Control.State) (trace : Collision.Divline)
    (resolve : Collision.Intercept → Word) (nodes : List E1M1ThingList.Node) (ret : Word)
    (layout : Layout (s.core.regs 4) trace resolve nodes)
    (image : Image s.core.memory (s.core.regs 4) trace nodes ret)
    (cursor : s.core.regs 2=head nodes)
    (pc : s.pc=if head nodes=(0#32) then 0x2c5e2 else 0x2c5d2)
    (r : Collision.PathResult) (tracked : OriginalLineCollection.Tracks s.core 0x2ba20 resolve r.collected 0)
    (capacity : r.collected.size+nodes.length≤128) (x : Bool) :
    (E1M1ThingTraversal.result s nodes.length).core.regs (register x)=s.core.regs (register x) := by
  rw [E1M1ThingTraversal.result,return_coordinate]
  exact run_coordinate s trace resolve nodes ret layout image cursor pc r tracked capacity x

set_option backward.isDefEq.respectTransparency false
/-- Iterator setup, bounds and empty-cell exits also preserve both coordinates. -/
theorem lookup_coordinate (s : X86Memory.State) (x : Bool) :
    (OriginalThingEntry.result s).core.regs (register x)=s.regs (register x) := by
  have guarded (t : X86Memory.State) :
      (OriginalThingEntry.guarded t).core.regs (register x)=t.regs (register x) := by
    unfold OriginalThingEntry.guarded
    split <;> (try split) <;> (try split) <;> cases x <;>
      simp [OriginalThingEntry.loaded,register,put,write]
  have lookup (t : X86Memory.State) :
      (OriginalThingEntry.lookup t).core.regs (register x)=t.regs (register x) := by
    cases x <;> simp [OriginalThingEntry.lookup,OriginalThingEntry.loadedHead,OriginalThingEntry.l3,
      OriginalThingEntry.l2,OriginalThingEntry.l1,register,put,write]
  unfold OriginalThingEntry.result OriginalThingEntry.finishLookup
  split <;> (try split) <;> (try rw [return_coordinate]) <;> (try rw [lookup]) <;> rw [guarded] <;>
    cases x <;> simp [OriginalThingEntry.entry,OriginalThingEntry.allocated,register,put,write]
end Doom.Proofs.E1M1ThingPreservation
