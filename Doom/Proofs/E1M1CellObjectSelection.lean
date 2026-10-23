import Doom.Proofs.E1M1FiringNextScene
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1CellObjectSelection
open Verification X86 X86Memory X86Control BlockSummary
attribute [local irreducible] load32

def address (links : Word) (x y : Int32) (width : Nat) :=
  links+(BitVec.ofNat 32 (Collision.pathCellIndex x y width) <<< 2)

/-- The actual table pointer and selected head, separate from the node image. -/
structure Image (m : Memory) (links : Word) (x y : Int32) (width : Nat)
    (nodes : List E1M1ThingList.Node) : Prop where
  global : load32 m (0x2c0f8#32)=links
  selected : load32 m (address links x y width)=E1M1ThingList.head nodes

structure Protected (sp lines links : Word) (x y : Int32) (width : Nat) : Prop where
  global : E1M1FiringMapState.Safe sp lines (0x2c0f8#32)
  selected : E1M1FiringMapState.Safe sp lines (address links x y width)

/-- Selection follows the same persistent frame as node geometry and links. -/
theorem transport (m n : Memory) (sp lines links : Word) (x y : Int32) (width : Nat)
    (nodes : List E1M1ThingList.Node) (image : Image m links x y width nodes)
    (safe : Protected sp lines links x y width) (frame : E1M1CellMapInvariant.Frame sp lines m n) :
    Image n links x y width nodes :=
  ⟨(frame _ safe.global).trans image.global,(frame _ safe.selected).trans image.selected⟩

def result (s : X86Control.State) := OriginalThingEntry.result (E1M1FiringNextThings.called s).core

/-- Only the actual CALL return word and iterator callback PUSH can write. -/
theorem read_word (s : X86Control.State) (sp : Word) (stack : s.core.regs 4=sp-(112#32))
    (a : Word) (callSafe : Apart a (sp-(116#32))) (entrySafe : Apart a (sp-(120#32))) :
    load32 (result s).core.memory a=load32 s.core.memory a := by
  have callStack := (OriginalPathCell.call_inputs false s.core (OriginalPathCell.gateFlags false s.core)).2.2.2.1
  have callAddr : (E1M1FiringNextThings.called s).core.regs 4=sp-(116#32) := by
    rw [stack] at callStack
    simpa [E1M1FiringNextThings.called,BitVec.sub_eq_add_neg,BitVec.add_assoc] using callStack
  apply (OriginalThingEntry.frame _ a ?_).trans
    (OriginalPathCell.call_frame false s.core _ a ?_)
  · change Apart a ((E1M1FiringNextThings.called s).core.regs 4-(4#32))
    rw [callAddr]
    simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using entrySafe
  · rw [stack]
    simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using callSafe

theorem frame (s : X86Control.State) (sp lines : Word) (stack : s.core.regs 4=sp-(112#32)) :
    E1M1CellMapInvariant.Frame sp lines s.core.memory (result s).core.memory :=
  fun a safe => read_word s sp stack a (safe.caller 116 (by simp)) (safe.caller 120 (by simp))

/-- The caller view at lookup has the original numeric grid state, including
positive locals; this holds for empty and nonempty lookup outcomes. -/
theorem observe (s : X86Control.State) (sp : Word) (stack : s.core.regs 4=sp-(112#32)) :
    E1M1PathAdvance.observe (E1M1ObjectBoundary.callerView (result s) sp)=E1M1PathAdvance.observe s.core := by
  apply E1M1FiringGridState.transport
  · intro reg member
    have neq : reg≠4 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl|rfl|rfl <;> decide
    simpa [E1M1ObjectBoundary.callerView,put,write,neq,result] using E1M1NextScanGrid.lookup_register s reg member
  · intro off member
    change load32 (result s).core.memory (sp-(112#32)+off)=load32 s.core.memory (s.core.regs 4+off)
    rw [stack]
    exact read_word s sp stack _ (E1M1GridLocals.below sp off member ⟨0,by decide⟩)
      (E1M1GridLocals.below sp off member ⟨1,by decide⟩)

/-- The callback PUSH preserves the actual CALL return word. -/
theorem caller_word (s : X86Control.State) (sp : Word) (stack : s.core.regs 4=sp-(112#32)) :
    load32 (result s).core.memory (sp-(116#32))=(0x2cab1#32) := by
  let call := E1M1FiringNextThings.called s
  have obs := OriginalPathCell.call_inputs false s.core (OriginalPathCell.gateFlags false s.core)
  have callStack : call.core.regs 4=sp-(116#32) := by
    have h := obs.2.2.2.1
    rw [stack] at h
    simpa [call,E1M1FiringNextThings.called,BitVec.sub_eq_add_neg,BitVec.add_assoc] using h
  change load32 (OriginalThingEntry.result call.core).core.memory _=_
  rw [←callStack,OriginalThingEntry.result_memory,OriginalThingEntry.return_word]
  dsimp only [call,E1M1FiringNextThings.called]
  rw [obs.2.2.2.1]
  exact obs.2.2.2.2.1
end Doom.Proofs.E1M1CellObjectSelection
