import Doom.Proofs.E1M1AimEntryQuery
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimPreRayMemory
open Verification X86 X86Memory X86Control BlockSummary
open E1M1CellWalkInvariant (Context Cell)
open E1M1PathMapQuery (traversal withStack)
open E1M1AimQueryCatalog (view)
open E1M1ScanGeometry (linePointer)
attribute [local irreducible] load32 store32

/-- Initial memory with only the future stack address substituted for guards.
This is a specification view, not an assumed executed machine state. -/
def layout (s : X86Memory.State) := withStack s (s.regs 4-(28#32))
def Later (q : Context) (s : X86Memory.State) (a : Word) : Prop :=
  E1M1AimQueryCatalog.Protected q (layout s) a
def Read (q : Context) (s : X86Memory.State) (a : Word) : Prop :=
  E1M1PathMapQuery.Safe s a ∧ Later q s a

theorem safe (s : X86Memory.State) (a : Word)
    (h : E1M1PathMapSetup.Safe (layout s) a) : E1M1PathMapSetup.Safe (traversal s).core a := by
  simpa only [E1M1PathMapSetup.Safe,OriginalPathInit.writes,E1M1PathMapQuery.traversal_stack,
    layout,withStack,write,ite_true] using h

theorem later (q : Context) (s : X86Memory.State) (a : Word) (h : Later q s a) :
    E1M1AimQueryCatalog.Protected q (traversal s).core a :=
  ⟨safe s a h.1,h.2⟩

theorem image (q : Context) (s : X86Memory.State) :
    E1M1AimEntryCatalog.Image (view q s).memory (view q (traversal s).core).memory (Read q s) := by
  intro a h
  exact E1M1PathMapQuery.traversal_frame s a h.1

/-- The callback guard depends on addresses only. Its callback value is created
by setup, so it must not be required to survive setup as an old memory value. -/
theorem callback (q : Context) (s : X86Memory.State)
    (h : E1M1QueryCallback.CallbackSafe q (layout s)) :
    E1M1QueryCallback.CallbackSafe q (traversal s).core :=
  ⟨safe s _ h.initial,h.walk,h.records⟩

/-- All payload reads are protected across both the aim prologue/setup and the
later path initialization. Values themselves are supplied in initial memory. -/
structure PayloadSafe (s : X86Memory.State) (q : Context) (c : Cell) : Prop where
  lines : ∀ i : Fin c.cell.ids.length, ∀ a∈E1M1ScanMemory.lineReads
    (linePointer q.lines c.cell.ids[i.val]) (c.data i.val).v (c.data i.val).w, E1M1PathMapQuery.Safe s a
  back : ∀ i : Fin c.cell.ids.length, E1M1PathMapQuery.Safe s (linePointer q.lines c.cell.ids[i.val]+50)
  objects : ∀ node∈c.nodes, ∀ off∈[(12#32),16,64], E1M1PathMapQuery.Safe s (node.pointer+off)
  links : ∀ node∈c.nodes, E1M1PathMapQuery.Safe s (node.pointer+44)
  global : E1M1PathMapQuery.Safe s 0x2c0f8
  selected : E1M1PathMapQuery.Safe s (E1M1CellObjectSelection.address q.links c.x c.y q.width)

/-- Transport the actual line/object/list payload, including the selected block
head. The payload is not assumed at the reached traversal boundary. -/
theorem payload (s : X86Memory.State) (q : Context) (c : Cell)
    (data : E1M1QueryImages.Payload s.memory q c) (h : PayloadSafe s q c) :
    E1M1QueryImages.Payload (traversal s).core.memory q c ∧
    E1M1QueryImages.Protected (traversal s).core q c := by
  have keep (a : Word) (h : E1M1PathMapQuery.Safe s a) := E1M1PathMapQuery.traversal_frame s a h
  constructor
  · refine ⟨?_,?_,?_,?_,?_,?_⟩
    · intro i
      exact E1M1NextCallbackMemory.line_words _ _ _ _ _ _ (data.encoded i)
        (fun a ha => keep a (h.lines i a ha))
    · intro i; rw [keep _ (h.back i)]; exact data.back i
    · intro node member
      rw [keep _ (h.objects node member _ (by simp)),keep _ (h.objects node member _ (by simp)),
        keep _ (h.objects node member _ (by simp))]
      exact data.objects node member
    · exact E1M1ThingList.linked_transport _ _ _ data.linked
        (fun node member => keep _ (h.links node member))
    · exact (keep _ h.global).trans data.selection.global
    · exact (keep _ h.selected).trans data.selection.selected
  · exact ⟨fun i a ha => E1M1PathMapQuery.traversal_safe s a (h.lines i a ha),
      fun i => E1M1PathMapQuery.traversal_safe s _ (h.back i),
      fun node member off ho => E1M1PathMapQuery.traversal_safe s _ (h.objects node member off ho),
      fun node member => E1M1PathMapQuery.traversal_safe s _ (h.links node member),
      E1M1PathMapQuery.traversal_safe s _ h.global,E1M1PathMapQuery.traversal_safe s _ h.selected⟩
end Doom.Proofs.E1M1AimPreRayMemory
