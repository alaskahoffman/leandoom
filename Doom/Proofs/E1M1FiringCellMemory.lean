import Doom.Proofs.E1M1NextCellScan
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
namespace Doom.Proofs.E1M1FiringCellMemory
open Verification X86 X86Memory X86Control BlockSummary
open E1M1ScanGeometry (path)
open E1M1ScanContracts (LineData)
open E1M1ThingListInputs (boundary before)
attribute [local irreducible] load32

section Firing
variable (gun : Fire.Gun) (s : X86Memory.State) (weapon : Weapon.Context)
    (actor : Word) (thing : Collision.SolidThing) (angle : Angle) (ox oy : Fixed)
    (xout yout : Int32 × Fixed × Fixed) (base lines : Word) (words : Array Nat)
    (c : E1M1PathMap.Cell) (w h : Nat) (data : Nat → LineData)
    (input : E1M1FiringScan.Inputs gun s weapon actor thing angle ox oy xout yout base lines words c w h data)
include input


attribute [local irreducible] Collision.SolidThing.attackEndpoint

variable (returns : E1M1ScanReturn.ReturnSafe (s.regs 4) lines)
    (flag : E1M1ThingGate.FlagSafe (s.regs 4) lines)
    (links : Word) (nodes : List E1M1ThingList.Node)
    (lookupSafe : ∀ a∈E1M1ThingEntry.reads thing angle ox oy w links, E1M1ThingEntry.ReadSafe gun s lines a)
    (global : load32 s.memory (0x2c0f8#32)=links)
    (selected : load32 s.memory (links+(BitVec.ofNat 32 (Collision.pathCellIndex
      (path thing angle ox oy).startBlockX (path thing angle ox oy).startBlockY w) <<< 2))=E1M1ThingList.head nodes)
include returns flag lookupSafe global selected

variable (objects : Nat → Word)
    (d : E1M1ThingListInputs.Data gun s lines (path thing angle ox oy).trace objects nodes)
include d

/-- The completed object list preserves arbitrary protected words. -/
theorem object_frame (room : c.ids.length+nodes.length≤128) (a : Word)
    (safeWord : E1M1ThingVisit.ReadSafe (s.regs 4-(120#32)) a) :
    load32 (E1M1FiringThings.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes).core.memory a=
      load32 (boundary gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).core.memory a := by
  cases nodes with
  | nil => rfl
  | cons node rest =>
    have present : E1M1ThingList.head (node::rest)≠(0#32) := d.nonzero node (by simp)
    obtain ⟨_,pc,sp,_,nonempty,tracked⟩ := E1M1ThingEntry.firing_lookup gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links
      (E1M1ThingList.head (node::rest)) lookupSafe global selected none
    have converted := E1M1ThingFinish.relabel (boundary gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).core 0x2ba20 lines objects
      (before gun s weapon actor thing angle ox oy xout yout base lines words c w h data input) (E1M1ThingListInputs.all_lines gun s weapon actor thing angle ox oy xout yout base lines words c w h data input) tracked
    have encoded := E1M1FiringThings.image gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links (node::rest) lookupSafe global selected objects d present
    have separated := E1M1FiringThings.layout gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links (node::rest) lookupSafe global selected objects d present
    have capacity := E1M1ThingListInputs.capacity gun s weapon actor thing angle ox oy xout yout base lines words c w h data input (node::rest) room
    have safe : E1M1ThingVisit.ReadSafe ((boundary gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).core.regs 4) a := by
      change E1M1ThingVisit.ReadSafe ((E1M1ThingEntry.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).core.regs 4) _
      rw [if_neg present] at sp
      rw [sp]
      exact safeWord
    exact (E1M1ThingListFrame.traversal_frame (boundary gun s weapon actor thing angle ox oy xout yout base lines words c w h data input) (path thing angle ox oy).trace
      (E1M1ThingFinish.resolve lines objects) (node::rest) (0x2cab1#32) separated encoded
      (nonempty present).1 (by simpa only [boundary,if_neg present] using pc)
      (before gun s weapon actor thing angle ox oy xout yout base lines words c w h data input) converted capacity a safe)



/-- Every protected initial word survives the actual first-cell line scan,
object lookup, entire object list and caller return test. -/
theorem firing_frame (room : c.ids.length+nodes.length≤128) (a : Word)
    (entrySafe : E1M1ThingEntry.ReadSafe gun s lines a)
    (objectSafe : E1M1ThingVisit.ReadSafe (s.regs 4-(120#32)) a) :
    load32 (E1M1FiringCellReturn.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes).core.memory a=load32 s.memory a := by
  exact (object_frame gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d room a objectSafe).trans
    (E1M1ThingListInputs.entry_read gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns a entrySafe)

/-- Start after the line scan: this also preserves mutable stamps in their
new state, without pretending they still equal firing-entry memory. -/
theorem after_lines_frame (room : c.ids.length+nodes.length≤128) (a : Word)
    (callSafe : Apart a (s.regs 4-(116#32)))
    (entrySafe : Apart a (s.regs 4-(120#32)))
    (objectSafe : E1M1ThingVisit.ReadSafe (s.regs 4-(120#32)) a) :
    load32 (E1M1FiringCellReturn.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes).core.memory a=
      load32 (E1M1ScanReturn.finished gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).1.core.memory a := by
  apply (object_frame gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d room a objectSafe).trans
  apply (OriginalThingEntry.frame _ a ?_).trans
  · apply OriginalPathCell.call_frame false _ _ a
    change Apart a ((E1M1ScanReturn.finished gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).1.core.regs 4-(4#32))
    rw [(E1M1ScanReturn.parent_return gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns).2.1]
    simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using callSafe
  · rw [E1M1ThingEntry.call_stack gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns]
    simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using entrySafe

end Firing
end Doom.Proofs.E1M1FiringCellMemory
