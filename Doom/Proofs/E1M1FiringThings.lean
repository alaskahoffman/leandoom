import Doom.Proofs.E1M1ThingListInputs
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace Doom.Proofs.E1M1FiringThings
open Verification X86 X86Memory X86Control BlockSummary
open E1M1ScanMemory (firstScan)
open E1M1ScanGeometry (path)
open E1M1ScanContracts (LineData)
open E1M1ThingListInputs (boundary before)
abbrev program := E1M1ThingTraversal.program

theorem contains_entry (pc : Nat) (h : E1M1ThingEntry.program pc≠none) :
    program pc=E1M1ThingEntry.program pc := by
  have h0 := E1M1ThingCallback.contains_prior pc h
  have h1 := E1M1ThingFirstSide.contains_prior pc (by rw [h0]; exact h)
  have h1 := h1.trans h0
  have h2 := E1M1ThingCrossing.contains_prior pc (by rw [h1]; exact h)
  have h2 := h2.trans h1
  have h3 := E1M1ThingFraction.contains_prior pc (by rw [h2]; exact h)
  have h3 := h3.trans h2
  exact (E1M1ThingReturn.contains_prior pc (by rw [h3]; exact h)).trans h3

section Firing
variable (gun : Fire.Gun) (s : X86Memory.State) (weapon : Weapon.Context)
    (actor : Word) (thing : Collision.SolidThing) (angle : Angle) (ox oy : Fixed)
    (xout yout : Int32 × Fixed × Fixed) (base lines : Word) (words : Array Nat)
    (c : E1M1PathMap.Cell) (w h : Nat) (data : Nat → LineData)
    (input : E1M1FiringScan.Inputs gun s weapon actor thing angle ox oy xout yout base lines words c w h data)
include input
attribute [local irreducible] Collision.SolidThing.attackEndpoint

def result (nodes : List E1M1ThingList.Node) :=
  match nodes with
  | [] => boundary gun s weapon actor thing angle ox oy xout yout base lines words c w h data input
  | _::_ => E1M1ThingTraversal.result (boundary gun s weapon actor thing angle ox oy xout yout base lines words c w h data input) nodes.length

variable (returns : E1M1ScanReturn.ReturnSafe (s.regs 4) lines)
    (flag : E1M1ThingGate.FlagSafe (s.regs 4) lines)
    (links : Word) (nodes : List E1M1ThingList.Node)
    (lookupSafe : ∀ a∈E1M1ThingEntry.reads thing angle ox oy w links, E1M1ThingEntry.ReadSafe gun s lines a)
    (global : load32 s.memory (0x2c0f8#32)=links)
    (selected : load32 s.memory (links+(BitVec.ofNat 32 (Collision.pathCellIndex
      (path thing angle ox oy).startBlockX (path thing angle ox oy).startBlockY w) <<< 2))=E1M1ThingList.head nodes)
include returns flag lookupSafe global selected

/-- Both saved words are supplied by actual CALL/prologue writes. Neither word
is an input-memory assumption, even though the whole list uses it repeatedly. -/
theorem saved_words (present : E1M1ThingList.head nodes≠(0#32)) :
    load32 (boundary gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).core.memory ((boundary gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).core.regs 4)=(0x2c720#32) ∧
    load32 (boundary gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).core.memory ((boundary gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).core.regs 4+(4#32))=(0x2cab1#32) := by
  have lookup := E1M1ThingEntry.firing_lookup gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links (E1M1ThingList.head nodes)
    lookupSafe global selected none
  have sp : (boundary gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).core.regs 4=s.regs 4-(120#32) := by
    simpa only [boundary,if_neg present] using lookup.2.2.1
  have call := E1M1ThingCoordinates.firing_call gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag none
  refine ⟨(lookup.2.2.2.2.1 present).2,?_⟩
  rw [sp]
  let called := E1M1ThingGate.called gun s weapon actor thing angle ox oy xout yout base lines words c w h data input
  change load32 (OriginalThingEntry.result called.core).core.memory (s.regs 4-(120#32)+(4#32))=_
  rw [OriginalThingEntry.result_memory]
  have address : s.regs 4-(120#32)+(4#32)=called.core.regs 4 := by
    rw [E1M1ThingEntry.call_stack gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns]
    simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  rw [address,OriginalThingEntry.return_word]
  exact call.2.2.2.2.2.2.1

variable (objects : Nat → Word)
    (d : E1M1ThingListInputs.Data gun s lines (path thing angle ox oy).trace objects nodes)
include d

/-- Assemble the complete list image from firing-entry object values and the
trace written by setup. No reached-state geometry/image is a hypothesis. -/
theorem image (present : E1M1ThingList.head nodes≠(0#32)) :
    E1M1ThingList.Image (boundary gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).core.memory ((boundary gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).core.regs 4)
      (path thing angle ox oy).trace nodes (0x2cab1#32) := by
  have saved := saved_words gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected present
  exact ⟨saved.1,saved.2,E1M1ThingListInputs.geometry gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns objects nodes d,
    E1M1ThingListInputs.linked gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns objects nodes d⟩

/-- The list stack is derived from the caller, rather than guessed at callbacks. -/
theorem layout (present : E1M1ThingList.head nodes≠(0#32)) :
    E1M1ThingList.Layout ((boundary gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).core.regs 4) (path thing angle ox oy).trace
      (E1M1ThingFinish.resolve lines objects) nodes := by
  have lookup := E1M1ThingEntry.firing_lookup gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links (E1M1ThingList.head nodes)
    lookupSafe global selected none
  have sp : (boundary gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).core.regs 4=s.regs 4-(120#32) := by
    simpa only [boundary,if_neg present] using lookup.2.2.1
  rw [sp]
  exact E1M1ThingListInputs.static_layout gun s weapon actor thing angle ox oy xout yout base lines words c w h data input objects nodes d

/-- Continuous execution from either gun's common post-sound boundary, through
the first cell's complete line and object lists, to the grid caller return site. -/
theorem execution (room : c.ids.length+nodes.length≤128)
    (things : Array Collision.SolidThing) (scene : ∀ node∈nodes, things[node.id]?=some node.target)
    (f : Option Flags) :
    let out := result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes
    (∃ steps≤406+281*c.ids.length+230*nodes.length, X86CodeMemory.Prefix FloorCaller.cm program [] steps
      ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ out) ∧
    out.core.regs 0=(1#32) ∧ out.core.regs 4=s.regs 4-(112#32) ∧ out.pc=0x2cab1 ∧
    (∃ after, E1M1ThingTraversal.objectCell (path thing angle ox oy).trace things
      (nodes.map E1M1ThingList.Node.id).toArray (before gun s weapon actor thing angle ox oy xout yout base lines words c w h data input)=.ok after ∧
      OriginalLineCollection.Tracks out.core 0x2ba20 (E1M1ThingFinish.resolve lines objects) after.collected 0) := by
  obtain ⟨⟨n,hn,prior⟩,pc,sp,empty,nonempty,tracked⟩ :=
    E1M1ThingEntry.firing_lookup gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links (E1M1ThingList.head nodes) lookupSafe global selected f
  have converted := E1M1ThingFinish.relabel (boundary gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).core 0x2ba20 lines objects
    (before gun s weapon actor thing angle ox oy xout yout base lines words c w h data input) (E1M1ThingListInputs.all_lines gun s weapon actor thing angle ox oy xout yout base lines words c w h data input) tracked
  have capacity := E1M1ThingListInputs.capacity gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes room
  cases nodes with
  | nil =>
    refine ⟨⟨n,by simp at hn ⊢; omega,prior.transfer program [] contains_entry (by simp)⟩,
      empty rfl,?_,?_,before gun s weapon actor thing angle ox oy xout yout base lines words c w h data input,?_,converted⟩
    · simpa [result,boundary,E1M1ThingList.head] using sp
    · simpa [result,boundary,E1M1ThingList.head] using pc
    · rfl
  | cons node rest =>
    have present : E1M1ThingList.head (node::rest)≠(0#32) := d.nonzero node (by simp)
    have atHead : (boundary gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).pc=0x2c5d2 := by simpa only [boundary,if_neg present] using pc
    have stack : (boundary gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).core.regs 4=s.regs 4-(120#32) := by simpa only [boundary,if_neg present] using sp
    have encoded := image gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links (node::rest) lookupSafe global selected objects d present
    have separated := layout gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links (node::rest) lookupSafe global selected objects d present
    obtain ⟨⟨m,hm,tail⟩,success,finalSP,finalPC,after,production,collected⟩ :=
      E1M1ThingTraversal.execution_cell (boundary gun s weapon actor thing angle ox oy xout yout base lines words c w h data input) (path thing angle ox oy).trace
        (E1M1ThingFinish.resolve lines objects) (node::rest) (0x2cab1#32) separated encoded
        (nonempty present).1 (by simpa only [if_neg present] using atHead)
        (before gun s weapon actor thing angle ox oy xout yout base lines words c w h data input) converted capacity things scene
    refine ⟨⟨n+m,by omega,E1M1PspriteStep.prefix_trans
      (prior.transfer program [] contains_entry (by simp)) tail⟩,success,?_,finalPC,after,production,collected⟩
    exact finalSP.trans (by rw [stack]; simp [BitVec.sub_eq_add_neg,BitVec.add_assoc])
/-- The object-cell fragment includes the actual scene's link-array lookup.
This does not claim correspondence of the surrounding grid-walk loop. -/
def sceneCell (trace : Collision.Divline) (world : Collision.Scene) (x y : Int32)
    (r : Collision.PathResult) : Except String Collision.PathResult := do
  let some ids := world.links[Collision.pathCellIndex x y world.grid.width]? |
    throw "path: missing thing cell"
  E1M1ThingTraversal.objectCell trace world.things ids r

omit input returns flag lookupSafe global selected d in
theorem scene_cell (trace : Collision.Divline) (world : Collision.Scene) (x y : Int32)
    (width : Nat) (nodes : List E1M1ThingList.Node) (r : Collision.PathResult)
    (dimension : world.grid.width=width)
    (ids : world.links[Collision.pathCellIndex x y width]?=some (nodes.map E1M1ThingList.Node.id).toArray) :
    sceneCell trace world x y r=E1M1ThingTraversal.objectCell trace world.things
      (nodes.map E1M1ThingList.Node.id).toArray r := by
  unfold sceneCell
  rw [dimension,ids]

/-- Link the DOS head and finite node chain to the selected production scene
cell, preserving its ID order rather than accepting an unrelated object array. -/
theorem execution_scene (room : c.ids.length+nodes.length≤128)
    (world : Collision.Scene) (dimension : world.grid.width=w)
    (ids : world.links[Collision.pathCellIndex (path thing angle ox oy).startBlockX
      (path thing angle ox oy).startBlockY w]?=some (nodes.map E1M1ThingList.Node.id).toArray)
    (scene : ∀ node∈nodes, world.things[node.id]?=some node.target) (f : Option Flags) :
    let out := result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes
    (∃ steps≤406+281*c.ids.length+230*nodes.length, X86CodeMemory.Prefix FloorCaller.cm program [] steps
      ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ out) ∧
    out.core.regs 0=(1#32) ∧ out.core.regs 4=s.regs 4-(112#32) ∧ out.pc=0x2cab1 ∧
    (∃ after, sceneCell (path thing angle ox oy).trace world (path thing angle ox oy).startBlockX
      (path thing angle ox oy).startBlockY (before gun s weapon actor thing angle ox oy xout yout base lines words c w h data input)=.ok after ∧
      OriginalLineCollection.Tracks out.core 0x2ba20 (E1M1ThingFinish.resolve lines objects) after.collected 0) := by
  rw [scene_cell _ world _ _ w nodes _ dimension ids]
  exact execution gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d room world.things scene f
end Firing
end Doom.Proofs.E1M1FiringThings
