import Doom.Proofs.E1M1GridLocals
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1FiringGridState
open Verification X86 X86Memory X86Control BlockSummary
open E1M1ScanMemory (firstScan)
open E1M1ScanGeometry (path)
open E1M1ScanContracts (LineData)
open E1M1ThingListInputs (boundary before)
open E1M1GridLocals (address offsets)
attribute [local irreducible] load32 Collision.pathFirstIntercept

/-- Complete numeric state initialized by the production path calculations. -/
def initial (p : Collision.PathStart) (xout yout : Int32 × Fixed × Fixed) : E1M1PathAdvance.Cell :=
  ⟨p.startBlockX.toBitVec,p.startBlockY.toBitVec,p.endBlockX.toBitVec,p.endBlockY.toBitVec,
    (Collision.pathFirstIntercept p.x1 yout.2.1 yout.2.2).raw.toBitVec,
    (Collision.pathFirstIntercept p.y1 xout.2.1 xout.2.2).raw.toBitVec,
    xout.1.toBitVec,yout.1.toBitVec,yout.2.2.raw.toBitVec,xout.2.2.raw.toBitVec,0⟩

/-- Assemble a numeric observation without unfolding the preceding execution. -/
theorem of_ready (sp : Word) (t : X86Control.State) (p : Collision.PathStart)
    (xout yout : Int32 × Fixed × Fixed) (ready : E1M1PathGridSetup.Ready sp t p xout yout)
    (endX : load32 t.core.memory (t.core.regs 4+(20#32))=p.endBlockX.toBitVec)
    (endY : load32 t.core.memory (t.core.regs 4+(24#32))=p.endBlockY.toBitVec) :
    E1M1PathAdvance.observe t.core=initial p xout yout := by
  simp only [E1M1PathAdvance.observe,OriginalPathAdvance.localWord,initial]
  congr 1
  · exact ready.mapX
  · exact ready.mapY
  · exact ready.xIntercept
  · rw [ready.stack]; exact ready.yIntercept
  · rw [ready.stack]; exact ready.xDirection
  · rw [ready.stack]; exact ready.yDirection
  · rw [ready.stack]; exact ready.xStride
  · rw [ready.stack]; exact ready.yStride
  · exact ready.counter

/-- Reuse the observation shape to transport four registers and seven locals. -/
theorem transport (t u : X86Memory.State)
    (regs : ∀ r∈([1,5,6,7] : List (Fin 8)), t.regs r=u.regs r)
    (locals : ∀ off∈offsets, OriginalPathAdvance.localWord t off=OriginalPathAdvance.localWord u off) :
    E1M1PathAdvance.observe t=E1M1PathAdvance.observe u := by
  unfold E1M1PathAdvance.observe
  congr 1
  · exact regs 6 (by simp)
  · exact regs 1 (by simp)
  · exact locals 20 (by simp [offsets])
  · exact locals 24 (by simp [offsets])
  · exact regs 5 (by simp)
  · exact locals 44 (by simp [offsets])
  · exact locals 32 (by simp [offsets])
  · exact locals 28 (by simp [offsets])
  · exact locals 36 (by simp [offsets])
  · exact locals 40 (by simp [offsets])
  · exact regs 7 (by simp)

section Firing
variable (gun : Fire.Gun) (s : X86Memory.State) (weapon : Weapon.Context)
    (actor : Word) (thing : Collision.SolidThing) (angle : Angle) (ox oy : Fixed)
    (xout yout : Int32 × Fixed × Fixed) (base lines : Word) (words : Array Nat)
    (c : E1M1PathMap.Cell) (w h : Nat) (data : Nat → LineData)
    (input : E1M1FiringScan.Inputs gun s weapon actor thing angle ox oy xout yout base lines words c w h data)
include input


attribute [local irreducible] Collision.SolidThing.attackEndpoint

/-- Stack position derived from the original firing and initialization prefix. -/
theorem grid_stack : (E1M1PathGridSetup.firstGrid gun s).core.regs 4=s.regs 4-(112#32) := by
  have geometry := E1M1AimGeometry.path_inputs _ thing angle _ ox oy
    (E1M1FiringGeometry.query_geometry gun s actor thing angle ox oy input.geometry)
  have sp := E1M1PathMapSetup.grid_stack _ ox oy _ _ _ _ geometry
  change (E1M1PathGridSetup.firstGrid gun s).core.regs 4=(E1M1AimSetup.firstTraversal gun s).core.regs 4-(60#32) at sp
  rw [E1M1ScanMemory.firing_stack] at sp
  simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using sp

/-- All eleven fields, including endpoints, are supplied by initialization. -/
theorem initial_observe :
    E1M1PathAdvance.observe (E1M1PathGridSetup.firstGrid gun s).core=initial (path thing angle ox oy) xout yout := by
  have geometry := E1M1AimGeometry.path_inputs _ thing angle _ ox oy
    (E1M1FiringGeometry.query_geometry gun s actor thing angle ox oy input.geometry)
  have grid := (E1M1PathGridSetup.grid_observation_from_init _ ox oy _ _ _ _ geometry
    xout yout input.okX input.okY).2
  have ends := E1M1GridLocals.endpoints _ ox oy _ _ _ _ geometry
  exact of_ready _ _ _ _ _ grid ends.1 ends.2

/-- CALL and the line-iterator prologue cannot overwrite positive grid locals. -/
theorem caller_local (off : Word) (member : off∈offsets) :
    load32 (firstScan gun s).core.memory (address (s.regs 4) off)=
      load32 (E1M1PathGridSetup.firstGrid gun s).core.memory (address (s.regs 4) off) := by
  apply E1M1ScanMemory.caller_frame
  have sp := grid_stack gun s weapon actor thing angle ox oy xout yout base lines words c w h data input
  change Apart _ (_-(4#32)) ∧ Apart _ (_-(8#32)) ∧ Apart _ (_-(12#32))
  rw [sp]
  exact ⟨by simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using E1M1GridLocals.below (s.regs 4) off member ⟨0,by decide⟩,
    by simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using E1M1GridLocals.below (s.regs 4) off member ⟨1,by decide⟩,
    by simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using E1M1GridLocals.below (s.regs 4) off member ⟨2,by decide⟩⟩

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

variable (locals : E1M1GridLocals.Safe (s.regs 4) lines)
include locals

omit flag lookupSafe global selected d in
/-- Freshly initialized locals survive the line scan and object-iterator lookup. -/
theorem boundary_local (off : Word) (member : off∈offsets) :
    load32 (boundary gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).core.memory (address (s.regs 4) off)=
      load32 (E1M1PathGridSetup.firstGrid gun s).core.memory (address (s.regs 4) off) := by
  exact (E1M1ThingListInputs.trace_read gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns _
    (E1M1GridLocals.scan_safe _ _ off member locals)
    (E1M1GridLocals.below _ off member ⟨0,by decide⟩)
    (E1M1GridLocals.below _ off member ⟨1,by decide⟩)).trans
    (caller_local gun s weapon actor thing angle ox oy xout yout base lines words c w h data input off member)

/-- Full object traversal preserves each initialized local, including empty lists. -/
theorem firing_local (room : c.ids.length+nodes.length≤128) (off : Word) (member : off∈offsets) :
    load32 (E1M1FiringThings.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes).core.memory (address (s.regs 4) off)=
      load32 (E1M1PathGridSetup.firstGrid gun s).core.memory (address (s.regs 4) off) := by
  have old := boundary_local gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns locals off member
  cases nodes with
  | nil => exact old
  | cons node rest =>
    have present : E1M1ThingList.head (node::rest)≠(0#32) := d.nonzero node (by simp)
    obtain ⟨_,pc,sp,_,nonempty,tracked⟩ := E1M1ThingEntry.firing_lookup gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links
      (E1M1ThingList.head (node::rest)) lookupSafe global selected none
    have converted := E1M1ThingFinish.relabel (boundary gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).core 0x2ba20 lines objects
      (before gun s weapon actor thing angle ox oy xout yout base lines words c w h data input) (E1M1ThingListInputs.all_lines gun s weapon actor thing angle ox oy xout yout base lines words c w h data input) tracked
    have encoded := E1M1FiringThings.image gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links (node::rest) lookupSafe global selected objects d present
    have separated := E1M1FiringThings.layout gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links (node::rest) lookupSafe global selected objects d present
    have capacity := E1M1ThingListInputs.capacity gun s weapon actor thing angle ox oy xout yout base lines words c w h data input (node::rest) room
    have safe : E1M1ThingVisit.ReadSafe ((boundary gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).core.regs 4) (address (s.regs 4) off) := by
      change E1M1ThingVisit.ReadSafe ((E1M1ThingEntry.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).core.regs 4) _
      rw [if_neg present] at sp
      rw [sp]
      exact E1M1GridLocals.thing_safe _ _ off member locals
    exact (E1M1ThingListFrame.traversal_frame (boundary gun s weapon actor thing angle ox oy xout yout base lines words c w h data input) (path thing angle ox oy).trace
      (E1M1ThingFinish.resolve lines objects) (node::rest) (0x2cab1#32) separated encoded
      (nonempty present).1 (by simpa only [boundary,if_neg present] using pc)
      (before gun s weapon actor thing angle ox oy xout yout base lines words c w h data input) converted capacity (address (s.regs 4) off) safe).trans old


/-- The first completed cell has the entire initialized numeric grid state,
not merely correct coordinates or a step relative to unspecified locals. -/
theorem before_observe (room : c.ids.length+nodes.length≤128)
    (things : Array Collision.SolidThing) (scene : ∀ node∈nodes, things[node.id]?=some node.target) :
    E1M1PathAdvance.observe (E1M1FiringCellReturn.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes).core=
      initial (path thing angle ox oy) xout yout := by
  have start := initial_observe gun s weapon actor thing angle ox oy xout yout base lines words c w h data input
  have regs := E1M1FiringGridRegisters.before_advance gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d room
  have x := E1M1FiringCellReturn.firing_coordinate gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d room true
  have y := E1M1FiringCellReturn.firing_coordinate gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d room false
  have sp := (E1M1FiringThings.execution gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d room things scene none).2.2.1
  change (E1M1FiringCellReturn.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes).core.regs 4=_ at sp
  have keep (off : Word) (member : off∈offsets) :
      OriginalPathAdvance.localWord (E1M1FiringCellReturn.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes).core off=
        OriginalPathAdvance.localWord (E1M1PathGridSetup.firstGrid gun s).core off := by
    unfold OriginalPathAdvance.localWord
    rw [sp,grid_stack gun s weapon actor thing angle ox oy xout yout base lines words c w h data input]
    exact firing_local gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d locals room off member
  apply Eq.trans (transport _ _ ?_ keep) start
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl
  · exact y.trans (congrArg E1M1PathAdvance.Cell.mapY start).symm
  · exact regs.1.trans (congrArg E1M1PathAdvance.Cell.xi start).symm
  · exact x.trans (congrArg E1M1PathAdvance.Cell.mapX start).symm
  · exact regs.2.trans (congrArg E1M1PathAdvance.Cell.count start).symm

/-- The authenticated firing prefix now performs its first grid advance from
the complete production-initialized numeric state. This is one cell, not a
proof of the enclosing traversal loop or its future capacity invariant. -/
theorem execution (room : c.ids.length+nodes.length≤128)
    (world : Collision.Scene) (dimension : world.grid.width=w)
    (ids : world.links[Collision.pathCellIndex (path thing angle ox oy).startBlockX
      (path thing angle ox oy).startBlockY w]?=some (nodes.map E1M1ThingList.Node.id).toArray)
    (scene : ∀ node∈nodes, world.things[node.id]?=some node.target) (f : Option Flags) :
    let out := E1M1FiringAdvance.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes
    (∃ steps≤427+281*c.ids.length+230*nodes.length,
      X86CodeMemory.Prefix FloorCaller.cm E1M1FiringAdvance.program [] steps
        ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ out) ∧
    out.core.regs 4=s.regs 4-(112#32) ∧
    E1M1PathAdvance.observe out.core=E1M1PathAdvance.step (initial (path thing angle ox oy) xout yout) ∧
    out.pc=E1M1PathAdvance.nextPc (initial (path thing angle ox oy) xout yout) := by
  have before := before_observe gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d locals room world.things scene
  obtain ⟨run,sp,step,next⟩ := E1M1FiringAdvance.execution gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d room world dimension ids scene f
  rw [before] at step next
  exact ⟨run,sp,step,next⟩
end Firing

/-- The initialized axis fragment uses the same signed/wrapping operations as
production Path.pathTraverse, with the original X-first tie ordering. -/
theorem production_axis (p : Collision.PathStart) (xout yout : Int32 × Fixed × Fixed) :
    let xi := Collision.pathFirstIntercept p.x1 yout.2.1 yout.2.2
    let yi := Collision.pathFirstIntercept p.y1 xout.2.1 xout.2.2
    let out := E1M1PathAdvance.productionAxis p.startBlockX p.startBlockY xi yi
      xout.1 yout.1 yout.2.2 xout.2.2
    E1M1PathAdvance.numeric (E1M1PathAdvance.axis (initial p xout yout))=
      (out.1.toBitVec,out.2.1.toBitVec,out.2.2.1.raw.toBitVec,out.2.2.2.raw.toBitVec) :=
  E1M1PathAdvance.production_axis _ _ _ _ _ _ _ _ _ _ _
end Doom.Proofs.E1M1FiringGridState
