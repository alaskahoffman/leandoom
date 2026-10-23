import Doom.Proofs.OriginalLineInterceptRegister
import Doom.Proofs.E1M1ThingGridRegisters
import Doom.Proofs.E1M1FiringAdvance
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1FiringGridRegisters
open Verification X86 X86Memory X86Control BlockSummary
open E1M1ScanMemory (firstScan)
open E1M1ScanGeometry (path)
open E1M1ScanContracts (LineData)
open E1M1ThingListInputs (boundary before)
open E1M1ThingGridRegisters (register)

theorem caller_intercept (s : X86Memory.State) :
    (E1M1PathMapCaller.scan s).core.regs 5=s.regs 5 := by
  have guarded (t : X86Memory.State) :
      (OriginalLineBounds.guarded t).core.regs 5=t.regs 5 := by
    unfold OriginalLineBounds.guarded
    split <;> (try split) <;> (try split) <;>
      simp [OriginalLineBounds.loaded,put,write]
  have returned (t : X86Memory.State) :
      (OriginalLineBounds.returned t).core.regs 5=t.regs 5 := by
    simp [OriginalLineBounds.returned,OriginalLineBounds.r3,OriginalLineBounds.r2,
      OriginalLineBounds.r1,put,write]
  have bounds (t : X86Memory.State) :
      (OriginalLineBounds.result t).core.regs 5=t.regs 5 := by
    unfold OriginalLineBounds.result
    split <;> (try rw [returned]) <;> rw [guarded] <;>
      simp [OriginalLineBounds.entry,OriginalLineBounds.e2,OriginalLineBounds.e1,
        X86Routine.pushWord,put,write]
  have lookup (t : X86Memory.State) :
      (OriginalLineCell.lookup t).core.regs 5=t.regs 5 := by
    simp [OriginalLineCell.lookup,OriginalLineCell.l7,OriginalLineCell.l6,
      OriginalLineCell.l5,OriginalLineCell.l4,OriginalLineCell.l3,OriginalLineCell.l2,
      OriginalLineCell.l1,put,write]
  unfold E1M1PathMapCaller.scan E1M1PathMapBounds.scanStart
  rw [lookup,bounds]
  simp [E1M1PathMapCaller.call,OriginalPathCell.called,OriginalPathCell.c3,
    OriginalPathCell.c2,OriginalPathCell.c1,X86Routine.pushWord,put,write]
section Firing
variable (gun : Fire.Gun) (s : X86Memory.State) (weapon : Weapon.Context)
    (actor : Word) (thing : Collision.SolidThing) (angle : Angle) (ox oy : Fixed)
    (xout yout : Int32 × Fixed × Fixed) (base lines : Word) (words : Array Nat)
    (c : E1M1PathMap.Cell) (w h : Nat) (data : Nat → LineData)
    (input : E1M1FiringScan.Inputs gun s weapon actor thing angle ox oy xout yout base lines words c w h data)
include input


/-- Path setup computes the X intercept and initializes the grid budget counter. -/
theorem initialized :
    (E1M1PathGridSetup.firstGrid gun s).core.regs 5=
      (Collision.pathFirstIntercept (path thing angle ox oy).x1 yout.2.1 yout.2.2).raw.toBitVec ∧
    (E1M1PathGridSetup.firstGrid gun s).core.regs 7=0 := by
  have geometry := E1M1AimGeometry.path_inputs _ thing angle _ ox oy
    (E1M1FiringGeometry.query_geometry gun s actor thing angle ox oy input.geometry)
  have grid := (E1M1PathGridSetup.grid_observation_from_init _ ox oy _ _ _ _ geometry
    xout yout input.okX input.okY).2
  exact ⟨grid.xIntercept,grid.counter⟩

set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] Collision.SolidThing.attackEndpoint

/-- EBP is saved and restored on every line-callback branch. -/
theorem scan_intercept :
    (E1M1ScanReturn.finished gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).1.core.regs
      5=(firstScan gun s).core.regs 5 := by
  let contract := E1M1FiringScan.initial gun s weapon actor thing angle ox oy xout yout base lines words c w h data input
  have run := E1M1FiringGeometry.first_scan_execution gun s none weapon input.firing actor thing angle ox oy input.geometry
    xout yout input.okX input.okY base lines words c w h input.map input.cursorSafe input.inside input.valid input.selected
  have keeps : ∀ i<c.ids.length, (contract.candidates i).crosses=true → (contract.candidates i).Continues := by
    intro i _ _
    dsimp only [contract,E1M1FiringScan.initial,E1M1ScanContracts.initial]
    exact E1M1ScanContracts.candidate_continues (path thing angle ox oy).trace lines c.ids[i]! (data i)
  exact OriginalLineInterceptRegister.finished_intercept (firstScan gun s).core c.ids.length 0x2ba20
    (E1M1PathMap.resolve lines) contract {trace := (path thing angle ox oy).trace} (firstScan gun s).flags run.2.2 keeps

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


omit flag lookupSafe global selected d in
/-- Both numeric registers at the object boundary come from initialization,
not assumptions about the reached machine state. -/
theorem boundary_register (x : Bool) :
    (boundary gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).core.regs (register x)=
      (if x then 0 else (Collision.pathFirstIntercept (path thing angle ox oy).x1 yout.2.1 yout.2.2).raw.toBitVec) := by
  change (OriginalThingEntry.result (E1M1ThingGate.called gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).core).core.regs (register x)=_
  rw [E1M1ThingGridRegisters.lookup_register]
  have init := initialized gun s weapon actor thing angle ox oy xout yout base lines words c w h data input
  have called : (E1M1ThingGate.called gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).core.regs (register x)=
      (E1M1ScanReturn.finished gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).1.core.regs (register x) := by
    cases x <;> simp [E1M1ThingGate.called,E1M1ThingGate.gate,OriginalPathCell.resumed,
      OriginalPathCell.called,OriginalPathCell.c3,OriginalPathCell.c2,OriginalPathCell.c1,
      X86Routine.pushWord,register,put,write]
  rw [called]
  cases x
  · exact (scan_intercept gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).trans
      ((caller_intercept (E1M1PathGridSetup.firstGrid gun s).core).trans init.1)
  · exact (E1M1ScanReturn.parent_return gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns).2.2.1.trans init.2

theorem firing_register (room : c.ids.length+nodes.length≤128) (x : Bool) :
    (E1M1FiringThings.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes).core.regs (register x)=
      (if x then 0 else (Collision.pathFirstIntercept (path thing angle ox oy).x1 yout.2.1 yout.2.2).raw.toBitVec) := by
  have old := boundary_register gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns x
  cases nodes with
  | nil => exact old
  | cons node rest =>
    have present : E1M1ThingList.head (node::rest)≠(0#32) := d.nonzero node (by simp)
    obtain ⟨_,pc,_,_,nonempty,tracked⟩ := E1M1ThingEntry.firing_lookup gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links
      (E1M1ThingList.head (node::rest)) lookupSafe global selected none
    have converted := E1M1ThingFinish.relabel (boundary gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).core 0x2ba20 lines objects
      (before gun s weapon actor thing angle ox oy xout yout base lines words c w h data input) (E1M1ThingListInputs.all_lines gun s weapon actor thing angle ox oy xout yout base lines words c w h data input) tracked
    have encoded := E1M1FiringThings.image gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links (node::rest) lookupSafe global selected objects d present
    have separated := E1M1FiringThings.layout gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links (node::rest) lookupSafe global selected objects d present
    have capacity := E1M1ThingListInputs.capacity gun s weapon actor thing angle ox oy xout yout base lines words c w h data input (node::rest) room
    exact (E1M1ThingGridRegisters.traversal_register (boundary gun s weapon actor thing angle ox oy xout yout base lines words c w h data input) (path thing angle ox oy).trace
      (E1M1ThingFinish.resolve lines objects) (node::rest) (0x2cab1#32) separated encoded
      (nonempty present).1 (by simpa only [boundary,if_neg present] using pc)
      (before gun s weapon actor thing angle ox oy xout yout base lines words c w h data input) converted capacity x).trans old

/-- The first grid advance starts with the initialized intercept and zero count. -/
theorem before_advance (room : c.ids.length+nodes.length≤128) :
    let out := E1M1FiringCellReturn.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes
    out.core.regs 5=(Collision.pathFirstIntercept (path thing angle ox oy).x1 yout.2.1 yout.2.2).raw.toBitVec ∧
    out.core.regs 7=0 := by
  exact ⟨firing_register gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d room false,
    firing_register gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d room true⟩


/-- Joined execution with initialized EBP and EDI. The first advancement either
ends at the current endpoint or starts another cell with count one; it cannot
exhaust the 64-cell budget. Stack-local initialization links remain separate. -/
theorem execution (room : c.ids.length+nodes.length≤128)
    (world : Collision.Scene) (dimension : world.grid.width=w)
    (ids : world.links[Collision.pathCellIndex (path thing angle ox oy).startBlockX
      (path thing angle ox oy).startBlockY w]?=some (nodes.map E1M1ThingList.Node.id).toArray)
    (scene : ∀ node∈nodes, world.things[node.id]?=some node.target) (f : Option Flags) :
    let before := E1M1FiringCellReturn.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes
    let out := E1M1FiringAdvance.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes
    (∃ steps≤427+281*c.ids.length+230*nodes.length,
      X86CodeMemory.Prefix FloorCaller.cm E1M1FiringAdvance.program [] steps
        ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ out) ∧
    out.core.regs 4=s.regs 4-(112#32) ∧
    (E1M1PathAdvance.observe before.core).xi=
      (Collision.pathFirstIntercept (path thing angle ox oy).x1 yout.2.1 yout.2.2).raw.toBitVec ∧
    (E1M1PathAdvance.observe before.core).count=0 ∧
    E1M1PathAdvance.observe out.core=E1M1PathAdvance.step (E1M1PathAdvance.observe before.core) ∧
    out.core.regs 7=(if E1M1PathAdvance.ended (E1M1PathAdvance.observe before.core) then 0 else 1) ∧
    out.pc=(if E1M1PathAdvance.ended (E1M1PathAdvance.observe before.core) then 0x2cafd else 0x2ca7f) := by
  have initialized := before_advance gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d room
  obtain ⟨run,sp,step,next⟩ := E1M1FiringAdvance.execution gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d room world dimension ids scene f
  refine ⟨run,sp,initialized.1,initialized.2,step,?_,?_⟩
  · have eq := congrArg E1M1PathAdvance.Cell.count step
    change _=(E1M1PathAdvance.step _).count at eq
    change (E1M1PathAdvance.observe (E1M1FiringAdvance.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes).core).count=_
    rw [eq]
    simp only [E1M1PathAdvance.step]
    split <;> simp_all only [E1M1PathAdvance.observe] <;> rfl
  · rw [next]
    simp only [E1M1PathAdvance.nextPc,E1M1PathAdvance.observe,initialized.2]
    split <;> rfl
end Firing
end Doom.Proofs.E1M1FiringGridRegisters
