import Doom.Proofs.E1M1ThingPreservation
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
namespace Doom.Proofs.E1M1FiringCellReturn
open Verification X86 X86Memory X86Control BlockSummary
open OriginalLineCoordinates (register)
open E1M1ScanMemory (firstScan)
open E1M1ScanGeometry (path)
open E1M1ScanContracts (LineData)
open E1M1ThingListInputs (boundary before)
abbrev program := E1M1FiringThings.program

/-- The caller's existing authenticated byte range is in the joined program. -/
theorem contains_cell (pc : Nat) (h : OriginalPathCell.program pc≠none) :
    program pc=OriginalPathCell.program pc := by
  have range : 0x2ca7f≤pc ∧ pc<0x2cab5 := by
    by_cases r : 0x2ca7f≤pc ∧ pc<0x2cab5
    · exact r
    · simp [OriginalPathCell.program,OriginalPathCell.bytesProgram,r] at h
  have all : ∀ i : Fin 54, program (0x2ca7f+i.val)=OriginalPathCell.program (0x2ca7f+i.val) := by decide
  have eq : 0x2ca7f+(pc-0x2ca7f)=pc := by omega
  simpa only [eq] using all ⟨pc-0x2ca7f,by omega⟩

/-- Execute the real TEST/JZ pair. The resulting state retains every register
and memory byte; only flags and control position change. -/
theorem success_test (s : X86Control.State) (pc : s.pc=0x2cab1)
    (success : s.core.regs 0=(1#32)) :
    X86CodeMemory.Prefix FloorCaller.cm program [] 2 s (OriginalPathCell.resumed false s.core) ∧
    (OriginalPathCell.resumed false s.core).pc=0x2cab5 ∧
    (OriginalPathCell.resumed false s.core).core=s.core := by
  have run := OriginalPathCell.resume_execution false s.core s.flags
  rw [show OriginalPathCell.returnPc false=0x2cab1 from rfl,OriginalPathXStep.at_pc _ _ pc] at run
  exact ⟨X86CodeMemory.lift_success (run.transfer program [] contains_cell (by simp)) FloorCaller.cm,
    by simp [OriginalPathCell.resumed,OriginalPathCell.skipPc,success],rfl⟩

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


omit returns flag lookupSafe global selected d in
/-- Coordinates are initialized by path setup and survive the line scan and
thing-iterator lookup, including its empty-list exit. -/
theorem boundary_coordinate (x : Bool) :
    (boundary gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).core.regs (register x)=
      (if x then (path thing angle ox oy).startBlockX else (path thing angle ox oy).startBlockY).toBitVec := by
  change (OriginalThingEntry.result (E1M1ThingGate.called gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).core).core.regs (register x)=_
  rw [E1M1ThingPreservation.lookup_coordinate]
  have first := E1M1ThingCoordinates.first_coordinates gun s weapon actor thing angle ox oy xout yout base lines words c w h data input
  have scanned := E1M1ThingCoordinates.scan_coordinate gun s weapon actor thing angle ox oy xout yout base lines words c w h data input x
  have called : (E1M1ThingGate.called gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).core.regs (register x)=
      (E1M1ScanReturn.finished gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).1.core.regs (register x) := by
    cases x <;> simp [E1M1ThingGate.called,E1M1ThingGate.gate,OriginalPathCell.resumed,
      OriginalPathCell.called,OriginalPathCell.c3,OriginalPathCell.c2,OriginalPathCell.c1,
      X86Routine.pushWord,register,put,write]
  exact called.trans (scanned.trans (by cases x <;> simp only [register,Bool.false_eq_true,↓reduceIte]; exact first.2; exact first.1))

/-- Both coordinates remain those of the selected cell after all its objects. -/
theorem firing_coordinate (room : c.ids.length+nodes.length≤128) (x : Bool) :
    (E1M1FiringThings.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes).core.regs (register x)=
      (if x then (path thing angle ox oy).startBlockX else (path thing angle ox oy).startBlockY).toBitVec := by
  have old := boundary_coordinate gun s weapon actor thing angle ox oy xout yout base lines words c w h data input x
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
    exact (E1M1ThingPreservation.traversal_coordinate (boundary gun s weapon actor thing angle ox oy xout yout base lines words c w h data input) (path thing angle ox oy).trace
      (E1M1ThingFinish.resolve lines objects) (node::rest) (0x2cab1#32) separated encoded
      (nonempty present).1 (by simpa only [boundary,if_neg present] using pc)
      (before gun s weapon actor thing angle ox oy xout yout base lines words c w h data input) converted capacity x).trans old

def result := OriginalPathCell.resumed false (E1M1FiringThings.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes).core

/-- Continuous execution from either post-sound weapon entry to the grid-step
boundary, with the selected cell's ordered hits and both coordinates intact. -/
theorem execution (room : c.ids.length+nodes.length≤128)
    (world : Collision.Scene) (dimension : world.grid.width=w)
    (ids : world.links[Collision.pathCellIndex (path thing angle ox oy).startBlockX
      (path thing angle ox oy).startBlockY w]?=some (nodes.map E1M1ThingList.Node.id).toArray)
    (scene : ∀ node∈nodes, world.things[node.id]?=some node.target) (f : Option Flags) :
    let out := result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes
    (∃ steps≤408+281*c.ids.length+230*nodes.length, X86CodeMemory.Prefix FloorCaller.cm program [] steps
      ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ out) ∧
    out.core.regs 0=(1#32) ∧ out.core.regs 4=s.regs 4-(112#32) ∧ out.pc=0x2cab5 ∧
    out.core.regs 6=(path thing angle ox oy).startBlockX.toBitVec ∧
    out.core.regs 1=(path thing angle ox oy).startBlockY.toBitVec ∧
    (∃ after, E1M1FiringThings.sceneCell (path thing angle ox oy).trace world (path thing angle ox oy).startBlockX
      (path thing angle ox oy).startBlockY (before gun s weapon actor thing angle ox oy xout yout base lines words c w h data input)=.ok after ∧
      OriginalLineCollection.Tracks out.core 0x2ba20 (E1M1ThingFinish.resolve lines objects) after.collected 0) := by
  obtain ⟨⟨n,hn,prior⟩,success,sp,pc,after,production,tracked⟩ :=
    E1M1FiringThings.execution_scene gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d room world dimension ids scene f
  have tail := success_test (E1M1FiringThings.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes) pc success
  exact ⟨⟨n+2,by omega,E1M1PspriteStep.prefix_trans prior tail.1⟩,success,sp,tail.2.1,
    firing_coordinate gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d room true,firing_coordinate gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d room false,after,production,tracked⟩
end Firing
end Doom.Proofs.E1M1FiringCellReturn
