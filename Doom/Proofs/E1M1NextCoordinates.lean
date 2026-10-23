import Doom.Proofs.E1M1FiringNextThings
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1NextCoordinates
open Verification X86 X86Memory X86Control BlockSummary
open E1M1ScanGeometry (path)
open E1M1ScanContracts (LineData)
open E1M1FiringGridState (initial)
attribute [local irreducible] load32

open E1M1ScanContracts (candidates)
open E1M1NextCallbackReady (Ready)
section Scan
variable (s : X86Memory.State) (sp cursor lines : Word) (objects : Nat → Word)
    (trace : Collision.Divline) (c : E1M1PathMap.Cell) (data : Nat → LineData)
    (stack : s.regs 4=sp-(124#32)) (list : s.regs 2=cursor)
    (items : E1M1PathMapLookup.ScanWords s lines c)
    (ids : ∀ i : Fin c.ids.length, c.ids[i.val]<475)
    (ready : Ready s lines trace c data)
    (layout : E1M1ScanContracts.Layout sp cursor lines c.ids.length (candidates trace lines c.ids data))
include stack list items ids ready layout

/-- Existing storage separation protects both coordinate spill slots throughout
all remaining line callbacks, including appending to a mixed hit array. -/
theorem scan_coordinate (f : Option Flags) (r : Collision.PathResult)
    (tracked : OriginalLineCollection.Tracks s 0x2ba20 (E1M1ThingFinish.resolve lines objects) r.collected c.ids.length)
    (axis : Bool) :
    (E1M1NextLineScan.result s lines trace c data f r).1.core.regs (OriginalLineCoordinates.register axis)=
      s.regs (OriginalLineCoordinates.register axis) := by
  let contract := E1M1NextLineScan.initial s sp cursor lines objects trace c data stack list items ids ready layout
  exact OriginalLineCoordinates.finished_coordinate s c.ids.length 0x2ba20
    (E1M1ThingFinish.resolve lines objects) contract r f tracked
    (fun j _ _ => E1M1ScanContracts.candidate_continues trace lines c.ids[j]! (data j)) axis
end Scan

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


variable (room : c.ids.length+nodes.length≤128)
    (world : Collision.Scene) (dimension : world.grid.width=w)
    (ids : world.links[Collision.pathCellIndex (path thing angle ox oy).startBlockX
      (path thing angle ox oy).startBlockY w]?=some (nodes.map E1M1ThingList.Node.id).toArray)
    (scene : ∀ node∈nodes, world.things[node.id]?=some node.target)
include room dimension ids scene

variable (locals : E1M1GridLocals.Safe (s.regs 4) lines)
include locals

/-- The real grid step supplies the coordinates; the next lookup and duplicate
skip preserve them. No reached-state coordinate hypothesis is used. -/
theorem suffix_coordinates (x y : Int32)
    (mapX : (E1M1PathAdvance.step (initial (path thing angle ox oy) xout yout)).mapX=x.toBitVec)
    (mapY : (E1M1PathAdvance.step (initial (path thing angle ox oy) xout yout)).mapY=y.toBitVec) :
    let start := E1M1FiringNextSuffix.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes
    start.core.regs 6=x.toBitVec ∧ start.core.regs 1=y.toBitVec := by
  have obs := E1M1FiringGridState.before_observe gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d locals room world.things scene
  have advanced := (E1M1PathAdvance.result_observe (E1M1FiringCellReturn.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes).core).1
  rw [obs] at advanced
  have retained (axis : Bool) :
      (E1M1FiringNextSuffix.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes).core.regs (OriginalLineCoordinates.register axis)=
      (E1M1NextCellMemory.advanced (E1M1FiringCellReturn.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes).core).regs (OriginalLineCoordinates.register axis) :=
    (OriginalLineCoordinates.visit_coordinate _ axis).trans (E1M1ThingCoordinates.caller_coordinate _ axis)
  exact ⟨(retained true).trans ((congrArg E1M1PathAdvance.Cell.mapX advanced).trans mapX),
    (retained false).trans ((congrArg E1M1PathAdvance.Cell.mapY advanced).trans mapY)⟩
end Firing
end Doom.Proofs.E1M1NextCoordinates
