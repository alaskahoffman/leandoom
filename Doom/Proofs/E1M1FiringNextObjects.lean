import Doom.Proofs.E1M1NextObjectTraversal
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1FiringNextObjects
open Verification X86 X86Memory X86Control BlockSummary
open E1M1ScanGeometry (path)
open E1M1ScanContracts (LineData)
open E1M1ThingListInputs (before)
open E1M1FiringGridState (initial)
open E1M1FiringLineVisits (seenAfter)
open E1M1FiringVisitedNext (TailSafe)
open OriginalLineVisits (Represents stamp)
attribute [local irreducible] load32 Collision.pathFirstIntercept

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



variable (stamps : E1M1ScanContracts.Stamps (s.regs 4) lines)
    (epochBefore : E1M1ScanMemory.BeforeInit gun s (0x13580#32))
    (epochAfter : E1M1PathMapSetup.StackSafe (s.regs 4-(112#32)) (0x13580#32))
    (stampSetup : ∀ j<475, E1M1PathMapFiring.Safe gun s (stamp lines j))
    (fresh : ∀ j<475, load32 s.memory (stamp lines j)≠load32 s.memory 0x13580+1)
    (epochTail : TailSafe (s.regs 4) (0x13580#32))
    (stampTail : ∀ j<475, TailSafe (s.regs 4) (stamp lines j))
include stamps epochBefore epochAfter stampSetup fresh epochTail stampTail

variable (room : c.ids.length+nodes.length≤128)
    (world : Collision.Scene) (dimension : world.grid.width=w)
    (ids : world.links[Collision.pathCellIndex (path thing angle ox oy).startBlockX
      (path thing angle ox oy).startBlockY w]?=some (nodes.map E1M1ThingList.Node.id).toArray)
    (scene : ∀ node∈nodes, world.things[node.id]?=some node.target)
include room dimension ids scene

variable (locals : E1M1GridLocals.Safe (s.regs 4) lines)
include locals

open E1M1NextCallbackReady (Ready)
open E1M1ScanGeometry (linePointer)
/-- Continuous firing now executes the second cell's entire object list and
returns to its caller. Both cells use the production scene's linked-ID order;
all second-list inputs derive from initial data, and the initial candidate
budget covers both line scans and both object scans. -/
theorem execution (f : Option Flags)
    (globalsSafe : ∀ a∈[(0x2c0fc#32),0x2c110,0x2c100,0x2c10c,0x2c120], E1M1FiringMapState.Safe (s.regs 4) lines a)
    (imageSafe : ∀ i<words.size, E1M1FiringMapState.Safe (s.regs 4) lines (base+BitVec.ofNat 32 (2*i)))
    (notEnd : E1M1PathAdvance.ended (initial (path thing angle ox oy) xout yout)=false)
    (x y : Int32)
    (mapX : (E1M1PathAdvance.step (initial (path thing angle ox oy) xout yout)).mapX=x.toBitVec)
    (mapY : (E1M1PathAdvance.step (initial (path thing angle ox oy) xout yout)).mapY=y.toBitVec)
    (nextCell : E1M1PathMap.Cell) (inMap : Collision.pathCellInside x y w h=true)
    (valid : nextCell.Valid words) (selectedCell : words[4+Collision.pathCellIndex x y w]?=some nextCell.offset)
    (nextData : Nat → LineData)
    (nextInput : E1M1NextCallbackReady.Data gun s lines (path thing angle ox oy).trace
      (E1M1DuplicateSuffix.tailCell nextCell) nextData)
    (traceSafe : ∀ a∈E1M1ThingGeometry.traceReads, E1M1FiringMapState.Safe (s.regs 4) lines a)
    (activeSafe : E1M1FiringMapState.Safe (s.regs 4) lines (0x2c024#32))
    (nextLayout : E1M1ScanContracts.Layout (s.regs 4) (base+BitVec.ofNat 32 (2*(nextCell.offset+1)))
      lines nextCell.ids.tail.length
      (E1M1ScanContracts.candidates (path thing angle ox oy).trace lines nextCell.ids.tail nextData))
    (nextNodes : List E1M1ThingList.Node)
    (headValue : load32 s.memory (links+(BitVec.ofNat 32 (Collision.pathCellIndex x y w) <<< 2))=(E1M1ThingList.head nextNodes))
    (nextSetup : ∀ a∈[(0x2c0f8#32),links+(BitVec.ofNat 32 (Collision.pathCellIndex x y w) <<< 2)],
      E1M1PathMapFiring.Safe gun s a)
    (nextSafe : ∀ a∈[(0x2c0f8#32),links+(BitVec.ofNat 32 (Collision.pathCellIndex x y w) <<< 2)],
      E1M1FiringMapState.Safe (s.regs 4) lines a)
    (nextObjects : E1M1ThingListInputs.Data gun s lines (path thing angle ox oy).trace objects nextNodes)
    (nextObjectSafe : ∀ node∈nextNodes, ∀ a∈E1M1ThingGeometry.objectReads node.pointer,
      E1M1FiringMapState.Safe (s.regs 4) lines a)
    (nextLinkSafe : ∀ node∈nextNodes,
      E1M1FiringMapState.Safe (s.regs 4) lines (node.pointer+(44#32)))
    (totalBudget : c.ids.length+nodes.length+nextCell.ids.tail.length+nextNodes.length≤128)
    (nextIds : world.links[Collision.pathCellIndex x y w]?=some (nextNodes.map E1M1ThingList.Node.id).toArray)
    (nextScene : ∀ node∈nextNodes, world.things[node.id]?=some node.target) :
    let start := E1M1FiringNextSuffix.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes
    ∃ after, E1M1FiringThings.sceneCell (path thing angle ox oy).trace world
      (path thing angle ox oy).startBlockX (path thing angle ox oy).startBlockY
      (before gun s weapon actor thing angle ox oy xout yout base lines words c w h data input)=.ok after ∧
    let scan := E1M1NextLineScan.result start.core lines (path thing angle ox oy).trace
      (E1M1DuplicateSuffix.tailCell nextCell) nextData start.flags after
    let entry := OriginalThingEntry.result (E1M1FiringNextThings.called scan.1).core
    let out := E1M1NextObjectTraversal.result entry nextNodes
    (∃ steps≤505+281*(c.ids.length+nextCell.ids.tail.length)+230*(nodes.length+nextNodes.length),
      X86CodeMemory.Prefix FloorCaller.cm E1M1FiringAdvance.program [] steps
        ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ out) ∧
    out.core.regs 0=(1#32) ∧ out.core.regs 4=s.regs 4-(112#32) ∧ out.pc=0x2cab1 ∧
    (∃ final, E1M1FiringThings.sceneCell (path thing angle ox oy).trace world x y scan.2=.ok final ∧
      OriginalLineCollection.Tracks out.core 0x2ba20 (E1M1ThingFinish.resolve lines objects) final.collected 0) ∧
    Represents out.core.memory lines (load32 s.memory 0x13580+1)
      (OriginalLineVisits.markPrefix
        (E1M1ScanContracts.candidates (path thing angle ox oy).trace lines nextCell.ids.tail nextData)
        nextCell.ids.tail.length 0 (seenAfter (path thing angle ox oy).trace lines c data)) := by
  obtain ⟨after,production,⟨n,hn,prior⟩,_,_,_,empty,nonempty,hits,visits,_,capacity,ready⟩ :=
    E1M1FiringNextObjectImage.execution gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d stamps epochBefore epochAfter stampSetup fresh epochTail stampTail room world dimension ids scene locals f globalsSafe imageSafe notEnd x y mapX mapY nextCell inMap valid selectedCell nextData nextInput traceSafe activeSafe nextLayout (by omega)
      nextNodes headValue nextSetup nextSafe nextObjects nextObjectSafe nextLinkSafe totalBudget
  obtain ⟨⟨m,hm,run⟩,success,stack,pc,⟨final,collected,tracked⟩,history⟩ :=
    E1M1NextObjectTraversal.execution _ (s.regs 4) lines (load32 s.memory 0x13580+1) objects
      (path thing angle ox oy).trace nextNodes _ _ nextObjects.nonzero empty nonempty ready hits capacity visits
      epochTail.objects (fun j hj => (stampTail j (by
        simpa only [OriginalLineVisitedRun.mark_size,E1M1FiringLineVisits.seen_size] using hj)).objects)
  refine ⟨after,production,⟨n+m,by omega,E1M1PspriteStep.prefix_trans prior run⟩,
    success,stack,pc,⟨final,?_,tracked⟩,history⟩
  rw [E1M1FiringThings.scene_cell _ world x y w nextNodes _ dimension nextIds,
    E1M1ThingTraversal.objectCell_collect _ world.things nextNodes _ nextScene]
  exact collected
end Firing
end Doom.Proofs.E1M1FiringNextObjects
