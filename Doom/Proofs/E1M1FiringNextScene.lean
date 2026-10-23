import Doom.Proofs.E1M1FiringSceneData
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1FiringNextScene
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
/-- The continuous two-cell execution retains callback data for any protected
future selection represented at firing entry, as well as the currently scanned
selection. Temporary stack words are rebuilt separately at real iterator entry. -/
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
    let returned := E1M1NextObjectTraversal.result entry nextNodes
    let grid := E1M1PathAdvance.step (initial (path thing angle ox oy) xout yout)
    let out := E1M1CellBoundaryAdvance.result returned
    (∃ steps≤526+281*(c.ids.length+nextCell.ids.tail.length)+230*(nodes.length+nextNodes.length),
      X86CodeMemory.Prefix FloorCaller.cm E1M1FiringAdvance.program [] steps
        ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ out) ∧
    out.core.regs 4=s.regs 4-(112#32) ∧
    E1M1PathAdvance.observe returned.core=grid ∧
    E1M1PathAdvance.observe out.core=E1M1PathAdvance.step grid ∧ out.pc=E1M1PathAdvance.nextPc grid ∧
    (∃ final, E1M1FiringThings.sceneCell (path thing angle ox oy).trace world x y scan.2=.ok final ∧
      final.collected.size≤c.ids.length+nodes.length+nextCell.ids.tail.length+nextNodes.length ∧
      OriginalLineCollection.Tracks out.core 0x2ba20 (E1M1ThingFinish.resolve lines objects) final.collected (128-(c.ids.length+nodes.length+nextCell.ids.tail.length+nextNodes.length))) ∧
    Represents out.core.memory lines (load32 s.memory 0x13580+1)
      (OriginalLineVisits.markPrefix
        (E1M1ScanContracts.candidates (path thing angle ox oy).trace lines nextCell.ids.tail nextData)
        nextCell.ids.tail.length 0 (seenAfter (path thing angle ox oy).trace lines c data)) ∧
    (∀ a, E1M1ThingVisit.ReadSafe (s.regs 4-(120#32)) a →
      Apart a (s.regs 4-(112#32)+(44#32)) → load32 out.core.memory a=load32 entry.core.memory a) ∧
    E1M1CellMapInvariant.Image out.core.memory (s.regs 4) base lines words w h ∧
    E1M1CellMapInvariant.Frame (s.regs 4) lines
      (E1M1FiringCellReturn.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes).core.memory out.core.memory ∧
    E1M1CellSceneInvariant.Image out.core.memory lines (path thing angle ox oy).trace
      (E1M1DuplicateSuffix.tailCell nextCell) nextData nextNodes ∧
    (∀ (cell : E1M1PathMap.Cell) (lineData : Nat → LineData),
      E1M1NextCallbackReady.Data gun s lines (path thing angle ox oy).trace cell lineData →
      ∀ (objectNodes : List E1M1ThingList.Node),
      E1M1ThingListInputs.Data gun s lines (path thing angle ox oy).trace objects objectNodes →
      (∀ node∈objectNodes, ∀ a∈E1M1ThingGeometry.objectReads node.pointer,
        E1M1FiringMapState.Safe (s.regs 4) lines a) →
      (∀ node∈objectNodes, E1M1FiringMapState.Safe (s.regs 4) lines (node.pointer+(44#32))) →
      E1M1CellSceneInvariant.Image out.core.memory lines (path thing angle ox oy).trace cell lineData objectNodes ∧
      E1M1CellSceneInvariant.Protected (s.regs 4) lines cell lineData objectNodes ∧
      E1M1CellSceneInvariant.Contracts (s.regs 4) lines (path thing angle ox oy).trace cell lineData objects objectNodes) := by
  obtain ⟨after,production,run,stack,numeric,advanced,pc,hits,history,frame,map,complete⟩ :=
    E1M1FiringNextMap.execution gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d stamps epochBefore epochAfter stampSetup fresh epochTail stampTail room world dimension ids scene locals f globalsSafe imageSafe notEnd x y mapX mapY nextCell inMap valid selectedCell nextData nextInput traceSafe activeSafe nextLayout nextNodes headValue nextSetup nextSafe nextObjects nextObjectSafe nextLinkSafe totalBudget nextIds nextScene
  let start := E1M1FiringNextSuffix.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes
  let scan := E1M1NextLineScan.result start.core lines (path thing angle ox oy).trace
    (E1M1DuplicateSuffix.tailCell nextCell) nextData start.flags after
  let out := E1M1CellBoundaryAdvance.result (E1M1NextObjectTraversal.result
    (OriginalThingEntry.result (E1M1FiringNextThings.called scan.1).core) nextNodes)
  have preserve : ∀ (cell : E1M1PathMap.Cell) (lineData : Nat → LineData),
      E1M1NextCallbackReady.Data gun s lines (path thing angle ox oy).trace cell lineData →
      ∀ (objectNodes : List E1M1ThingList.Node),
      E1M1ThingListInputs.Data gun s lines (path thing angle ox oy).trace objects objectNodes →
      (∀ node∈objectNodes, ∀ a∈E1M1ThingGeometry.objectReads node.pointer,
        E1M1FiringMapState.Safe (s.regs 4) lines a) →
      (∀ node∈objectNodes, E1M1FiringMapState.Safe (s.regs 4) lines (node.pointer+(44#32))) →
      E1M1CellSceneInvariant.Image out.core.memory lines (path thing angle ox oy).trace cell lineData objectNodes ∧
      E1M1CellSceneInvariant.Protected (s.regs 4) lines cell lineData objectNodes ∧
      E1M1CellSceneInvariant.Contracts (s.regs 4) lines (path thing angle ox oy).trace cell lineData objects objectNodes := by
    intro cell lineData lineInput objectNodes objectInput objectSafe linkSafe
    have prepared := E1M1FiringSceneData.prepared gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d room world dimension ids scene
      cell lineData lineInput objectNodes objectInput objectSafe linkSafe traceSafe activeSafe
    exact ⟨E1M1CellSceneInvariant.transport _ _ (s.regs 4) lines (path thing angle ox oy).trace
      cell lineData objectNodes prepared.1 prepared.2.1 complete,prepared.2⟩
  exact ⟨after,production,run,stack,numeric,advanced,pc,hits,history,frame,map,complete,
    (preserve _ nextData nextInput nextNodes nextObjects nextObjectSafe nextLinkSafe).1,preserve⟩
end Firing
end Doom.Proofs.E1M1FiringNextScene
