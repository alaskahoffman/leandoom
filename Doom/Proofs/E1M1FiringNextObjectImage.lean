import Doom.Proofs.E1M1NextObjectMemory
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1FiringNextObjectImage
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
/-- Derive the second list image and capacity from firing-entry data and the
initialized trace, retaining the same continuous prefix and its mixed history.
The head identifies this exact finite node chain; no reached image is assumed. -/
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
    (budget : c.ids.length+nodes.length+nextCell.ids.tail.length≤128)
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
    (totalBudget : c.ids.length+nodes.length+nextCell.ids.tail.length+nextNodes.length≤128) :
    let start := E1M1FiringNextSuffix.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes
    ∃ after, E1M1FiringThings.sceneCell (path thing angle ox oy).trace world
      (path thing angle ox oy).startBlockX (path thing angle ox oy).startBlockY
      (before gun s weapon actor thing angle ox oy xout yout base lines words c w h data input)=.ok after ∧
    let scan := E1M1NextLineScan.result start.core lines (path thing angle ox oy).trace
      (E1M1DuplicateSuffix.tailCell nextCell) nextData start.flags after
    let call := E1M1FiringNextThings.called scan.1
    let out := OriginalThingEntry.result call.core
    (∃ steps≤502+281*(c.ids.length+nextCell.ids.tail.length)+230*nodes.length,
      X86CodeMemory.Prefix FloorCaller.cm E1M1FiringAdvance.program [] steps
        ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ out) ∧
    call.core.regs 0=x.toBitVec ∧ call.core.regs 2=y.toBitVec ∧
    OriginalThingEntry.head (OriginalThingEntry.guarded (OriginalThingEntry.entry call.core)).core=(E1M1ThingList.head nextNodes) ∧
    ((E1M1ThingList.head nextNodes)=0 → out.core.regs 0=(1#32) ∧ out.core.regs 4=s.regs 4-(112#32) ∧ out.pc=0x2cab1) ∧
    ((E1M1ThingList.head nextNodes)≠0 → out.pc=0x2c5d2 ∧ out.core.regs 2=(E1M1ThingList.head nextNodes) ∧ out.core.regs 4=s.regs 4-(120#32) ∧
      load32 out.core.memory (out.core.regs 4)=(0x2c720#32)) ∧
    OriginalLineCollection.Tracks out.core 0x2ba20 (E1M1ThingFinish.resolve lines objects) scan.2.collected 0 ∧
    Represents out.core.memory lines (load32 s.memory 0x13580+1)
      (OriginalLineVisits.markPrefix
        (E1M1ScanContracts.candidates (path thing angle ox oy).trace lines nextCell.ids.tail nextData)
        nextCell.ids.tail.length 0 (seenAfter (path thing angle ox oy).trace lines c data)) ∧
    (∃ added : List Collision.Intercept, scan.2.collected.toList=after.collected.toList++added) ∧
    scan.2.collected.size+nextNodes.length≤128 ∧
    ((E1M1ThingList.head nextNodes)≠0 →
      E1M1ThingList.Image out.core.memory (out.core.regs 4) (path thing angle ox oy).trace nextNodes (0x2cab1#32) ∧
      E1M1ThingList.Layout (out.core.regs 4) (path thing angle ox oy).trace (E1M1ThingFinish.resolve lines objects) nextNodes) := by
  obtain ⟨after,production,prior,cx,cy,head,empty,nonempty,hits,visits,ordered⟩ :=
    E1M1FiringNextLookup.execution gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d stamps epochBefore epochAfter stampSetup fresh epochTail stampTail room world dimension ids scene locals f globalsSafe imageSafe notEnd x y mapX mapY nextCell inMap valid selectedCell nextData nextInput traceSafe activeSafe nextLayout budget
      (E1M1ThingList.head nextNodes) headValue nextSetup nextSafe
  obtain ⟨_,items,pc,sp,mem,cursor,⟨sameAfter,sameProduction,bound,tracked⟩,_,ready⟩ :=
    E1M1FiringNextGeometry.execution gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d stamps epochBefore epochAfter stampSetup fresh epochTail stampTail room world dimension ids scene locals f globalsSafe imageSafe notEnd x y mapX mapY nextCell inMap valid selectedCell nextData nextInput traceSafe activeSafe
  have same : sameAfter=after := Except.ok.inj (sameProduction.symm.trans production)
  subst sameAfter
  have entry := E1M1NextCursor.firing_cursor gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d room world dimension ids scene locals globalsSafe imageSafe x y mapX mapY nextCell inMap valid selectedCell
  have address : (E1M1FiringNextSuffix.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes).core.regs 2=base+BitVec.ofNat 32 (2*(nextCell.offset+1)) := by
    rw [cursor,entry,E1M1NextCursor.tail_address]
  have capacity := E1M1CellCapacity.suffix_reserve _ _ _ _ (c.ids.length+nodes.length)
    nextCell.ids.tail.length tracked budget
  let scan := E1M1NextLineScan.result (E1M1FiringNextSuffix.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes).core lines (path thing angle ox oy).trace
    (E1M1DuplicateSuffix.tailCell nextCell) nextData (E1M1FiringNextSuffix.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes).flags after
  let out := OriginalThingEntry.result (E1M1FiringNextThings.called scan.1).core
  have tailRead (a : Word) (safe : E1M1FiringMapState.Safe (s.regs 4) lines a) :
      load32 out.core.memory a=load32 (E1M1FiringNextScan.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes).core.memory a := by
    have keep := E1M1NextObjectMemory.read_word _ (s.regs 4) _ lines objects (path thing angle ox oy).trace (E1M1DuplicateSuffix.tailCell nextCell) nextData sp address items (E1M1NextCursor.tail_ids nextCell words valid) ready nextLayout returns (E1M1FiringNextSuffix.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes).flags after capacity a safe
    rw [mem] at keep
    exact keep
  have read (a : Word) (setup : E1M1PathMapFiring.Safe gun s a)
      (safe : E1M1FiringMapState.Safe (s.regs 4) lines a) : load32 out.core.memory a=load32 s.memory a :=
    (tailRead a safe).trans (E1M1NextCallbackMemory.firing_frame gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d room world dimension ids scene a setup safe)
  have traceWords :
      (load32 out.core.memory 0x2ba10,load32 out.core.memory 0x2ba14,load32 out.core.memory 0x2ba18,load32 out.core.memory 0x2ba1c)=
      ((path thing angle ox oy).trace.x.raw.toBitVec,(path thing angle ox oy).trace.y.raw.toBitVec,
        (path thing angle ox oy).trace.dx.raw.toBitVec,(path thing angle ox oy).trace.dy.raw.toBitVec) := by
    rw [tailRead _ (traceSafe _ (by simp [E1M1ThingGeometry.traceReads])),
      tailRead _ (traceSafe _ (by simp [E1M1ThingGeometry.traceReads])),
      tailRead _ (traceSafe _ (by simp [E1M1ThingGeometry.traceReads])),
      tailRead _ (traceSafe _ (by simp [E1M1ThingGeometry.traceReads]))]
    exact E1M1NextCallbackMemory.trace_words gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d room world dimension ids scene traceSafe
  have geometry (node : E1M1ThingList.Node) (member : node∈nextNodes) :
      E1M1ThingVisit.Geometry out.core.memory (path thing angle ox oy).trace node.pointer node.target := by
    have keep (a : Word) (ha : a∈E1M1ThingGeometry.objectReads node.pointer) :=
      read a (nextObjects.objectSafe node member a ha).before (nextObjectSafe node member a ha)
    exact ⟨congrArg (fun v => v.1) traceWords,congrArg (fun v => v.2.1) traceWords,
      congrArg (fun v => v.2.2.1) traceWords,congrArg (fun v => v.2.2.2) traceWords,
      (keep _ (by simp [E1M1ThingGeometry.objectReads])).trans (nextObjects.objectX node member),
      (keep _ (by simp [E1M1ThingGeometry.objectReads])).trans (nextObjects.objectY node member),
      (keep _ (by simp [E1M1ThingGeometry.objectReads])).trans (nextObjects.radius node member)⟩
  have linked : E1M1ThingList.Linked out.core.memory nextNodes :=
    E1M1ThingList.linked_transport _ _ nextNodes nextObjects.linked
      (fun node member => read _ (nextObjects.linkSafe node member).before (nextLinkSafe node member))
  have size := E1M1NextObjectMemory.scan_size (E1M1FiringNextSuffix.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes).core lines (path thing angle ox oy).trace
    (E1M1DuplicateSuffix.tailCell nextCell) nextData (E1M1FiringNextSuffix.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes).flags after
  change scan.2.collected.size≤after.collected.size+nextCell.ids.tail.length at size
  refine ⟨after,production,prior,cx,cy,head,empty,nonempty,hits,visits,ordered,?_,?_⟩
  · change scan.2.collected.size+nextNodes.length≤128
    omega
  · intro present
    have stack := (nonempty present).2.2.1
    have caller := E1M1NextObjectMemory.caller_word _ (s.regs 4) _ lines objects (path thing angle ox oy).trace (E1M1DuplicateSuffix.tailCell nextCell) nextData sp address items (E1M1NextCursor.tail_ids nextCell words valid) ready nextLayout returns (E1M1FiringNextSuffix.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes).flags after capacity
    change load32 out.core.memory (s.regs 4-(116#32))=(0x2cab1#32) at caller
    refine ⟨⟨(nonempty present).2.2.2,?_,geometry,linked⟩,?_⟩
    · change load32 out.core.memory (out.core.regs 4+(4#32))=_
      rw [stack]
      simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using caller
    · rw [stack]
      exact E1M1ThingListInputs.static_layout gun s weapon actor thing angle ox oy xout yout base lines words c w h data input objects nextNodes nextObjects
end Firing
end Doom.Proofs.E1M1FiringNextObjectImage
