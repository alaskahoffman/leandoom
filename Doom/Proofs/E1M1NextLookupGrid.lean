import Doom.Proofs.E1M1NextScanGrid
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1NextLookupGrid
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
/-- Identify every second-lookup grid field with the first production step.
The first collection result is identified by determinism, not assumed machine values. -/
theorem observe (f : Option Flags)
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
    (after : Collision.PathResult)
    (production : E1M1FiringThings.sceneCell (path thing angle ox oy).trace world
      (path thing angle ox oy).startBlockX (path thing angle ox oy).startBlockY
      (before gun s weapon actor thing angle ox oy xout yout base lines words c w h data input)=.ok after) :
    let start := E1M1FiringNextSuffix.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes
    let entry := E1M1NextObjectMemory.result start.core lines (path thing angle ox oy).trace
      (E1M1DuplicateSuffix.tailCell nextCell) nextData start.flags after
    E1M1PathAdvance.observe (E1M1ObjectBoundary.callerView entry (s.regs 4))=
      E1M1PathAdvance.step (initial (path thing angle ox oy) xout yout) := by
  let start := E1M1FiringNextSuffix.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes
  let advanced := E1M1NextCellMemory.advanced (E1M1FiringCellReturn.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes).core
  obtain ⟨_,items,_,sp,mem,cursor,⟨sameAfter,sameProduction,_,tracked⟩,_,ready⟩ :=
    E1M1FiringNextGeometry.execution gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d stamps epochBefore epochAfter stampSetup fresh epochTail stampTail room world dimension ids scene locals f globalsSafe imageSafe notEnd x y mapX mapY nextCell inMap valid selectedCell nextData nextInput traceSafe activeSafe
  have same : sameAfter=after := Except.ok.inj (sameProduction.symm.trans production)
  subst sameAfter
  have entry := E1M1NextCursor.firing_cursor gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d room world dimension ids scene locals globalsSafe imageSafe
    x y mapX mapY nextCell inMap valid selectedCell
  have address : start.core.regs 2=base+BitVec.ofNat 32 (2*(nextCell.offset+1)) := by
    rw [cursor,entry,E1M1NextCursor.tail_address]
  have capacity := E1M1CellCapacity.suffix_reserve _ _ _ _ (c.ids.length+nodes.length)
    nextCell.ids.tail.length tracked budget
  have regs := E1M1NextScanGrid.registers start.core (s.regs 4) _ lines objects
    (path thing angle ox oy).trace (E1M1DuplicateSuffix.tailCell nextCell) nextData
    sp address items (E1M1NextCursor.tail_ids nextCell words valid) ready nextLayout
    returns start.flags after capacity
  have keep := E1M1NextScanGrid.local_word start.core (s.regs 4) _ lines objects
    (path thing angle ox oy).trace (E1M1DuplicateSuffix.tailCell nextCell) nextData
    sp address items (E1M1NextCursor.tail_ids nextCell words valid) ready nextLayout
    returns start.flags after capacity locals
  have before := E1M1FiringGridState.before_observe gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d locals room world.things scene
  have advancedObs := (E1M1PathAdvance.result_observe
    (E1M1FiringCellReturn.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes).core).1
  rw [before] at advancedObs
  have priorSP := (E1M1FiringCellReturn.execution gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d room world dimension ids scene none).2.2.1
  have advancedSP : advanced.regs 4=s.regs 4-(112#32) :=
    (E1M1NextCellMemory.stack _).trans priorSP
  have saved := E1M1NextSavedFrame.saved_words gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d room world dimension ids scene
  apply Eq.trans (E1M1FiringGridState.transport _ advanced ?_ ?_) advancedObs
  · intro reg member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl
    · exact (regs.1 1 (by simp)).trans
        ((OriginalLineCoordinates.visit_coordinate _ false).trans
          (E1M1ThingCoordinates.caller_coordinate advanced false))
    · exact (regs.1 5 (by simp)).trans
        ((OriginalLineInterceptRegister.visit_intercept _).trans
          (E1M1FiringGridRegisters.caller_intercept advanced))
    · exact (regs.1 6 (by simp)).trans
        ((OriginalLineCoordinates.visit_coordinate _ true).trans
          (E1M1ThingCoordinates.caller_coordinate advanced true))
    · have counter := regs.2
      rw [mem,saved.1] at counter
      exact counter
  · intro off member
    change load32 _ (s.regs 4-(112#32)+off)=load32 advanced.memory (advanced.regs 4+off)
    rw [advancedSP]
    have kept := keep off member
    rw [mem] at kept
    exact kept.trans (E1M1NextScanGrid.caller_local advanced (s.regs 4) advancedSP off member)
end Firing
end Doom.Proofs.E1M1NextLookupGrid
