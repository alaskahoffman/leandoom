import Doom.Proofs.E1M1NextCallbackReady
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1FiringNextGeometry
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
/-- Join derived callback readiness to the same continuous firing prefix.
All added values describe initial line data or pure production computations;
no next-cell callback inputs are assumed at the reached machine state. -/
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
    (activeSafe : E1M1FiringMapState.Safe (s.regs 4) lines (0x2c024#32)) :
    let entry := E1M1FiringNextScan.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes
    let out := E1M1FiringNextSuffix.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes
    (∃ steps≤467+281*c.ids.length+230*nodes.length,
      X86CodeMemory.Prefix FloorCaller.cm E1M1FiringAdvance.program [] steps
        ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ out) ∧
    E1M1PathMapLookup.ScanWords out.core lines (E1M1DuplicateSuffix.tailCell nextCell) ∧
    out.pc=0x2c57f ∧ out.core.regs 4=s.regs 4-(124#32) ∧
    out.core.memory=entry.core.memory ∧ out.core.regs 2=entry.core.regs 2+(2#32) ∧
    (∃ after, E1M1FiringThings.sceneCell (path thing angle ox oy).trace world
      (path thing angle ox oy).startBlockX (path thing angle ox oy).startBlockY
      (before gun s weapon actor thing angle ox oy xout yout base lines words c w h data input)=.ok after ∧
      after.collected.size≤c.ids.length+nodes.length ∧
      OriginalLineCollection.Tracks out.core 0x2ba20 (E1M1ThingFinish.resolve lines objects)
        after.collected (128-(c.ids.length+nodes.length))) ∧
    Represents out.core.memory lines (load32 s.memory 0x13580+1)
      (seenAfter (path thing angle ox oy).trace lines c data) ∧
    Ready out.core lines (path thing angle ox oy).trace (E1M1DuplicateSuffix.tailCell nextCell) nextData := by
  have prior := E1M1FiringNextSuffix.execution gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d stamps epochBefore epochAfter stampSetup fresh epochTail stampTail room world dimension ids scene locals f globalsSafe imageSafe notEnd x y mapX mapY nextCell inMap valid selectedCell
  obtain ⟨run,items,pc,sp,memory,cursor,hits,represented⟩ := prior
  have trace := E1M1NextCallbackMemory.trace_words gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d room world dimension ids scene traceSafe
  have active := E1M1NextCallbackMemory.active gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d room world dimension ids scene activeSafe
  have callback := E1M1NextCallbackMemory.callback_word gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d room world dimension ids scene
  have ready : Ready (E1M1FiringNextSuffix.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes).core lines
      (path thing angle ox oy).trace (E1M1DuplicateSuffix.tailCell nextCell) nextData := by
    refine ⟨?_,?_,?_,?_,nextInput.computed,?_⟩
    · rw [sp,memory]; exact callback
    · rw [memory]; exact active
    · intro i
      apply E1M1ScanGeometry.callback_geometry _ (s.regs 4) sp i.val _ _ _ _ _
        (items.pointers i (Fixed.ofInt 0)) _ _ (nextInput.callback i)
      · rw [memory]; exact trace
      · apply E1M1NextCallbackMemory.line_words s.memory _ _ _ _ _ (nextInput.encoded i)
        intro a ha
        rw [memory]
        exact E1M1NextCallbackMemory.firing_frame gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d room world dimension ids scene a (nextInput.setup i a ha) (nextInput.safe i a ha)
    · intro i
      rw [memory,E1M1NextCallbackMemory.firing_frame gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d room world dimension ids scene _ (nextInput.backSetup i) (nextInput.backSafe i)]
      exact nextInput.back i
    · intro i
      have bound : (E1M1DuplicateSuffix.tailCell nextCell).ids[i.val]<475 := by
        have hi : i.val+1<nextCell.ids.length := by
          have := i.isLt
          change i.val<nextCell.ids.tail.length at this
          have nonempty : nextCell.ids≠[] := by intro eq; have h := valid.2.1; simp [eq] at h
          have len : nextCell.ids.tail.length+1=nextCell.ids.length := by cases h : nextCell.ids <;> simp_all
          omega
        simpa [E1M1DuplicateSuffix.tailCell,List.getElem_tail] using (valid.2.2.2.1 ⟨i.val+1,hi⟩).1
      exact E1M1ScanGeometry.storage_layout _ (s.regs 4) lines sp i.val _ bound
        (items.pointers i (Fixed.ofInt 0)) input.layout.storage
  exact ⟨run,items,pc,sp,memory,cursor,hits,represented,ready⟩
end Firing
end Doom.Proofs.E1M1FiringNextGeometry
