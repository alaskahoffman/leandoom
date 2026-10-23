import Doom.Proofs.E1M1CellCapacity
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1FiringNextSuffix
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

/-- The actual state after consuming the next cell's leading duplicate. -/
def result := OriginalLineCell.visit (E1M1FiringNextScan.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes).core

/-- Execute the derived duplicate branch and retain its exact list suffix,
visit history and hits. Remaining capacity follows from the proved first-cell
candidate bound, not from a new assumption about the reached hit count. -/
theorem execution (f : Option Flags)
    (globalsSafe : ∀ a∈[(0x2c0fc#32),0x2c110,0x2c100,0x2c10c,0x2c120], E1M1FiringMapState.Safe (s.regs 4) lines a)
    (imageSafe : ∀ i<words.size, E1M1FiringMapState.Safe (s.regs 4) lines (base+BitVec.ofNat 32 (2*i)))
    (notEnd : E1M1PathAdvance.ended (initial (path thing angle ox oy) xout yout)=false)
    (x y : Int32)
    (mapX : (E1M1PathAdvance.step (initial (path thing angle ox oy) xout yout)).mapX=x.toBitVec)
    (mapY : (E1M1PathAdvance.step (initial (path thing angle ox oy) xout yout)).mapY=y.toBitVec)
    (nextCell : E1M1PathMap.Cell) (inMap : Collision.pathCellInside x y w h=true)
    (valid : nextCell.Valid words) (selectedCell : words[4+Collision.pathCellIndex x y w]?=some nextCell.offset) :
    let entry := E1M1FiringNextScan.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes
    let out := result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes
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
      (seenAfter (path thing angle ox oy).trace lines c data) := by
  obtain ⟨⟨n,hn,prior⟩,items,pc,sp,⟨after,production,tracked⟩,represented,duplicate⟩ :=
    E1M1FiringVisitedNext.execution gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d stamps epochBefore epochAfter stampSetup fresh epochTail stampTail room world dimension ids scene locals f globalsSafe imageSafe notEnd x y mapX mapY nextCell inMap valid selectedCell
  have last := (E1M1FiringVisitedNext.leading_duplicate _ lines _ words nextCell valid items _
    (E1M1FiringLineVisits.seen_size _ _ _ _) represented
    (E1M1FiringLineVisits.seen_zero _ _ _ _ words input.valid)).1
  obtain ⟨⟨m,hm,tail⟩,memory,cursor,stack,stop⟩ := E1M1DuplicateSuffix.skip
    (E1M1FiringNextScan.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes) pc last duplicate
  have nonempty : nextCell.ids≠[] := by
    intro eq
    have head := valid.2.1
    simp [eq] at head
  have suffix := E1M1DuplicateSuffix.scan_tail _ _ lines nextCell nonempty items memory cursor
  have lineBound := E1M1ScanCapacity.finished_size (E1M1ScanMemory.firstScan gun s).core c.ids.length 0x2ba20
    (E1M1PathMap.resolve lines) (E1M1FiringScan.initial gun s weapon actor thing angle ox oy xout yout base lines words c w h data input)
    (E1M1ScanMemory.firstScan gun s).flags (path thing angle ox oy).trace
  change (before gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).collected.size≤c.ids.length at lineBound
  have objectBound := E1M1CellCapacity.scene_bound _ world _ _ w nodes _ after dimension ids scene production
  have bound : after.collected.size≤c.ids.length+nodes.length := by omega
  have retained : OriginalLineCollection.Tracks (result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes).core
      0x2ba20 (E1M1ThingFinish.resolve lines objects) after.collected 0 := by
    refine ⟨?_,?_,tracked.room⟩
    · change OriginalLineFinish.Encodes (OriginalLineCell.visit _).core.memory _ _ _
      rw [memory]; exact tracked.encoded
    · change load32 (OriginalLineCell.visit _).core.memory _=_
      rw [memory]; exact tracked.cursor
  refine ⟨⟨n+m,by omega,E1M1PspriteStep.prefix_trans prior tail⟩,
    suffix,stop,stack.trans sp,memory,cursor,⟨after,production,bound,
    E1M1CellCapacity.reserve _ _ _ _ _ retained bound room⟩,?_⟩
  change Represents (OriginalLineCell.visit _).core.memory _ _ _
  rw [memory]; exact represented
end Firing
end Doom.Proofs.E1M1FiringNextSuffix
