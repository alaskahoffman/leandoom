import Doom.Proofs.E1M1FiringNextGeometry
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1NextCursor
open Verification X86 X86Memory X86Control BlockSummary
open E1M1ScanGeometry (path)
open E1M1ScanContracts (LineData)
open E1M1FiringGridState (initial)
attribute [local irreducible] load32

/-- Moving past the duplicate advances the original modular BLOCKMAP address. -/
theorem tail_address (base : Word) (offset : Nat) :
    base+BitVec.ofNat 32 (2*offset)+(2#32)=base+BitVec.ofNat 32 (2*(offset+1)) := by
  simp [Nat.mul_add,BitVec.ofNat_add,BitVec.add_assoc]

/-- Cell validity bounds the IDs in the remaining suffix as well. -/
theorem tail_ids (c : E1M1PathMap.Cell) (words : Array Nat) (valid : c.Valid words)
    (i : Fin (E1M1DuplicateSuffix.tailCell c).ids.length) :
    (E1M1DuplicateSuffix.tailCell c).ids[i.val]<475 := by
  have hi : i.val+1<c.ids.length := by
    have := i.isLt
    change i.val<c.ids.tail.length at this
    have nonempty : c.ids≠[] := by intro eq; have h := valid.2.1; simp [eq] at h
    have len : c.ids.tail.length+1=c.ids.length := by cases h : c.ids <;> simp_all
    omega
  simpa [E1M1DuplicateSuffix.tailCell,List.getElem_tail] using (valid.2.2.2.1 ⟨i.val+1,hi⟩).1

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

/-- The selected offset, not an assumed reached cursor, fixes the next list address. -/
theorem firing_cursor (globalsSafe : ∀ a∈[(0x2c0fc#32),0x2c110,0x2c100,0x2c10c,0x2c120], E1M1FiringMapState.Safe (s.regs 4) lines a)
    (imageSafe : ∀ i<words.size, E1M1FiringMapState.Safe (s.regs 4) lines (base+BitVec.ofNat 32 (2*i)))
    (x y : Int32)
    (mapX : (E1M1PathAdvance.step (initial (path thing angle ox oy) xout yout)).mapX=x.toBitVec)
    (mapY : (E1M1PathAdvance.step (initial (path thing angle ox oy) xout yout)).mapY=y.toBitVec)
    (nextCell : E1M1PathMap.Cell) (inMap : Collision.pathCellInside x y w h=true)
    (valid : nextCell.Valid words) (selectedCell : words[4+Collision.pathCellIndex x y w]?=some nextCell.offset) :
    (E1M1FiringNextScan.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes).core.regs 2=base+BitVec.ofNat 32 (2*nextCell.offset) := by
  have maps := E1M1FiringMapState.map gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d room world dimension ids scene globalsSafe imageSafe
  have obs := E1M1FiringGridState.before_observe gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d locals room world.things scene
  have advanced := (E1M1PathAdvance.result_observe (E1M1FiringCellReturn.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes).core).1
  rw [obs] at advanced
  have next := E1M1NextCellMemory.map _ base lines words w h maps.1 maps.2.1 maps.2.2.1 maps.2.2.2.1 maps.2.2.2.2
  exact E1M1FiringScan.caller_cursor _ base lines words nextCell x y w h next.1
    ((congrArg E1M1PathAdvance.Cell.mapX advanced).trans mapX)
    ((congrArg E1M1PathAdvance.Cell.mapY advanced).trans mapY)
    next.2.1 inMap valid next.2.2.1 next.2.2.2 selectedCell
end Firing
end Doom.Proofs.E1M1NextCursor
