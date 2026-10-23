import Doom.Proofs.E1M1FiringLineVisits
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1FiringVisitedNext
open Verification X86 X86Memory X86Control BlockSummary
open E1M1ScanGeometry (path)
open E1M1ScanContracts (LineData)
open E1M1ThingListInputs (before)
open E1M1FiringGridState (initial)
open E1M1FiringLineVisits (seenAfter)
open OriginalLineVisits (Represents stamp)
attribute [local irreducible] load32 Collision.pathFirstIntercept

/-- Post-line-scan writes only. In particular this must not require a mutable
stamp to be disjoint from the line scan's write to that very same stamp. -/
structure TailSafe (sp a : Word) : Prop where
  caller : ∀ off∈[(116#32),120,124], Apart a (sp-off)
  objects : E1M1ThingVisit.ReadSafe (sp-(120#32)) a
  advance : Apart a (sp-(112#32)+(44#32))

theorem next_safe (s : X86Memory.State) (sp a : Word)
    (stack : s.regs 4=sp-(112#32)) (safe : TailSafe sp a) :
    E1M1NextCellMemory.Safe s a := by
  refine ⟨?_,?_⟩
  · rw [stack]; exact safe.advance
  · unfold E1M1PathMapCaller.Safe
    rw [stack]
    exact ⟨by simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe.caller 116 (by simp),
      by simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe.caller 120 (by simp),
      by simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe.caller 124 (by simp)⟩

set_option backward.isDefEq.respectTransparency false in
/-- At an actual cell entry, the leading linedef zero takes the duplicate
branch if a preceding cell marked it. No geometry or free hit slot is needed. -/
theorem leading_duplicate (s : X86Memory.State) (lines epoch : Word)
    (words : Array Nat) (c : E1M1PathMap.Cell) (valid : c.Valid words)
    (items : E1M1PathMapLookup.ScanWords s lines c) (seen : Array Bool)
    (size : seen.size=475) (represented : Represents s.memory lines epoch seen)
    (marked : seen[0]! =true) :
    OriginalLineCell.itemWord s≠(0xffffffff#32) ∧
    OriginalLineCell.already (OriginalLineCell.header s).core := by
  have head := valid.2.1
  have positive : 0<c.ids.length := by
    cases ids : c.ids <;> simp_all
  have zero : c.ids[0]! =0 := by
    cases ids : c.ids with
    | nil => simp [ids] at positive
    | cons id rest => simpa [ids] using head
  have ptr : OriginalLineDispatch.pointer s=E1M1PathMap.resolve lines ⟨Fixed.ofInt 0,true,0⟩ := by
    have value := items.pointers ⟨0,positive⟩ (Fixed.ofInt 0)
    rw [←getElem!_pos c.ids 0 positive,zero] at value
    simpa [OriginalLineDispatch.pointer,OriginalLineCell.itemWord,OriginalLineCell.item,
      OriginalLineInvariant.atIndex,OriginalLineInvariant.address,put,write] using value
  constructor
  · simpa [OriginalLineCell.itemWord,OriginalLineCell.item,
      OriginalLineInvariant.atIndex,OriginalLineInvariant.address,put,write] using items.nonlast ⟨0,positive⟩
  · change load32 s.memory 0x13580=load32 s.memory (OriginalLineDispatch.stamp s)
    have addr : OriginalLineDispatch.stamp s=stamp lines 0 := by
      unfold OriginalLineDispatch.stamp
      rw [ptr]
      rfl
    rw [addr,represented.1]
    exact ((represented.2 0 (by omega)).mpr marked).symm

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

/-- The modified stamps survive the full object list and caller return. All
values are obtained from initialization and the actual first line scan. -/
theorem before_seen (room : c.ids.length+nodes.length≤128) :
    Represents (E1M1FiringCellReturn.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes).core.memory lines
      (load32 s.memory 0x13580+1) (seenAfter (path thing angle ox oy).trace lines c data) := by
  have old := E1M1FiringLineVisits.fresh_scan gun s weapon actor thing angle ox oy xout yout base lines words c w h data input stamps epochBefore epochAfter stampSetup fresh
  have keep (a : Word) (safe : TailSafe (s.regs 4) a) :=
    E1M1FiringCellMemory.after_lines_frame gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d room a
      (safe.caller 116 (by simp)) (safe.caller 120 (by simp)) safe.objects
  refine ⟨(keep _ epochTail).trans old.1,?_⟩
  intro j hj
  have bound : j<475 := by rw [E1M1FiringLineVisits.seen_size] at hj; exact hj
  rw [keep _ (stampTail j bound)]
  exact old.2 j hj

variable (room : c.ids.length+nodes.length≤128)
    (world : Collision.Scene) (dimension : world.grid.width=w)
    (ids : world.links[Collision.pathCellIndex (path thing angle ox oy).startBlockX
      (path thing angle ox oy).startBlockY w]?=some (nodes.map E1M1ThingList.Node.id).toArray)
    (scene : ∀ node∈nodes, world.things[node.id]?=some node.target)
include room dimension ids scene

/-- Advance and lookup retain the updated bitset, without resetting it for the
next cell. This is the exact state used by the joined firing prefix. -/
theorem next_seen :
    Represents (E1M1FiringNextScan.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes).core.memory lines
      (load32 s.memory 0x13580+1) (seenAfter (path thing angle ox oy).trace lines c data) := by
  have sp := (E1M1FiringCellReturn.execution gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d room world dimension ids scene none).2.2.1
  apply E1M1NextCellMemory.visits _ lines _ _
    (before_seen gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d stamps epochBefore epochAfter stampSetup fresh epochTail stampTail room)
    (next_safe _ _ _ sp epochTail)
  intro j hj
  exact next_safe _ _ _ sp (stampTail j (by rw [E1M1FiringLineVisits.seen_size] at hj; exact hj))

variable (locals : E1M1GridLocals.Safe (s.regs 4) lines)
include locals

/-- The updated visited relation accompanies the continuous firing prefix,
selected next-cell list and retained ordered hits at one reached state. -/
theorem execution (f : Option Flags)
    (globalsSafe : ∀ a∈[(0x2c0fc#32),0x2c110,0x2c100,0x2c10c,0x2c120], E1M1FiringMapState.Safe (s.regs 4) lines a)
    (imageSafe : ∀ i<words.size, E1M1FiringMapState.Safe (s.regs 4) lines (base+BitVec.ofNat 32 (2*i)))
    (notEnd : E1M1PathAdvance.ended (initial (path thing angle ox oy) xout yout)=false)
    (x y : Int32)
    (mapX : (E1M1PathAdvance.step (initial (path thing angle ox oy) xout yout)).mapX=x.toBitVec)
    (mapY : (E1M1PathAdvance.step (initial (path thing angle ox oy) xout yout)).mapY=y.toBitVec)
    (nextCell : E1M1PathMap.Cell) (inMap : Collision.pathCellInside x y w h=true)
    (valid : nextCell.Valid words) (selectedCell : words[4+Collision.pathCellIndex x y w]?=some nextCell.offset) :
    let out := E1M1FiringNextScan.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes
    (∃ steps≤457+281*c.ids.length+230*nodes.length,
      X86CodeMemory.Prefix FloorCaller.cm E1M1FiringAdvance.program [] steps
        ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ out) ∧
    E1M1PathMapLookup.ScanWords out.core lines nextCell ∧ out.pc=0x2c57f ∧
    out.core.regs 4=s.regs 4-(124#32) ∧
    (∃ after, E1M1FiringThings.sceneCell (path thing angle ox oy).trace world
      (path thing angle ox oy).startBlockX (path thing angle ox oy).startBlockY
      (before gun s weapon actor thing angle ox oy xout yout base lines words c w h data input)=.ok after ∧
      OriginalLineCollection.Tracks out.core 0x2ba20 (E1M1ThingFinish.resolve lines objects) after.collected 0) ∧
    Represents out.core.memory lines (load32 s.memory 0x13580+1)
      (seenAfter (path thing angle ox oy).trace lines c data) ∧
    OriginalLineCell.already (OriginalLineCell.header out.core).core := by
  obtain ⟨run,items,pc,sp,hits⟩ := E1M1FiringNextScan.execution gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d locals
    room world dimension ids scene f globalsSafe imageSafe notEnd x y mapX mapY nextCell inMap valid selectedCell
  have represented := next_seen gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d stamps epochBefore epochAfter stampSetup fresh epochTail stampTail room world dimension ids scene
  have duplicate := leading_duplicate _ lines _ words nextCell valid items _
    (E1M1FiringLineVisits.seen_size _ _ _ _) represented
    (E1M1FiringLineVisits.seen_zero _ _ _ _ words input.valid)
  exact ⟨run,items,pc,sp,hits,represented,duplicate.2⟩
end Firing
end Doom.Proofs.E1M1FiringVisitedNext
