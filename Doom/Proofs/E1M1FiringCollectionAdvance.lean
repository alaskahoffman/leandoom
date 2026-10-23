import Doom.Proofs.E1M1AdvanceCollection
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
namespace Doom.Proofs.E1M1FiringCollectionAdvance
open Verification X86 X86Memory X86Control BlockSummary
open E1M1ScanGeometry (path)
open E1M1ScanContracts (LineData)
open E1M1ThingListInputs (before)
open E1M1FiringGridState (initial)
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

variable (locals : E1M1GridLocals.Safe (s.regs 4) lines)
include locals

/-- First-cell advancement retains the same ordered production hits and
cursor. Its only possible local store is disjoint by the existing initial
layout contract, so no additional post-step memory premise is introduced. -/
theorem execution (room : c.ids.length+nodes.length≤128)
    (world : Collision.Scene) (dimension : world.grid.width=w)
    (ids : world.links[Collision.pathCellIndex (path thing angle ox oy).startBlockX
      (path thing angle ox oy).startBlockY w]?=some (nodes.map E1M1ThingList.Node.id).toArray)
    (scene : ∀ node∈nodes, world.things[node.id]?=some node.target) (f : Option Flags) :
    let out := E1M1FiringAdvance.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes
    (∃ steps≤427+281*c.ids.length+230*nodes.length,
      X86CodeMemory.Prefix FloorCaller.cm E1M1FiringAdvance.program [] steps
        ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ out) ∧
    out.core.regs 4=s.regs 4-(112#32) ∧
    E1M1PathAdvance.observe out.core=E1M1PathAdvance.step (initial (path thing angle ox oy) xout yout) ∧
    out.pc=E1M1PathAdvance.nextPc (initial (path thing angle ox oy) xout yout) ∧
    (∃ after, E1M1FiringThings.sceneCell (path thing angle ox oy).trace world
      (path thing angle ox oy).startBlockX (path thing angle ox oy).startBlockY
      (before gun s weapon actor thing angle ox oy xout yout base lines words c w h data input)=.ok after ∧
      OriginalLineCollection.Tracks out.core 0x2ba20 (E1M1ThingFinish.resolve lines objects) after.collected 0) := by
  obtain ⟨run,sp,obs,pc⟩ := E1M1FiringGridState.execution gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d locals room world dimension ids scene f
  obtain ⟨_,_,oldsp,_,_,_,after,production,tracked⟩ := E1M1FiringCellReturn.execution gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d room world dimension ids scene f
  have safe : OriginalLineMixedInvariant.ArraySafe 0x2ba20
      ((E1M1FiringCellReturn.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes).core.regs 4+(44#32)) := by
    rw [oldsp]
    exact locals.array 44 (by simp [E1M1GridLocals.offsets])
  exact ⟨run,sp,obs,pc,after,production,
    E1M1AdvanceCollection.collection _ _ _ _ 0 tracked safe⟩

/-- If the first cell is not the endpoint, the reached next-cell gate has count
one and the same collected hits. Later lookup/scan obligations are not assumed. -/
theorem next_cell (room : c.ids.length+nodes.length≤128)
    (world : Collision.Scene) (dimension : world.grid.width=w)
    (ids : world.links[Collision.pathCellIndex (path thing angle ox oy).startBlockX
      (path thing angle ox oy).startBlockY w]?=some (nodes.map E1M1ThingList.Node.id).toArray)
    (scene : ∀ node∈nodes, world.things[node.id]?=some node.target) (f : Option Flags)
    (notEnd : E1M1PathAdvance.ended (initial (path thing angle ox oy) xout yout)=false) :
    let out := E1M1FiringAdvance.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes
    (∃ steps≤427+281*c.ids.length+230*nodes.length,
      X86CodeMemory.Prefix FloorCaller.cm E1M1FiringAdvance.program [] steps
        ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ out) ∧
    out.core.regs 4=s.regs 4-(112#32) ∧ out.pc=0x2ca7f ∧ out.core.regs 7=(1#32) ∧
    E1M1PathAdvance.observe out.core=
      {E1M1PathAdvance.axis (initial (path thing angle ox oy) xout yout) with count:=1} ∧
    (∃ after, E1M1FiringThings.sceneCell (path thing angle ox oy).trace world
      (path thing angle ox oy).startBlockX (path thing angle ox oy).startBlockY
      (before gun s weapon actor thing angle ox oy xout yout base lines words c w h data input)=.ok after ∧
      OriginalLineCollection.Tracks out.core 0x2ba20 (E1M1ThingFinish.resolve lines objects) after.collected 0) := by
  obtain ⟨run,sp,obs,pc,hits⟩ := execution gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d locals room world dimension ids scene f
  have budget := E1M1AdvanceCollection.counter (initial (path thing angle ox oy) xout yout) 0 (by decide) rfl
  have count := (congrArg E1M1PathAdvance.Cell.count obs).trans budget.1
  have next := pc.trans budget.2
  have axis : E1M1PathAdvance.step (initial (path thing angle ox oy) xout yout)=
      {E1M1PathAdvance.axis (initial (path thing angle ox oy) xout yout) with count:=1} := by
    simp only [E1M1PathAdvance.step,notEnd,Bool.false_eq_true,↓reduceIte]
    rfl
  exact ⟨run,sp,by simpa [notEnd] using next,by simpa [E1M1PathAdvance.observe,notEnd] using count,obs.trans axis,hits⟩
end Firing
end Doom.Proofs.E1M1FiringCollectionAdvance
