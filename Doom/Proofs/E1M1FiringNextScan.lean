import Doom.Proofs.E1M1FiringMapState
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
namespace Doom.Proofs.E1M1FiringNextScan
open Verification X86 X86Memory X86Control BlockSummary
open E1M1ScanGeometry (path)
open E1M1ScanContracts (LineData)
open E1M1ThingListInputs (before)
open E1M1FiringGridState (initial)
attribute [local irreducible] load32 Collision.pathFirstIntercept

/-- The next caller reuses precisely the same three stack slots. Their array
separation is already in the first scan and saved-return contracts. -/
theorem caller_array (sp cursor lines : Word) (n : Nat)
    (cs : Nat → OriginalLineMixedInvariant.Candidate)
    (layout : E1M1ScanContracts.Layout sp cursor lines n cs)
    (returns : E1M1ScanReturn.ReturnSafe sp lines)
    (off : Word) (member : off∈[(116#32),120,124]) :
    OriginalLineMixedInvariant.ArraySafe 0x2ba20 (sp-off) := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl
  · exact returns.array _ (by simp [E1M1ScanReturn.returnWords])
  · exact returns.array _ (by simp [E1M1ScanReturn.returnWords])
  · exact layout.arrayWords _ (E1M1ScanContracts.fixed_member sp cursor n cs _ (by simp))

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

omit returns flag lookupSafe global selected d locals in
def result := E1M1NextCellMemory.scan
  (E1M1FiringCellReturn.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes).core

/-- Continuous firing execution reaches the next selected line-list entry.
Map and enable inputs are derived through the first scans. The previous scene
cell's hits survive, but this theorem does not execute the next line callback
or claim any new capacity for it. -/
theorem execution (room : c.ids.length+nodes.length≤128)
    (world : Collision.Scene) (dimension : world.grid.width=w)
    (ids : world.links[Collision.pathCellIndex (path thing angle ox oy).startBlockX
      (path thing angle ox oy).startBlockY w]?=some (nodes.map E1M1ThingList.Node.id).toArray)
    (scene : ∀ node∈nodes, world.things[node.id]?=some node.target) (f : Option Flags)
    (globalsSafe : ∀ a∈[(0x2c0fc#32),0x2c110,0x2c100,0x2c10c,0x2c120], E1M1FiringMapState.Safe (s.regs 4) lines a)
    (imageSafe : ∀ i<words.size, E1M1FiringMapState.Safe (s.regs 4) lines (base+BitVec.ofNat 32 (2*i)))
    (notEnd : E1M1PathAdvance.ended (initial (path thing angle ox oy) xout yout)=false)
    (x y : Int32)
    (mapX : (E1M1PathAdvance.step (initial (path thing angle ox oy) xout yout)).mapX=x.toBitVec)
    (mapY : (E1M1PathAdvance.step (initial (path thing angle ox oy) xout yout)).mapY=y.toBitVec)
    (nextCell : E1M1PathMap.Cell) (inMap : Collision.pathCellInside x y w h=true)
    (valid : nextCell.Valid words) (selectedCell : words[4+Collision.pathCellIndex x y w]?=some nextCell.offset) :
    let out := result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes
    (∃ steps≤457+281*c.ids.length+230*nodes.length,
      X86CodeMemory.Prefix FloorCaller.cm E1M1FiringAdvance.program [] steps
        ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ out) ∧
    E1M1PathMapLookup.ScanWords out.core lines nextCell ∧ out.pc=0x2c57f ∧
    out.core.regs 4=s.regs 4-(124#32) ∧
    (∃ after, E1M1FiringThings.sceneCell (path thing angle ox oy).trace world
      (path thing angle ox oy).startBlockX (path thing angle ox oy).startBlockY
      (before gun s weapon actor thing angle ox oy xout yout base lines words c w h data input)=.ok after ∧
      OriginalLineCollection.Tracks out.core 0x2ba20 (E1M1ThingFinish.resolve lines objects) after.collected 0) := by
  obtain ⟨⟨a,ha,prior⟩,_,sp,pc,_,_,after,production,tracked⟩ :=
    E1M1FiringCellReturn.execution gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d room world dimension ids scene f
  have obs := E1M1FiringGridState.before_observe gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d locals room world.things scene
  have maps := E1M1FiringMapState.map gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d room world dimension ids scene globalsSafe imageSafe
  have enabled := E1M1FiringMapState.enabled gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d room world dimension ids scene true
  have next : E1M1PathAdvance.nextPc (initial (path thing angle ox oy) xout yout)=0x2ca7f := by
    simpa [notEnd] using (E1M1AdvanceCollection.counter (initial (path thing angle ox oy) xout yout) 0 (by decide) rfl).2
  obtain ⟨⟨b,hb,tail⟩,items,stop,stack⟩ := E1M1NextCellScan.inside
    (E1M1FiringCellReturn.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes).core
    (E1M1FiringCellReturn.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes).flags
    (initial (path thing angle ox oy) xout yout) obs next x y mapX mapY base lines words nextCell w h
    enabled maps.1 maps.2.1 maps.2.2.1 maps.2.2.2.1 maps.2.2.2.2 inMap valid selectedCell
  rw [OriginalPathXStep.at_pc _ _ pc] at tail
  have retained : OriginalLineCollection.Tracks (result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes).core
      0x2ba20 (E1M1ThingFinish.resolve lines objects) after.collected 0 := by
    apply E1M1NextCellMemory.collection _ _ _ _ 0 tracked
    · rw [sp]
      exact locals.array 44 (by simp [E1M1GridLocals.offsets])
    · unfold E1M1PathMapCaller.Safe
      rw [sp]
      have safe (off : Word) (ho : off∈[(116#32),120,124]) :=
        (caller_array (s.regs 4) _ lines _ _ input.layout returns off ho).2
      exact ⟨by simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using FloorCaller.apart_symm (safe 116 (by simp)),
        by simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using FloorCaller.apart_symm (safe 120 (by simp)),
        by simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using FloorCaller.apart_symm (safe 124 (by simp))⟩
    · intro i hi off ho
      have bound : i<128 := by have := tracked.room; omega
      have safe (k : Word) (hk : k∈[(116#32),120,124]) := FloorCaller.apart_symm
        ((caller_array (s.regs 4) _ lines _ _ input.layout returns k hk).1 i bound off ho)
      unfold E1M1PathMapCaller.Safe
      rw [sp]
      exact ⟨by simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe 116 (by simp),
        by simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe 120 (by simp),
        by simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe 124 (by simp)⟩
  refine ⟨⟨a+b,by omega,E1M1PspriteStep.prefix_trans
      (prior.transfer E1M1FiringAdvance.program [] E1M1FiringAdvance.contains_prior (by simp)) tail⟩,
    items,stop,?_,after,production,retained⟩
  rw [sp] at stack
  simpa [result,BitVec.sub_eq_add_neg,BitVec.add_assoc] using stack
end Firing
end Doom.Proofs.E1M1FiringNextScan
