import Doom.Proofs.E1M1FiringCellMemory
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
namespace Doom.Proofs.E1M1FiringMapState
open Verification X86 X86Memory X86Control BlockSummary
open E1M1ScanGeometry (path)
open E1M1ScanContracts (LineData)
attribute [local irreducible] load32

/-- Additional address separation after map initialization. Map values and the
setup separation still come from the existing firing-entry map contract. -/
structure Safe (sp lines a : Word) : Prop where
  scan : E1M1ThingGeometry.ScanSafe sp lines a
  caller : ∀ off∈[(116#32),120,124], Apart a (sp-off)
  objects : E1M1ThingVisit.ReadSafe (sp-(120#32)) a
  advance : Apart a (sp-(112#32)+(44#32))

theorem caller_safe (s : X86Memory.State) (sp lines a : Word)
    (stack : s.regs 4=sp-(112#32)) (safe : Safe sp lines a) :
    E1M1PathMapCaller.Safe s a := by
  unfold E1M1PathMapCaller.Safe
  rw [stack]
  exact ⟨by simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe.caller 116 (by simp),
    by simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe.caller 120 (by simp),
    by simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe.caller 124 (by simp)⟩

/-- The flag local is above all object callback writes. Only heap separation
comes from the already required flag contract. -/
theorem flag_safe (sp lines : Word) (flag : E1M1ThingGate.FlagSafe sp lines) :
    E1M1ThingVisit.ReadSafe (sp-(120#32)) (E1M1ThingGate.flagWord sp) := by
  refine ⟨?_,⟨?_,?_⟩,?_,?_,flag.array⟩
  · intro off ho
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
    rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simpa only [E1M1ThingGate.flagWord,BitVec.sub_eq_add_neg,BitVec.add_assoc] using
      OriginalPathXStep.apart_translate sp _ _ (by unfold Apart; decide)
  · simpa only [E1M1ThingGate.flagWord,BitVec.sub_eq_add_neg,BitVec.add_assoc] using
      OriginalPathXStep.apart_translate sp _ _ (by unfold Apart; decide)
  · intro off ho
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
    rcases ho with rfl|rfl|rfl|rfl|rfl
    all_goals simpa only [E1M1ThingGate.flagWord,BitVec.sub_eq_add_neg,BitVec.add_assoc] using
      OriginalPathXStep.apart_translate sp _ _ (by unfold Apart; decide)
  · simpa only [E1M1ThingGate.flagWord,BitVec.sub_eq_add_neg,BitVec.add_assoc] using
      OriginalPathXStep.apart_translate sp _ _ (by unfold Apart; decide)
  · intro off ho
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
    rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simpa only [E1M1ThingGate.flagWord,BitVec.sub_eq_add_neg,BitVec.add_assoc] using
      OriginalPathXStep.apart_translate sp _ _ (by unfold Apart; decide)

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


/-- Both enable bits still have their initialized value after the complete
cell. This uses the changed initialized flag, not its old firing-entry value. -/
theorem flag_word (room : c.ids.length+nodes.length≤128) :
    load32 (E1M1FiringCellReturn.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes).core.memory
      (E1M1ThingGate.flagWord (s.regs 4))=(3#32) := by
  have keep := E1M1FiringCellMemory.after_lines_frame gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d room
    (E1M1ThingGate.flagWord (s.regs 4))
    (by simpa only [E1M1ThingGate.flagWord,BitVec.sub_eq_add_neg] using
      OriginalPathXStep.apart_translate (s.regs 4) _ _ (by unfold Apart; decide))
    (by simpa only [E1M1ThingGate.flagWord,BitVec.sub_eq_add_neg] using
      OriginalPathXStep.apart_translate (s.regs 4) _ _ (by unfold Apart; decide))
    (flag_safe _ _ flag)
  exact keep.trans (E1M1ThingGate.scan_flag gun s weapon actor thing angle ox oy xout yout base lines words c w h data input flag)

variable (room : c.ids.length+nodes.length≤128)
    (world : Collision.Scene) (dimension : world.grid.width=w)
    (ids : world.links[Collision.pathCellIndex (path thing angle ox oy).startBlockX
      (path thing angle ox oy).startBlockY w]?=some (nodes.map E1M1ThingList.Node.id).toArray)
    (scene : ∀ node∈nodes, world.things[node.id]?=some node.target)
include room dimension ids scene

theorem enabled (line : Bool) :
    OriginalPathCell.enabled line (E1M1FiringCellReturn.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes).core=true := by
  have sp := (E1M1FiringCellReturn.execution gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d room world dimension ids scene none).2.2.1
  have byte := congrArg (fun v : Word => v.extractLsb' 0 8) (flag_word gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d room)
  rw [E1M1PathCell.low_byte] at byte
  unfold OriginalPathCell.enabled OriginalPathCell.optionBits
  rw [sp]
  have addr : s.regs 4-(112#32)+(64#32)=E1M1ThingGate.flagWord (s.regs 4) := by
    simp [E1M1ThingGate.flagWord,BitVec.sub_eq_add_neg,BitVec.add_assoc]
  change ((E1M1FiringCellReturn.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes).core.memory (s.regs 4-(112#32)+(64#32)) &&& OriginalPathCell.mask line != 0)=true
  rw [addr,byte]
  cases line <;> decide

/-- Assemble next-lookup facts at the actual completed first cell. All map
values originate at firing entry; only pure address layout is added. -/
theorem map (globalsSafe : ∀ a∈[(0x2c0fc#32),0x2c110,0x2c100,0x2c10c,0x2c120], Safe (s.regs 4) lines a)
    (imageSafe : ∀ i<words.size, Safe (s.regs 4) lines (base+BitVec.ofNat 32 (2*i))) :
    let out := (E1M1FiringCellReturn.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes).core
    E1M1PathMapCaller.Dimensions out w h ∧ E1M1PathMapCaller.Globals out base lines ∧
    E1M1PathMap.WordImage out.memory base words ∧
    (∀ a∈[(0x2c0fc#32),0x2c110,0x2c100,0x2c10c,0x2c120], Apart a (out.regs 4+(44#32))) ∧
    (∀ i<words.size, E1M1NextCellMemory.Safe out (base+BitVec.ofNat 32 (2*i))) := by
  have sp := (E1M1FiringCellReturn.execution gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d room world dimension ids scene none).2.2.1
  have keep (a : Word) (safe : Safe (s.regs 4) lines a) (setup : E1M1PathMapFiring.Safe gun s a) :
      load32 (E1M1FiringCellReturn.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes).core.memory a=load32 s.memory a := by
    exact E1M1FiringCellMemory.firing_frame gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d room a
      ⟨setup,safe.scan.scan,safe.scan.array,safe.caller 116 (by simp),safe.caller 120 (by simp)⟩ safe.objects
  have globalKeep (a : Word) (ha : a∈[(0x2c0fc#32),0x2c110,0x2c100,0x2c10c,0x2c120]) :=
    keep a (globalsSafe a ha) (input.map.globalsSafe a ha)
  refine ⟨⟨(globalKeep _ (by simp)).trans input.map.width,(globalKeep _ (by simp)).trans input.map.height,
      input.map.widthBound,input.map.heightBound,?_⟩,
    ⟨(globalKeep _ (by simp)).trans input.map.table,(globalKeep _ (by simp)).trans input.map.lists,
      (globalKeep _ (by simp)).trans input.map.lines,?_⟩,?_,?_,?_⟩
  · intro a ha
    apply caller_safe _ _ lines a sp (globalsSafe a ?_)
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl <;> simp
  · intro a ha
    apply caller_safe _ _ lines a sp (globalsSafe a ?_)
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl <;> simp
  · intro i value hv
    obtain ⟨hi,_⟩ := Array.getElem?_eq_some_iff.mp hv
    have half := congrArg (fun v : Word => v.extractLsb' 0 16) (keep _ (imageSafe i hi) (input.map.imageSafe i hi))
    rw [SectorDispatch.load_half,SectorDispatch.load_half] at half
    exact half.trans (input.map.image i value hv)
  · intro a ha
    rw [sp]
    exact (globalsSafe a ha).advance
  · intro i hi
    exact ⟨by rw [sp]; exact (imageSafe i hi).advance,caller_safe _ _ lines _ sp (imageSafe i hi)⟩
end Firing
end Doom.Proofs.E1M1FiringMapState
