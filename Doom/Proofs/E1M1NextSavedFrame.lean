import Doom.Proofs.E1M1NextLineReturn
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1NextSavedFrame
open Verification X86 X86Memory X86Control BlockSummary
open E1M1ScanGeometry (path)
open E1M1ScanContracts (LineData)
attribute [local irreducible] load32

/-- Reuse flag/heap separation; all stack gaps follow from the original SP. -/
theorem flag_safe (sp lines : Word) (flag : E1M1ThingGate.FlagSafe sp lines) :
    E1M1FiringMapState.Safe sp lines (E1M1ThingGate.flagWord sp) := by
  refine ⟨⟨E1M1ThingGate.flag_protected sp lines flag.stamps,flag.array⟩,?_,
    E1M1FiringMapState.flag_safe sp lines flag,?_⟩
  · intro off ho
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
    rcases ho with rfl|rfl|rfl
    all_goals simpa only [E1M1ThingGate.flagWord,BitVec.sub_eq_add_neg,BitVec.add_assoc] using
      OriginalPathXStep.apart_translate sp _ _ (by unfold Apart; decide)
  · simpa only [E1M1ThingGate.flagWord,BitVec.sub_eq_add_neg,BitVec.add_assoc] using
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


variable (room : c.ids.length+nodes.length≤128)
    (world : Collision.Scene) (dimension : world.grid.width=w)
    (ids : world.links[Collision.pathCellIndex (path thing angle ox oy).startBlockX
      (path thing angle ox oy).startBlockY w]?=some (nodes.map E1M1ThingList.Node.id).toArray)
    (scene : ∀ node∈nodes, world.things[node.id]?=some node.target)
include room dimension ids scene


/-- The caller's actual CALL/PUSH determine the next saved EDI and return word. -/
theorem saved_words :
    let m := (E1M1FiringNextScan.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes).core.memory
    load32 m (s.regs 4-(120#32))=
      (E1M1NextCellMemory.advanced (E1M1FiringCellReturn.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes).core).regs 7 ∧
    load32 m (s.regs 4-(116#32))=(0x2ca94#32) := by
  have sp := (E1M1FiringCellReturn.execution gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d room world dimension ids scene none).2.2.1
  have saved := E1M1ScanReturn.caller_words
    (E1M1NextCellMemory.advanced (E1M1FiringCellReturn.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes).core)
  rw [E1M1NextCellMemory.stack,sp] at saved
  simpa [E1M1FiringNextScan.result,BitVec.sub_eq_add_neg,BitVec.add_assoc] using saved

/-- The next caller retains the initialized line/object enable bits. -/
theorem flag_word :
    load32 (E1M1FiringNextScan.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes).core.memory
      (E1M1ThingGate.flagWord (s.regs 4))=(3#32) :=
  (E1M1NextCallbackMemory.next_frame gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d room world dimension ids scene _ (flag_safe _ _ flag)).trans
    (E1M1FiringMapState.flag_word gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d room)
end Firing
end Doom.Proofs.E1M1NextSavedFrame
