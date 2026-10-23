import Doom.Proofs.E1M1CellSceneInvariant
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1FiringSceneData
open Verification X86 X86Memory X86Control BlockSummary
open E1M1ScanGeometry (path linePointer)
open E1M1ScanContracts (LineData)
open E1M1CellSceneInvariant (Image Protected Contracts)
attribute [local irreducible] load32

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

/-- Prepare any protected future line/object collection at the completed first
cell. Values originate in firing-entry data and actual trace initialization;
the selected future collection need not be the second cell's collection. -/
theorem prepared (cell : E1M1PathMap.Cell) (lineData : Nat → LineData)
    (lineInput : E1M1NextCallbackReady.Data gun s lines (path thing angle ox oy).trace cell lineData)
    (objectNodes : List E1M1ThingList.Node)
    (objectInput : E1M1ThingListInputs.Data gun s lines (path thing angle ox oy).trace objects objectNodes)
    (objectSafe : ∀ node∈objectNodes, ∀ a∈E1M1ThingGeometry.objectReads node.pointer,
      E1M1FiringMapState.Safe (s.regs 4) lines a)
    (linkSafe : ∀ node∈objectNodes, E1M1FiringMapState.Safe (s.regs 4) lines (node.pointer+(44#32)))
    (traceSafe : ∀ a∈E1M1ThingGeometry.traceReads, E1M1FiringMapState.Safe (s.regs 4) lines a)
    (activeSafe : E1M1FiringMapState.Safe (s.regs 4) lines (0x2c024#32)) :
    let out := E1M1FiringCellReturn.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes
    Image out.core.memory lines (path thing angle ox oy).trace cell lineData objectNodes ∧
    Protected (s.regs 4) lines cell lineData objectNodes ∧
    Contracts (s.regs 4) lines (path thing angle ox oy).trace cell lineData objects objectNodes := by
  let out := E1M1FiringCellReturn.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes
  have read (a : Word) (setup : E1M1PathMapFiring.Safe gun s a)
      (safe : E1M1FiringMapState.Safe (s.regs 4) lines a) :
      load32 out.core.memory a=load32 s.memory a :=
    E1M1FiringCellMemory.firing_frame gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d room a
      ⟨setup,safe.scan.scan,safe.scan.array,safe.caller 116 (by simp),safe.caller 120 (by simp)⟩ safe.objects
  have traceWords := E1M1NextCallbackMemory.trace_words gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d room world dimension ids scene traceSafe
  have keep (a : Word) (safe : E1M1FiringMapState.Safe (s.regs 4) lines a) :=
    E1M1NextCallbackMemory.next_frame gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d room world dimension ids scene a safe
  dsimp only at traceWords
  rw [keep _ (traceSafe _ (by simp [E1M1ThingGeometry.traceReads])),
    keep _ (traceSafe _ (by simp [E1M1ThingGeometry.traceReads])),
    keep _ (traceSafe _ (by simp [E1M1ThingGeometry.traceReads])),
    keep _ (traceSafe _ (by simp [E1M1ThingGeometry.traceReads]))] at traceWords
  have active := E1M1NextCallbackMemory.active gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d room world dimension ids scene activeSafe
  have activeFirst := (keep _ activeSafe).symm.trans active
  refine ⟨⟨traceWords,activeFirst,?_,?_,?_,?_⟩,
    ⟨traceSafe,activeSafe,lineInput.safe,lineInput.backSafe,?_,linkSafe⟩,
    ⟨lineInput.callback,lineInput.computed,input.layout.storage,?_⟩⟩
  · intro i
    exact E1M1NextCallbackMemory.line_words s.memory out.core.memory _ _ _ _ (lineInput.encoded i)
      (fun a ha => read a (lineInput.setup i a ha) (lineInput.safe i a ha))
  · intro i
    rw [read _ (lineInput.backSetup i) (lineInput.backSafe i)]
    exact lineInput.back i
  · intro node member
    have obj (a : Word) (ha : a∈E1M1ThingGeometry.objectReads node.pointer) :=
      read a (objectInput.objectSafe node member a ha).before (objectSafe node member a ha)
    exact ⟨congrArg (fun v => v.1) traceWords,congrArg (fun v => v.2.1) traceWords,
      congrArg (fun v => v.2.2.1) traceWords,congrArg (fun v => v.2.2.2) traceWords,
      (obj _ (by simp [E1M1ThingGeometry.objectReads])).trans (objectInput.objectX node member),
      (obj _ (by simp [E1M1ThingGeometry.objectReads])).trans (objectInput.objectY node member),
      (obj _ (by simp [E1M1ThingGeometry.objectReads])).trans (objectInput.radius node member)⟩
  · exact E1M1ThingList.linked_transport _ _ objectNodes objectInput.linked
      (fun node member => read _ (objectInput.linkSafe node member).before (linkSafe node member))
  · intro node member a ha
    have split : a∈E1M1ThingGeometry.traceReads ∨ a∈E1M1ThingGeometry.objectReads node.pointer := by
      simpa [E1M1ThingVisit.reads,E1M1ThingGeometry.traceReads,E1M1ThingGeometry.objectReads,or_assoc] using ha
    exact split.elim (fun h => traceSafe a h) (fun h => objectSafe node member a h)
  · exact E1M1ThingListInputs.static_layout gun s weapon actor thing angle ox oy xout yout base lines words c w h data input objects objectNodes objectInput
end Firing
end Doom.Proofs.E1M1FiringSceneData
