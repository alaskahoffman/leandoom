import Doom.Proofs.E1M1FiringNextSuffix
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1NextCallbackMemory
open Verification X86 X86Memory X86Control BlockSummary
open E1M1ScanGeometry (path linePointer)
open E1M1ScanContracts (LineData)
open E1M1ScanMemory (firstScan LineWords lineReads)
attribute [local irreducible] load32

/-- Transport the actual line and both vertices, including wrapping endpoint sums. -/
theorem line_words (m n : Memory) (line : Collision.Line) (p v w : Word)
    (encoded : LineWords m line p v w)
    (keep : ∀ a∈lineReads p v w, load32 n a=load32 m a) :
    LineWords n line p v w := by
  exact ⟨(keep _ (by simp [lineReads])).trans encoded.vertex1,
    (keep _ (by simp [lineReads])).trans encoded.vertex2,
    (keep _ (by simp [lineReads])).trans encoded.x1,
    (keep _ (by simp [lineReads])).trans encoded.y1,
    (keep _ (by simp [lineReads])).trans encoded.x2,
    (keep _ (by simp [lineReads])).trans encoded.y2,
    (keep _ (by simp [lineReads])).trans encoded.dx,
    (keep _ (by simp [lineReads])).trans encoded.dy⟩

/-- CALL and the iterator prologue write the callback address afresh. -/
theorem caller_callback (s : X86Memory.State) :
    load32 (E1M1PathMapCaller.scan s).core.memory (s.regs 4-(12#32))=(0x2c5f0#32) := by
  have mem : (E1M1PathMapCaller.scan s).core.memory=(OriginalLineBounds.entry (E1M1PathMapCaller.call s).core).memory :=
    (OriginalLineCell.lookup_observe _).2.1.trans (E1M1PathMapBounds.result_memory _)
  rw [mem]
  have addr : (E1M1PathMapCaller.call s).core.regs 4-(8#32)=s.regs 4-(12#32) := by
    rw [E1M1PathMapCaller.call_stack]
    simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  rw [←addr]
  change load32 (store32 _ ((E1M1PathMapCaller.call s).core.regs 4-(8#32))
    ((E1M1PathMapCaller.call s).core.regs 3)) _=_
  rw [load_store]
  exact (OriginalPathCell.call_inputs true s (OriginalPathCell.gateFlags true s)).2.2.1

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

/-- The grid advance and next lookup preserve words protected at the original SP. -/
theorem next_frame (a : Word) (safe : E1M1FiringMapState.Safe (s.regs 4) lines a) :
    load32 (E1M1FiringNextScan.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes).core.memory a=
      load32 (E1M1FiringCellReturn.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes).core.memory a := by
  have sp := (E1M1FiringCellReturn.execution gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d room world dimension ids scene none).2.2.1
  exact E1M1NextCellMemory.frame _ a
    (E1M1FiringVisitedNext.next_safe _ _ a sp ⟨safe.caller,safe.objects,safe.advance⟩)

/-- Immutable data comes from firing entry, through both scans and the next lookup. -/
theorem firing_frame (a : Word) (setup : E1M1PathMapFiring.Safe gun s a)
    (safe : E1M1FiringMapState.Safe (s.regs 4) lines a) :
    load32 (E1M1FiringNextScan.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes).core.memory a=load32 s.memory a := by
  exact (next_frame gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d room world dimension ids scene a safe).trans
    (E1M1FiringCellMemory.firing_frame gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d room a
      ⟨setup,safe.scan.scan,safe.scan.array,safe.caller 116 (by simp),safe.caller 120 (by simp)⟩ safe.objects)

/-- Initialized globals retain their new values, rather than pre-firing contents. -/
theorem initialized_frame (a : Word) (safe : E1M1FiringMapState.Safe (s.regs 4) lines a) :
    load32 (E1M1FiringNextScan.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes).core.memory a=load32 (firstScan gun s).core.memory a := by
  exact (next_frame gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d room world dimension ids scene a safe).trans
    ((E1M1FiringCellMemory.after_lines_frame gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d room a
      (safe.caller 116 (by simp)) (safe.caller 120 (by simp)) safe.objects).trans
      (E1M1ThingGeometry.scan_read gun s weapon actor thing angle ox oy xout yout base lines words c w h data input a safe.scan))

theorem trace_words (safe : ∀ a∈E1M1ThingGeometry.traceReads,
    E1M1FiringMapState.Safe (s.regs 4) lines a) :
    let m := (E1M1FiringNextScan.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes).core.memory
    let t := (path thing angle ox oy).trace
    (load32 m 0x2ba10,load32 m 0x2ba14,load32 m 0x2ba18,load32 m 0x2ba1c)=
      (t.x.raw.toBitVec,t.y.raw.toBitVec,t.dx.raw.toBitVec,t.dy.raw.toBitVec) := by
  have keep (a : Word) (ha : a∈E1M1ThingGeometry.traceReads) := initialized_frame gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d room world dimension ids scene a (safe a ha)
  change (load32 (E1M1FiringNextScan.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes).core.memory _,load32 _ _,load32 _ _,load32 _ _)=_
  rw [keep _ (by simp [E1M1ThingGeometry.traceReads]),keep _ (by simp [E1M1ThingGeometry.traceReads]),
    keep _ (by simp [E1M1ThingGeometry.traceReads]),keep _ (by simp [E1M1ThingGeometry.traceReads])]
  exact E1M1ScanMemory.firing_trace gun s actor thing angle ox oy input.geometry input.traceSafe

theorem active (safe : E1M1FiringMapState.Safe (s.regs 4) lines (0x2c024#32)) :
    load32 (E1M1FiringNextScan.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes).core.memory 0x2c024=0 :=
  (initialized_frame gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d room world dimension ids scene _ safe).trans
    (E1M1ScanContracts.firing_active gun s actor thing angle ox oy input.geometry input.activeSafe)

theorem callback_word :
    load32 (E1M1FiringNextScan.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes).core.memory (s.regs 4-(124#32))=(0x2c5f0#32) := by
  have sp := (E1M1FiringCellReturn.execution gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d room world dimension ids scene none).2.2.1
  have stored := caller_callback (E1M1NextCellMemory.advanced (E1M1FiringCellReturn.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes).core)
  rw [E1M1NextCellMemory.stack,sp] at stored
  simpa [E1M1FiringNextScan.result,BitVec.sub_eq_add_neg,BitVec.add_assoc] using stored
end Firing
end Doom.Proofs.E1M1NextCallbackMemory
