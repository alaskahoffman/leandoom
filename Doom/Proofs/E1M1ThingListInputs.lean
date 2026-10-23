import Doom.Proofs.E1M1ScanCapacity
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace Doom.Proofs.E1M1ThingListInputs
open Verification X86 X86Memory X86Control BlockSummary
open E1M1ScanMemory (firstScan)
open E1M1ScanGeometry (path)
open E1M1ScanContracts (LineData)
open OriginalThingSecondSide (firstSide lastSide)
abbrev program := E1M1ThingTraversal.program

/-- Pure address separation at the original firing stack position. No reached
machine state, callback result or traversal outcome is a field. -/
structure Storage (sp : Word) (nodes : List E1M1ThingList.Node) : Prop where
  stack : E1M1ThingVisit.StackSafe (sp-(120#32))
  callback : E1M1ThingVisit.ReadSafe (sp-(120#32)) (sp-(120#32))
  caller : E1M1ThingVisit.ReadSafe (sp-(120#32)) (sp-(116#32))
  reads : ∀ node∈nodes, ∀ a∈E1M1ThingVisit.reads node.pointer, E1M1ThingVisit.ReadSafe (sp-(120#32)) a
  link : ∀ node∈nodes, E1M1ThingVisit.ReadSafe (sp-(120#32)) (node.pointer+(44#32))

/-- Initial actor values and links are preserved; the trace is freshly initialized
by firing setup, so its old contents are deliberately not assumed here. -/
structure Data (gun : Fire.Gun) (s : X86Memory.State) (lines : Word)
    (trace : Collision.Divline) (objects : Nat → Word) (nodes : List E1M1ThingList.Node) : Prop where
  objectX : ∀ node∈nodes, load32 s.memory (node.pointer+(12#32))=node.target.x.raw.toBitVec
  objectY : ∀ node∈nodes, load32 s.memory (node.pointer+(16#32))=node.target.y.raw.toBitVec
  radius : ∀ node∈nodes, load32 s.memory (node.pointer+(64#32))=node.target.radius.raw.toBitVec
  objectSafe : ∀ node∈nodes, ∀ a∈E1M1ThingGeometry.objectReads node.pointer, E1M1ThingEntry.ReadSafe gun s lines a
  linked : E1M1ThingList.Linked s.memory nodes
  linkSafe : ∀ node∈nodes, E1M1ThingEntry.ReadSafe gun s lines (node.pointer+(44#32))
  nonzero : ∀ node∈nodes, node.pointer≠(0#32)
  pointer : ∀ node∈nodes, objects node.id=node.pointer
  traceScan : ∀ a∈E1M1ThingGeometry.traceReads, E1M1ThingGeometry.ScanSafe (s.regs 4) lines a
  traceCall : ∀ a∈E1M1ThingGeometry.traceReads, Apart a (s.regs 4-(116#32))
  traceEntry : ∀ a∈E1M1ThingGeometry.traceReads, Apart a (s.regs 4-(120#32))
  storage : Storage (s.regs 4) nodes
  computed : ∀ node∈nodes, firstSide trace node.target≠lastSide trace node.target →
    ∃ frac, Collision.interceptVector trace (OriginalThingFraction.diagonal trace node.target)=.ok frac

section Firing
variable (gun : Fire.Gun) (s : X86Memory.State) (weapon : Weapon.Context)
    (actor : Word) (thing : Collision.SolidThing) (angle : Angle) (ox oy : Fixed)
    (xout yout : Int32 × Fixed × Fixed) (base lines : Word) (words : Array Nat)
    (c : E1M1PathMap.Cell) (w h : Nat) (data : Nat → LineData)
    (input : E1M1FiringScan.Inputs gun s weapon actor thing angle ox oy xout yout base lines words c w h data)
include input
attribute [local irreducible] Collision.SolidThing.attackEndpoint

def boundary := E1M1ThingEntry.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input
def before := (E1M1ScanReturn.finished gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).2

/-- Both collections share one bound supplied on the original candidate lists. -/
theorem capacity (nodes : List E1M1ThingList.Node) (room : c.ids.length+nodes.length≤128) :
    (before gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).collected.size+nodes.length≤128 := by
  have size := E1M1ScanCapacity.finished_size (firstScan gun s).core c.ids.length 0x2ba20
    (E1M1PathMap.resolve lines) (E1M1FiringScan.initial gun s weapon actor thing angle ox oy xout yout base lines words c w h data input)
    (firstScan gun s).flags (path thing angle ox oy).trace
  change (before gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).collected.size≤c.ids.length at size
  omega

theorem all_lines : E1M1ThingFinish.AllLines (before gun s weapon actor thing angle ox oy xout yout base lines words c w h data input) :=
  E1M1ThingFinish.finished_lines (firstScan gun s).core c.ids.length 0x2ba20
    (E1M1PathMap.resolve lines) (E1M1FiringScan.initial gun s weapon actor thing angle ox oy xout yout base lines words c w h data input)
    (firstScan gun s).flags (path thing angle ox oy).trace

variable (returns : E1M1ScanReturn.ReturnSafe (s.regs 4) lines)
    (flag : E1M1ThingGate.FlagSafe (s.regs 4) lines)
include returns

theorem entry_read (a : Word) (safe : E1M1ThingEntry.ReadSafe gun s lines a) :
    load32 (boundary gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).core.memory a=load32 s.memory a := by
  apply (OriginalThingEntry.frame _ a ?_).trans
    (E1M1ThingEntry.call_read gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns a safe)
  rw [E1M1ThingEntry.call_stack gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns]
  simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe.entry

theorem trace_read (a : Word) (scan : E1M1ThingGeometry.ScanSafe (s.regs 4) lines a)
    (call : Apart a (s.regs 4-(116#32))) (entry : Apart a (s.regs 4-(120#32))) :
    load32 (boundary gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).core.memory a=load32 (firstScan gun s).core.memory a := by
  apply (OriginalThingEntry.frame _ a ?_).trans
  · apply (OriginalPathCell.call_frame false _ _ a ?_).trans
      (E1M1ThingGeometry.scan_read gun s weapon actor thing angle ox oy xout yout base lines words c w h data input a scan)
    change Apart a ((E1M1ScanReturn.finished gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).1.core.regs 4-(4#32))
    rw [(E1M1ScanReturn.parent_return gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns).2.1]
    simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using call
  · rw [E1M1ThingEntry.call_stack gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns]
    simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using entry

variable (objects : Nat → Word) (nodes : List E1M1ThingList.Node)
    (d : Data gun s lines (path thing angle ox oy).trace objects nodes)
include d

theorem trace_words :
    let m := (boundary gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).core.memory
    let t := (path thing angle ox oy).trace
    (load32 m 0x2ba10,load32 m 0x2ba14,load32 m 0x2ba18,load32 m 0x2ba1c)=
      (t.x.raw.toBitVec,t.y.raw.toBitVec,t.dx.raw.toBitVec,t.dy.raw.toBitVec) := by
  have keep (a : Word) (ha : a∈E1M1ThingGeometry.traceReads) :=
    trace_read gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns a (d.traceScan a ha) (d.traceCall a ha) (d.traceEntry a ha)
  change (load32 (boundary gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).core.memory _,load32 _ _,load32 _ _,load32 _ _)=_
  rw [keep _ (by simp [E1M1ThingGeometry.traceReads]),keep _ (by simp [E1M1ThingGeometry.traceReads]),
    keep _ (by simp [E1M1ThingGeometry.traceReads]),keep _ (by simp [E1M1ThingGeometry.traceReads])]
  exact E1M1ScanMemory.firing_trace gun s actor thing angle ox oy input.geometry input.traceSafe

theorem geometry (node : E1M1ThingList.Node) (member : node∈nodes) :
    E1M1ThingVisit.Geometry (boundary gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).core.memory (path thing angle ox oy).trace node.pointer node.target := by
  have t := trace_words gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns objects nodes d
  have keep (a : Word) (ha : a∈E1M1ThingGeometry.objectReads node.pointer) :=
    entry_read gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns a (d.objectSafe node member a ha)
  exact ⟨congrArg (fun v => v.1) t,congrArg (fun v => v.2.1) t,
    congrArg (fun v => v.2.2.1) t,congrArg (fun v => v.2.2.2) t,
    (keep _ (by simp [E1M1ThingGeometry.objectReads])).trans (d.objectX node member),
    (keep _ (by simp [E1M1ThingGeometry.objectReads])).trans (d.objectY node member),
    (keep _ (by simp [E1M1ThingGeometry.objectReads])).trans (d.radius node member)⟩

theorem linked : E1M1ThingList.Linked (boundary gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).core.memory nodes := by
  exact E1M1ThingList.linked_transport _ _ nodes d.linked
    (fun node member => entry_read gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns _ (d.linkSafe node member))

omit returns in
theorem static_layout : E1M1ThingList.Layout (s.regs 4-(120#32)) (path thing angle ox oy).trace
    (E1M1ThingFinish.resolve lines objects) nodes := by
  refine ⟨d.storage.stack,d.storage.callback,?_,d.nonzero,?_,d.storage.reads,d.storage.link,d.computed⟩
  · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using d.storage.caller
  · intro node member frac
    simpa [E1M1ThingFinish.resolve] using d.pointer node member
end Firing
end Doom.Proofs.E1M1ThingListInputs
