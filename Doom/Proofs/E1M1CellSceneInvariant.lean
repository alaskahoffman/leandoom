import Doom.Proofs.E1M1FiringNextMap
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1CellSceneInvariant
open Verification X86 X86Memory X86Control BlockSummary
open E1M1ScanContracts (LineData)
open E1M1ScanGeometry (linePointer)
attribute [local irreducible] load32

/-- Persistent callback data, without temporary stack words or an assumed
callback outcome. Any chosen line list and object list may be represented. -/
structure Image (m : Memory) (lines : Word) (trace : Collision.Divline)
    (cell : E1M1PathMap.Cell) (data : Nat → LineData) (nodes : List E1M1ThingList.Node) : Prop where
  traceWords : (load32 m 0x2ba10,load32 m 0x2ba14,load32 m 0x2ba18,load32 m 0x2ba1c)=
    (trace.x.raw.toBitVec,trace.y.raw.toBitVec,trace.dx.raw.toBitVec,trace.dy.raw.toBitVec)
  active : load32 m (0x2c024#32)=0
  encoded : ∀ i : Fin cell.ids.length, E1M1ScanMemory.LineWords m (data i.val).line
    (linePointer lines cell.ids[i.val]) (data i.val).v (data i.val).w
  back : ∀ i : Fin cell.ids.length, load32 m (linePointer lines cell.ids[i.val]+50)=0 ↔ (data i.val).line.back.isNone=true
  geometry : ∀ node∈nodes, E1M1ThingVisit.Geometry m trace node.pointer node.target
  linked : E1M1ThingList.Linked m nodes

structure Protected (sp lines : Word) (cell : E1M1PathMap.Cell)
    (data : Nat → LineData) (nodes : List E1M1ThingList.Node) : Prop where
  trace : ∀ a∈E1M1ThingGeometry.traceReads, E1M1FiringMapState.Safe sp lines a
  active : E1M1FiringMapState.Safe sp lines (0x2c024#32)
  lineWords : ∀ i : Fin cell.ids.length, ∀ a∈E1M1ScanMemory.lineReads
    (linePointer lines cell.ids[i.val]) (data i.val).v (data i.val).w, E1M1FiringMapState.Safe sp lines a
  back : ∀ i : Fin cell.ids.length, E1M1FiringMapState.Safe sp lines (linePointer lines cell.ids[i.val]+50)
  objects : ∀ node∈nodes, ∀ a∈E1M1ThingVisit.reads node.pointer, E1M1FiringMapState.Safe sp lines a
  links : ∀ node∈nodes, E1M1FiringMapState.Safe sp lines (node.pointer+(44#32))

/-- Static callback arithmetic and layouts are independent of reached memory. -/
structure Contracts (sp lines : Word) (trace : Collision.Divline) (cell : E1M1PathMap.Cell)
    (data : Nat → LineData) (objects : Nat → Word) (nodes : List E1M1ThingList.Node) : Prop where
  side : ∀ i : Fin cell.ids.length, ∀ a∈OriginalLineSecondPoint.reads
    (linePointer lines cell.ids[i.val]) (data i.val).v (data i.val).w, E1M1ScanGeometry.SideSafe sp a
  computed : ∀ i : Fin cell.ids.length,
    OriginalLineSecondPoint.firstSide trace (data i.val).line≠OriginalLineSecondPoint.lastSide trace (data i.val).line →
    Collision.interceptVector trace ⟨(data i.val).line.x,(data i.val).line.y,(data i.val).line.dx,(data i.val).line.dy⟩=.ok (data i.val).frac
  storage : E1M1ScanGeometry.Storage sp lines
  objects : E1M1ThingList.Layout (sp-(120#32)) trace (E1M1ThingFinish.resolve lines objects) nodes

/-- The same cell frame preserves arbitrary protected future callback data. -/
theorem transport (m n : Memory) (sp lines : Word) (trace : Collision.Divline)
    (cell : E1M1PathMap.Cell) (data : Nat → LineData) (nodes : List E1M1ThingList.Node)
    (image : Image m lines trace cell data nodes) (safe : Protected sp lines cell data nodes)
    (frame : E1M1CellMapInvariant.Frame sp lines m n) : Image n lines trace cell data nodes := by
  refine ⟨?_,(frame _ safe.active).trans image.active,?_,?_,?_,?_⟩
  · rw [frame _ (safe.trace _ (by simp [E1M1ThingGeometry.traceReads])),
      frame _ (safe.trace _ (by simp [E1M1ThingGeometry.traceReads])),
      frame _ (safe.trace _ (by simp [E1M1ThingGeometry.traceReads])),
      frame _ (safe.trace _ (by simp [E1M1ThingGeometry.traceReads]))]
    exact image.traceWords
  · intro i
    exact E1M1NextCallbackMemory.line_words m n _ _ _ _ (image.encoded i)
      (fun a ha => frame a (safe.lineWords i a ha))
  · intro i
    rw [frame _ (safe.back i)]
    exact image.back i
  · intro node member
    exact E1M1ThingList.geometry_transport m n trace node (image.geometry node member)
      (fun a ha => frame a (safe.objects node member a ha))
  · exact E1M1ThingList.linked_transport m n nodes image.linked (fun node member => frame _ (safe.links node member))

/-- Rebuild all indexed line-callback templates from the persistent image and
actual lookup pointers. The callback stack word must come from the real prologue. -/
theorem lines_ready (s : X86Memory.State) (sp lines : Word) (trace : Collision.Divline)
    (cell : E1M1PathMap.Cell) (data : Nat → LineData) (objects : Nat → Word) (nodes : List E1M1ThingList.Node)
    (image : Image s.memory lines trace cell data nodes)
    (contracts : Contracts sp lines trace cell data objects nodes)
    (stack : s.regs 4=sp-(124#32)) (target : load32 s.memory (s.regs 4)=(0x2c5f0#32))
    (items : E1M1PathMapLookup.ScanWords s lines cell)
    (ids : ∀ i : Fin cell.ids.length, cell.ids[i.val]<475) :
    E1M1NextCallbackReady.Ready s lines trace cell data := by
  refine ⟨target,image.active,?_,image.back,contracts.computed,?_⟩
  · intro i
    exact E1M1ScanGeometry.callback_geometry s sp stack i.val trace _ _ _ _
      (items.pointers i (Fixed.ofInt 0)) image.traceWords (image.encoded i) (contracts.side i)
  · intro i
    exact E1M1ScanGeometry.storage_layout s sp lines stack i.val _ (ids i)
      (items.pointers i (Fixed.ofInt 0)) contracts.storage

/-- Rebuild the object iterator image from persistent geometry/links and the
actual freshly written callback/return words. No saved stack image is carried
unchanged from a previous cell. -/
theorem objects_ready (s : X86Memory.State) (sp lines : Word) (trace : Collision.Divline)
    (cell : E1M1PathMap.Cell) (data : Nat → LineData) (objects : Nat → Word) (nodes : List E1M1ThingList.Node)
    (image : Image s.memory lines trace cell data nodes)
    (contracts : Contracts sp lines trace cell data objects nodes)
    (stack : s.regs 4=sp-(120#32))
    (callback : load32 s.memory (s.regs 4)=(0x2c720#32))
    (caller : load32 s.memory (sp-(116#32))=(0x2cab1#32)) :
    E1M1ThingList.Image s.memory (s.regs 4) trace nodes (0x2cab1#32) ∧
    E1M1ThingList.Layout (s.regs 4) trace (E1M1ThingFinish.resolve lines objects) nodes := by
  refine ⟨⟨callback,?_,image.geometry,image.linked⟩,?_⟩
  · rw [stack]
    simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using caller
  · rw [stack]; exact contracts.objects

/-- The real lookup creates the line callback word anew. Its frame supplies the
persistent image, so line readiness is derived without a reached-memory premise. -/
theorem lookup_ready (s : X86Memory.State) (sp lines : Word) (trace : Collision.Divline)
    (cell : E1M1PathMap.Cell) (data : Nat → LineData) (objects : Nat → Word) (nodes : List E1M1ThingList.Node)
    (image : Image s.memory lines trace cell data nodes)
    (safe : Protected sp lines cell data nodes)
    (contracts : Contracts sp lines trace cell data objects nodes)
    (stack : s.regs 4=sp-(112#32))
    (scanStack : (E1M1PathMapCaller.scan s).core.regs 4=sp-(124#32))
    (items : E1M1PathMapLookup.ScanWords (E1M1PathMapCaller.scan s).core lines cell)
    (ids : ∀ i : Fin cell.ids.length, cell.ids[i.val]<475) :
    let out := E1M1PathMapCaller.scan s
    Image out.core.memory lines trace cell data nodes ∧
    E1M1NextCallbackReady.Ready out.core lines trace cell data := by
  have frame : E1M1CellMapInvariant.Frame sp lines s.memory (E1M1PathMapCaller.scan s).core.memory :=
    fun a ha => E1M1NextCellMemory.caller_frame s a (E1M1FiringMapState.caller_safe s sp lines a stack ha)
  have retained := transport _ _ sp lines trace cell data nodes image safe frame
  have target := E1M1NextCallbackMemory.caller_callback s
  rw [stack] at target
  have callback : load32 (E1M1PathMapCaller.scan s).core.memory
      ((E1M1PathMapCaller.scan s).core.regs 4)=(0x2c5f0#32) := by
    rw [scanStack]
    simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using target
  exact ⟨retained,lines_ready _ sp lines trace cell data objects nodes retained contracts scanStack callback items ids⟩
end Doom.Proofs.E1M1CellSceneInvariant
