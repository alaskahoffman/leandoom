import Doom.Proofs.E1M1QuerySource
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1QueryImages
open Verification X86 X86Memory X86Control BlockSummary
open E1M1CellWalkInvariant (Context Cell)
open E1M1PathMapSetup (grid Safe StackSafe)
open E1M1ScanGeometry (linePointer)
attribute [local irreducible] load32

/-- Existing map/object data only. Trace words and active flags are deliberately
absent: initialization writes those, rather than preserving their old values. -/
structure Payload (m : Memory) (q : Context) (c : Cell) : Prop where
  encoded : ∀ i : Fin c.cell.ids.length, E1M1ScanMemory.LineWords m (c.data i.val).line
    (linePointer q.lines c.cell.ids[i.val]) (c.data i.val).v (c.data i.val).w
  back : ∀ i : Fin c.cell.ids.length, load32 m (linePointer q.lines c.cell.ids[i.val]+50)=0 ↔ (c.data i.val).line.back.isNone=true
  objects : ∀ node∈c.nodes,
    (load32 m (node.pointer+12),load32 m (node.pointer+16),load32 m (node.pointer+64))=
    (node.target.x.raw.toBitVec,node.target.y.raw.toBitVec,node.target.radius.raw.toBitVec)
  linked : E1M1ThingList.Linked m c.nodes
  selection : E1M1CellObjectSelection.Image m q.links c.x c.y q.width c.nodes

structure Protected (s : X86Memory.State) (q : Context) (c : Cell) : Prop where
  lines : ∀ i : Fin c.cell.ids.length, ∀ a∈E1M1ScanMemory.lineReads
    (linePointer q.lines c.cell.ids[i.val]) (c.data i.val).v (c.data i.val).w, Safe s a
  back : ∀ i : Fin c.cell.ids.length, Safe s (linePointer q.lines c.cell.ids[i.val]+50)
  objects : ∀ node∈c.nodes, ∀ off∈[(12#32),16,64], Safe s (node.pointer+off)
  links : ∀ node∈c.nodes, Safe s (node.pointer+44)
  global : Safe s 0x2c0f8
  selected : Safe s (E1M1CellObjectSelection.address q.links c.x c.y q.width)

/-- Initialization supplies the new trace and disables early-out for aiming;
only the subsequent axis setup must preserve these freshly written globals. -/
theorem globals (s : X86Memory.State) (ox oy sx sy ex ey : Fixed)
    (geometry : OriginalPathInit.Inputs s ox oy sx sy ex ey)
    (options : load32 s.memory (s.regs 4+4)=3)
    (traceSafe : ∀ a∈E1M1ThingGeometry.traceReads, StackSafe (s.regs 4-60) a)
    (activeSafe : StackSafe (s.regs 4-60) 0x2c024) :
    let p := Collision.pathStart ox oy sx sy ex ey
    (load32 (grid s).core.memory 0x2ba10,load32 (grid s).core.memory 0x2ba14,
      load32 (grid s).core.memory 0x2ba18,load32 (grid s).core.memory 0x2ba1c)=
      (p.trace.x.raw.toBitVec,p.trace.y.raw.toBitVec,p.trace.dx.raw.toBitVec,p.trace.dy.raw.toBitVec) ∧
    load32 (grid s).core.memory 0x2c024=0 := by
  have init := OriginalPathInit.ready s ox oy sx sy ex ey geometry
  have keep (a : Word) (safe : StackSafe (s.regs 4-60) a) :
      load32 (grid s).core.memory a=load32 (OriginalPathInit.result s).core.memory a :=
    E1M1PathMapSetup.after_frame _ a (by rw [init.stack]; exact safe)
  constructor
  · rw [keep _ (traceSafe _ (by simp [E1M1ThingGeometry.traceReads])),
        keep _ (traceSafe _ (by simp [E1M1ThingGeometry.traceReads])),
        keep _ (traceSafe _ (by simp [E1M1ThingGeometry.traceReads])),
        keep _ (traceSafe _ (by simp [E1M1ThingGeometry.traceReads]))]
    exact init.trace
  · rw [keep _ activeSafe]
    have active := congrArg (fun v => v.2.1) init.globals
    calc
      _ = (3 : Word) &&& 4 := by simpa only [options] using active
      _ = 0 := by decide

/-- Map data and the caller's actual aiming options survive initialization. -/
theorem map (s : X86Memory.State) (q : Context) (ox oy sx sy ex ey : Fixed)
    (geometry : OriginalPathInit.Inputs s ox oy sx sy ex ey)
    (stack : s.regs 4=q.sp-52) (options : load32 s.memory (s.regs 4+4)=3)
    (flagSafe : Safe s (E1M1ThingGate.flagWord q.sp))
    (input : E1M1PathMapSetup.MapInputs s q.base q.lines q.words q.width q.height) :
    E1M1CellMapInvariant.Image (grid s).core.memory q.sp q.base q.lines q.words q.width q.height := by
  obtain ⟨dims,values,encoded,_⟩ := E1M1PathMapSetup.map_at_grid s ox oy sx sy ex ey geometry
    q.base q.lines q.words q.width q.height input
  refine ⟨dims.width,dims.height,dims.widthBound,dims.heightBound,
    values.table,values.lists,values.lines,encoded,?_⟩
  rw [E1M1PathMapSetup.grid_frame s ox oy sx sy ex ey geometry _ flagSafe]
  have address : s.regs 4+4=E1M1ThingGate.flagWord q.sp := by
    rw [stack]; simp [E1M1ThingGate.flagWord,BitVec.sub_eq_add_neg,BitVec.add_assoc]
  rw [←address]; exact options

/-- Rebuild callback images from initialized globals and protected entry data. -/
theorem cell (s : X86Memory.State) (q : Context) (c : Cell) (ox oy sx sy ex ey : Fixed)
    (geometry : OriginalPathInit.Inputs s ox oy sx sy ex ey)
    (trace : q.trace=(Collision.pathStart ox oy sx sy ex ey).trace)
    (options : load32 s.memory (s.regs 4+4)=3)
    (traceSafe : ∀ a∈E1M1ThingGeometry.traceReads, StackSafe (s.regs 4-60) a)
    (activeSafe : StackSafe (s.regs 4-60) 0x2c024)
    (payload : Payload s.memory q c) (safe : Protected s q c) :
    E1M1CellSceneInvariant.Image (grid s).core.memory q.lines q.trace c.cell c.data c.nodes ∧
    E1M1CellObjectSelection.Image (grid s).core.memory q.links c.x c.y q.width c.nodes := by
  have init := globals s ox oy sx sy ex ey geometry options traceSafe activeSafe
  dsimp only at init
  rw [←trace] at init
  have keep (a : Word) (safe : Safe s a) := E1M1PathMapSetup.grid_frame s ox oy sx sy ex ey geometry a safe
  refine ⟨⟨init.1,init.2,?_,?_,?_,?_⟩,⟨(keep _ safe.global).trans payload.selection.global,
    (keep _ safe.selected).trans payload.selection.selected⟩⟩
  · intro i
    exact E1M1NextCallbackMemory.line_words _ _ _ _ _ _ (payload.encoded i)
      (fun a ha => keep a (safe.lines i a ha))
  · intro i; rw [keep _ (safe.back i)]; exact payload.back i
  · intro node member
    refine ⟨congrArg (fun v => v.1) init.1,congrArg (fun v => v.2.1) init.1,
      congrArg (fun v => v.2.2.1) init.1,congrArg (fun v => v.2.2.2) init.1,?_,?_,?_⟩
    · exact (keep _ (safe.objects node member _ (by simp))).trans (congrArg (fun v => v.1) (payload.objects node member))
    · exact (keep _ (safe.objects node member _ (by simp))).trans (congrArg (fun v => v.2.1) (payload.objects node member))
    · exact (keep _ (safe.objects node member _ (by simp))).trans (congrArg (fun v => v.2.2) (payload.objects node member))
  · exact E1M1ThingList.linked_transport _ _ _ payload.linked (fun node member => keep _ (safe.links node member))

/-- Outside cells require no entry payload; every used inside image is derived. -/
theorem images (s : X86Memory.State) (q : Context) (cells : List Cell) (ox oy sx sy ex ey : Fixed)
    (geometry : OriginalPathInit.Inputs s ox oy sx sy ex ey)
    (trace : q.trace=(Collision.pathStart ox oy sx sy ex ey).trace)
    (options : load32 s.memory (s.regs 4+4)=3)
    (traceSafe : ∀ a∈E1M1ThingGeometry.traceReads, StackSafe (s.regs 4-60) a)
    (activeSafe : StackSafe (s.regs 4-60) 0x2c024)
    (payloads : ∀ c∈cells, E1M1MixedCellWalk.inside q c=true → Payload s.memory q c ∧ Protected s q c) :
    E1M1MixedCellWalk.Images q cells (grid s).core.memory := by
  intro c member yes d hd
  have eq := List.mem_singleton.mp hd
  subst d
  exact cell s q c ox oy sx sy ex ey geometry trace options traceSafe activeSafe
    (payloads c member yes).1 (payloads c member yes).2
end Doom.Proofs.E1M1QueryImages
