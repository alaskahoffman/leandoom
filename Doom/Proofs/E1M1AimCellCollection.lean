import Doom.Proofs.E1M1AimCellWalk
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
namespace Doom.Proofs.E1M1AimCellCollection
open Verification X86 X86Memory X86Control BlockSummary
open E1M1NoiseAllocation (Region)
open E1M1CellWalkInvariant (Context Cell)
open E1M1AimCellStamps (Layout)

/-- Any existing collection frame now preserves the entire cell payload with
its per-word protection derived from placement. The execution frame is retained. -/
theorem payload (stack : Region) (q : Context) (c : Cell) (m n : Memory)
    (placement : Layout stack q c) (reserve : E1M1AimWalkRegions.Reserve stack q.sp)
    (before : E1M1QueryImages.Payload m q c) (frame : E1M1CellMapInvariant.Frame q.sp q.lines m n) :
    E1M1QueryImages.Payload n q c := by
  exact E1M1AimRetryData.payload m n q c before
    (fun a ha => frame a (E1M1AimCellWalk.reads_safe stack q c placement reserve a ha))

/-- Transport all future cell images across one collection frame, without
requiring their unrelated arithmetic, capacity or caller-layout contracts. -/
theorem images (stack : Region) (q : Context) (cells : List Cell) (m n : Memory)
    (placement : ∀ c∈cells, Layout stack q c) (reserve : E1M1AimWalkRegions.Reserve stack q.sp)
    (before : E1M1CellWalkInvariant.Images q cells m)
    (frame : E1M1CellMapInvariant.Frame q.sp q.lines m n) :
    E1M1CellWalkInvariant.Images q cells n := by
  intro c member
  exact ⟨E1M1CellSceneInvariant.transport m n q.sp q.lines q.trace c.cell c.data c.nodes
      (before c member).1 (E1M1AimCellWalk.scene_safe stack q c (placement c member) reserve) frame,
    E1M1CellObjectSelection.transport m n q.sp q.lines q.links c.x c.y q.width c.nodes
      (before c member).2 (E1M1AimCellWalk.selection_safe stack q c (placement c member) reserve) frame⟩

/-- Connect derived protection to the actual original line lookup and its fresh
callback word. Existing numeric contracts and actual scan pointers remain. -/
theorem lookup_ready (stackRegion : Region) (s : X86Memory.State) (q : Context) (c : Cell)
    (placement : Layout stackRegion q c) (reserve : E1M1AimWalkRegions.Reserve stackRegion q.sp)
    (image : E1M1CellSceneInvariant.Image s.memory q.lines q.trace c.cell c.data c.nodes)
    (contracts : E1M1CellSceneInvariant.Contracts q.sp q.lines q.trace c.cell c.data q.objects c.nodes)
    (stack : s.regs 4=q.sp-(112#32))
    (scanStack : (E1M1PathMapCaller.scan s).core.regs 4=q.sp-(124#32))
    (items : E1M1PathMapLookup.ScanWords (E1M1PathMapCaller.scan s).core q.lines c.cell) :
    let out := E1M1PathMapCaller.scan s
    E1M1CellSceneInvariant.Image out.core.memory q.lines q.trace c.cell c.data c.nodes ∧
    E1M1NextCallbackReady.Ready out.core q.lines q.trace c.cell c.data := by
  exact E1M1CellSceneInvariant.lookup_ready s q.sp q.lines q.trace c.cell c.data q.objects c.nodes
    image (E1M1AimCellWalk.scene_safe stackRegion q c placement reserve) contracts stack scanStack items
    placement.input.ids

/-- Original setup followed by an existing collection frame preserves the
initial payload; neither boundary's payload is independently assumed. -/
theorem setup_then_collection (stack : Region) (s : X86Memory.State) (q : Context) (c : Cell) (n : Memory)
    (placement : Layout stack q c) (setupReserve : E1M1AimSetupFootprint.Reserve stack s)
    (walkReserve : E1M1AimWalkRegions.Reserve stack q.sp)
    (before : E1M1QueryImages.Payload s.memory q c)
    (frame : E1M1CellMapInvariant.Frame q.sp q.lines (E1M1PathMapQuery.traversal s).core.memory n) :
    E1M1QueryImages.Payload n q c := by
  exact payload stack q c _ n placement walkReserve
    (E1M1AimCellEntry.traversal stack s q c setupReserve placement.input before).1 frame
end Doom.Proofs.E1M1AimCellCollection
