import Doom.Proofs.E1M1CellAdvance
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1CellWalkInvariant
open Verification X86 X86Memory X86Control BlockSummary
open E1M1ScanContracts (LineData candidates)
open OriginalLineVisits (Represents stamp)
open E1M1FiringVisitedNext (TailSafe)
attribute [local irreducible] load32

structure Context where
  sp : Word
  base : Word
  lines : Word
  epoch : Word
  words : Array Nat
  width : Nat
  height : Nat
  links : Word
  objects : Nat → Word
  trace : Collision.Divline
  world : Collision.Scene

/-- Pure data for a selected cell; this contains no reached machine state. -/
structure Cell where
  x : Int32
  y : Int32
  cell : E1M1PathMap.Cell
  data : Nat → LineData
  nodes : List E1M1ThingList.Node

def cost (c : Cell) := c.cell.ids.length+c.nodes.length
def instructions (c : Cell) := 89+281*c.cell.ids.length+230*c.nodes.length
def budget (cells : List Cell) := (cells.map cost).sum
def bound (cells : List Cell) := (cells.map instructions).sum

/-- A fixed address condition, independent of the current registers. -/
def CallerSafe (sp a : Word) := ∀ off∈[(116#32),120,124], Apart a (sp-off)

structure Common (q : Context) : Prop where
  mapLayout : E1M1CellMapInvariant.Layout q.sp q.base q.lines q.words
  stamps : E1M1ScanContracts.Stamps q.sp q.lines
  returns : E1M1ScanReturn.ReturnSafe q.sp q.lines
  epochSafe : TailSafe q.sp (0x13580#32)
  stampSafe : ∀ j<475, TailSafe q.sp (stamp q.lines j)
  locals : E1M1GridLocals.Safe q.sp q.lines
  cursor : CallerSafe q.sp (0x2c028#32)
  records : ∀ i<128, ∀ off∈[(0#32),4,8], CallerSafe q.sp (OriginalLineCollection.slot 0x2ba20 i off)
  dimension : q.world.grid.width=q.width

structure Static (q : Context) (c : Cell) : Prop where
  valid : c.cell.Valid q.words
  selected : q.words[4+Collision.pathCellIndex c.x c.y q.width]?=some c.cell.offset
  inside : Collision.pathCellInside c.x c.y q.width q.height=true
  payloadSafe : E1M1CellSceneInvariant.Protected q.sp q.lines c.cell c.data c.nodes
  contracts : E1M1CellSceneInvariant.Contracts q.sp q.lines q.trace c.cell c.data q.objects c.nodes
  layout : E1M1ScanContracts.Layout q.sp (q.base+BitVec.ofNat 32 (2*c.cell.offset)) q.lines c.cell.ids.length
    (candidates q.trace q.lines c.cell.ids c.data)
  selectionSafe : E1M1CellObjectSelection.Protected q.sp q.lines q.links c.x c.y q.width
  sceneIds : q.world.links[Collision.pathCellIndex c.x c.y q.width]?=some (c.nodes.map E1M1ThingList.Node.id).toArray
  scene : ∀ node∈c.nodes, q.world.things[node.id]?=some node.target

/-- Every future cell image is supplied once, in the initial memory. -/
def Images (q : Context) (cells : List Cell) (m : Memory) := ∀ c∈cells,
  E1M1CellSceneInvariant.Image m q.lines q.trace c.cell c.data c.nodes ∧
  E1M1CellObjectSelection.Image m q.links c.x c.y q.width c.nodes

structure State (q : Context) (s : X86Control.State) (r : Collision.PathResult) (seen : Array Bool) : Prop where
  stack : s.core.regs 4=q.sp-(112#32)
  maps : E1M1CellMapInvariant.Image s.core.memory q.sp q.base q.lines q.words q.width q.height
  tracked : OriginalLineCollection.Tracks s.core 0x2ba20 (E1M1ThingFinish.resolve q.lines q.objects) r.collected 0
  represented : Represents s.core.memory q.lines q.epoch seen
  size : seen.size=475

theorem caller_safe (s : X86Memory.State) (sp a : Word) (stack : s.regs 4=sp-(112#32))
    (safe : CallerSafe sp a) : E1M1PathMapCaller.Safe s a := by
  unfold E1M1PathMapCaller.Safe
  rw [stack]
  exact ⟨by simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe 116 (by simp),
    by simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe 120 (by simp),
    by simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe 124 (by simp)⟩

/-- One scan's frame preserves all remaining images, not just its own cell. -/
theorem images_transport (q : Context) (cells : List Cell) (m n : Memory)
    (statics : ∀ c∈cells, Static q c) (images : Images q cells m)
    (frame : E1M1CellMapInvariant.Frame q.sp q.lines m n) : Images q cells n := by
  intro c member
  exact ⟨E1M1CellSceneInvariant.transport m n q.sp q.lines q.trace c.cell c.data c.nodes
      (images c member).1 (statics c member).payloadSafe frame,
    E1M1CellObjectSelection.transport m n q.sp q.lines q.links c.x c.y q.width c.nodes
      (images c member).2 (statics c member).selectionSafe frame⟩

/-- Deduct the cell's candidates from one traversal-wide budget; no refill. -/
theorem budget_tail (c : Cell) (rest : List Cell) (before after : Nat)
    (room : before+budget (c::rest)≤128) (used : after≤before+cost c) :
    before+cost c≤128 ∧ after+budget rest≤128 := by
  simp only [budget,List.map_cons,List.sum_cons] at room ⊢
  omega
end Doom.Proofs.E1M1CellWalkInvariant
