import Doom.Proofs.E1M1AimCellEntry
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
namespace Doom.Proofs.E1M1AimCellStamps
open Verification X86 X86Memory X86Control BlockSummary
open E1M1NoiseAllocation (Region)
open E1M1AimObjectRegions (region)
open E1M1CellWalkInvariant (Context Cell)
open E1M1ScanGeometry (linePointer)

/-- Extra allocation separation needed once collection starts writing stamps.
Read-only vertex/node prefixes may still alias each other. -/
structure Layout (stack : Region) (q : Context) (c : Cell) : Prop where
  input : E1M1AimCellRegions.Layout stack q c
  vertices : ∀ i : Fin c.cell.ids.length,
    (region (c.data i.val).v 8).Disjoint (E1M1AimStaticRegions.linedefs q.lines) ∧
    (region (c.data i.val).w 8).Disjoint (E1M1AimStaticRegions.linedefs q.lines)
  nodes : ∀ node∈c.nodes,
    (region node.pointer 68).Disjoint (E1M1AimStaticRegions.linedefs q.lines)
  heads : (region q.links 3312).Disjoint (E1M1AimStaticRegions.linedefs q.lines)
  globalsStack : E1M1AimStaticRegions.globals.Disjoint stack

theorem line_reads (stack : Region) (q : Context) (c : Cell) (placement : Layout stack q c)
    (i : Fin c.cell.ids.length) (a : Word)
    (member : a∈E1M1ScanMemory.lineReads (linePointer q.lines c.cell.ids[i.val])
      (c.data i.val).v (c.data i.val).w ++ [linePointer q.lines c.cell.ids[i.val]+50]) :
    ∀ j<475, Apart a (OriginalLineVisits.stamp q.lines j) := by
  intro j hj
  have line (off : Nat) (fits : off+4≤54) := E1M1AimStampRegions.line_field
    q.lines c.cell.ids[i.val] j off (placement.input.ids i) hj fits
  have v (off : Nat) (fits : off+4≤8) := E1M1AimStampRegions.external_field q.lines
    (c.data i.val).v 8 off j placement.input.lines.bound (placement.input.vertices i).1.bound
    (placement.vertices i).1 fits hj
  have w (off : Nat) (fits : off+4≤8) := E1M1AimStampRegions.external_field q.lines
    (c.data i.val).w 8 off j placement.input.lines.bound (placement.input.vertices i).2.bound
    (placement.vertices i).2 fits hj
  simp only [E1M1ScanMemory.lineReads,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl)|rfl
  · simpa using line 0 (by decide)
  · exact line 4 (by decide)
  · simpa using v 0 (by decide)
  · exact v 4 (by decide)
  · simpa using w 0 (by decide)
  · exact w 4 (by decide)
  · exact line 8 (by decide)
  · exact line 12 (by decide)
  · exact line 50 (by decide)

/-- Existing line-array/global separation already protects all fixed globals
against stamps; no new pairwise stamp assumptions are necessary. -/
theorem global (stack : Region) (q : Context) (c : Cell) (placement : Layout stack q c)
    (a : Word) (inside : E1M1AimMapRegions.globalStores.Contains a) :
    ∀ j<475, Apart a (OriginalLineVisits.stamp q.lines j) := by
  intro j hj
  exact Region.apart inside (E1M1AimStaticRegions.line_stamp q.lines placement.input.lines.bound j hj)
    placement.input.lines.globalsApart.symm

theorem reads (stack : Region) (q : Context) (c : Cell) (placement : Layout stack q c) :
    ∀ a∈E1M1AimRetryData.cellReads q c, ∀ j<475, Apart a (OriginalLineVisits.stamp q.lines j) := by
  intro a member j hj
  simp only [E1M1AimRetryData.cellReads,List.mem_append] at member
  rcases member with (line|node)|selected
  · obtain ⟨i,_,hi⟩ := List.mem_flatMap.mp line
    exact line_reads stack q c placement i a hi j hj
  · obtain ⟨n,hn,ha⟩ := List.mem_flatMap.mp node
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl|rfl <;>
      exact E1M1AimStampRegions.external_field q.lines n.pointer 68 _ j placement.input.lines.bound
        (placement.input.nodes n hn).bound (placement.nodes n hn) (by decide) hj
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at selected
    rcases selected with rfl|rfl
    · exact global stack q c placement _ (by decide) j hj
    · rw [placement.input.width,E1M1AimCellRegions.head_address]
      have hi := E1M1AimCellRegions.index_bound c.x c.y
        (by simpa only [placement.input.width,placement.input.height] using placement.input.inside)
      exact E1M1AimStampRegions.external_field q.lines q.links 3312 _ j placement.input.lines.bound
        placement.input.heads.bound placement.heads (by omega) hj
end Doom.Proofs.E1M1AimCellStamps
