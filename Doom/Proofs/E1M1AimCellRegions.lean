import Doom.Proofs.E1M1AimCollectionEntry
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
namespace Doom.Proofs.E1M1AimCellRegions
open Verification X86 X86Memory X86Control BlockSummary
open E1M1NoiseAllocation (Region)
open E1M1AimObjectRegions (Storage Located region field)
open E1M1CellWalkInvariant (Context Cell)
open E1M1ScanGeometry (linePointer)

/-- The signed guard for the pinned 36 by 23 grid bounds every selected head. -/
theorem index_bound (x y : Int32) (inside : Collision.pathCellInside x y 36 23=true) :
    Collision.pathCellIndex x y 36 < 828 := by
  simp [Collision.pathCellInside] at inside
  unfold Collision.pathCellIndex
  omega

/-- Every block-list head occupies one complete word in the 828-entry table. -/
theorem head_address (links : Word) (x y : Int32) :
    E1M1CellObjectSelection.address links x y 36 =
      links+BitVec.ofNat 32 (4*Collision.pathCellIndex x y 36) := by
  unfold E1M1CellObjectSelection.address
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft,Nat.shiftLeft_eq,Nat.mul_mod,Nat.mul_comm]

theorem head_located (stack : Region) (links : Word) (x y : Int32)
    (storage : Storage stack links 3312) (inside : Collision.pathCellInside x y 36 23=true) :
    Located stack (E1M1CellObjectSelection.address links x y 36) := by
  rw [head_address]
  exact field stack links 3312 _ storage (by have := index_bound x y inside; omega)

/-- The whole line-array allocation supplies each bounded line's read prefix. -/
theorem line_located (stack : Region) (lines : Word) (i off : Nat)
    (storage : Storage stack lines (475*62)) (bounded : i<475) (fits : off+4≤54) :
    Located stack (linePointer lines i+BitVec.ofNat 32 off) := by
  have address : linePointer lines i+BitVec.ofNat 32 off=lines+BitVec.ofNat 32 (62*i+off) := by
    simp only [linePointer,BitVec.ofNat_add,BitVec.ofNat_mul]
    rw [BitVec.mul_comm (BitVec.ofNat 32 i)]
    ac_rfl
  rw [address]
  exact field stack lines (475*62) _ storage (by omega)

/-- Read prefixes and separation, not a claim that live DOS allocations have
already been established. Vertex and actor read-only prefixes may alias. -/
structure Layout (stack : Region) (q : Context) (c : Cell) : Prop where
  width : q.width=36
  height : q.height=23
  inside : Collision.pathCellInside c.x c.y q.width q.height=true
  lines : Storage stack q.lines (475*62)
  ids : ∀ i : Fin c.cell.ids.length, c.cell.ids[i.val]<475
  vertices : ∀ i : Fin c.cell.ids.length,
    Storage stack (c.data i.val).v 8 ∧ Storage stack (c.data i.val).w 8
  nodes : ∀ node∈c.nodes, Storage stack node.pointer 68
  heads : Storage stack q.links 3312
  globalStack : (region 0x2c0f8 4).Disjoint stack

theorem line_reads (stack : Region) (q : Context) (c : Cell) (placement : Layout stack q c)
    (i : Fin c.cell.ids.length) :
    ∀ a∈E1M1ScanMemory.lineReads (linePointer q.lines c.cell.ids[i.val])
      (c.data i.val).v (c.data i.val).w ++ [linePointer q.lines c.cell.ids[i.val]+50],
      Located stack a := by
  intro a member
  simp only [E1M1ScanMemory.lineReads,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl)|rfl
  · simpa using line_located stack q.lines _ 0 placement.lines (placement.ids i) (by decide)
  · exact line_located stack q.lines _ 4 placement.lines (placement.ids i) (by decide)
  · simpa using field stack _ 8 0 (placement.vertices i).1 (by decide)
  · exact field stack _ 8 4 (placement.vertices i).1 (by decide)
  · simpa using field stack _ 8 0 (placement.vertices i).2 (by decide)
  · exact field stack _ 8 4 (placement.vertices i).2 (by decide)
  · exact line_located stack q.lines _ 8 placement.lines (placement.ids i) (by decide)
  · exact line_located stack q.lines _ 12 placement.lines (placement.ids i) (by decide)
  · exact line_located stack q.lines _ 50 placement.lines (placement.ids i) (by decide)

theorem node_reads (stack : Region) (q : Context) (c : Cell) (placement : Layout stack q c)
    (node : E1M1ThingList.Node) (member : node∈c.nodes) :
    ∀ a∈[node.pointer+12,node.pointer+16,node.pointer+64,node.pointer+44], Located stack a := by
  intro a ha
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl <;> exact field stack node.pointer 68 _ (placement.nodes node member) (by decide)

/-- The one fixed input global lies within the broad write envelope but is not
itself a setup write; treat it exactly instead of requiring impossible separation. -/
theorem reads (stack : Region) (q : Context) (c : Cell) (placement : Layout stack q c) :
    ∀ a∈E1M1AimRetryData.cellReads q c, Located stack a ∨ a=(0x2c0f8#32) := by
  intro a member
  simp only [E1M1AimRetryData.cellReads,List.mem_append] at member
  rcases member with (line|node)|selected
  · obtain ⟨i,_,hi⟩ := List.mem_flatMap.mp line
    exact Or.inl (line_reads stack q c placement i a hi)
  · obtain ⟨node,hn,ha⟩ := List.mem_flatMap.mp node
    exact Or.inl (node_reads stack q c placement node hn a ha)
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at selected
    rcases selected with rfl|rfl
    · exact Or.inr rfl
    · apply Or.inl
      rw [placement.width]
      exact head_located stack q.links c.x c.y placement.heads
        (by simpa only [placement.width,placement.height] using placement.inside)

theorem covered (stack : Region) (q : Context) (c : Cell) (placement : Layout stack q c) :
    E1M1AimRegions.Covered stack (E1M1AimRetryData.cellReads q c) := by
  intro a member
  rcases reads stack q c placement a member with located|rfl
  · obtain ⟨r,inside,apartStack,_⟩ := located
    exact ⟨r,inside,apartStack⟩
  · exact ⟨region 0x2c0f8 4,by decide,placement.globalStack⟩
end Doom.Proofs.E1M1AimCellRegions
