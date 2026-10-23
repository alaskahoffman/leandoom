import Doom.Proofs.E1M1PathMap
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
namespace Doom.Proofs.E1M1PathMapLookup
open Verification X86 X86Memory X86Control E1M1PathMap

/-- Register/global representation at the original BLOCKMAP lookup entry.
The list cursor and offset word are conclusions, not supplied fields. -/
structure Context (s : X86Memory.State) (base : Word) (x y : Int32) (width : Nat) : Prop where
  xReg : s.regs 0=x.toBitVec
  yReg : s.regs 2=y.toBitVec
  widthReg : s.regs 3=BitVec.ofNat 32 width
  tableGlobal : load32 s.memory 0x2c100=base+(8#32)
  listGlobal : load32 s.memory 0x2c10c=base

/-- The offset table begins four 16-bit words into the lump. Modular addresses
are intentional: this identity also covers unaligned and wrapping images. -/
theorem table_address (base : Word) (index : Nat) :
    base+(8#32)+(BitVec.ofNat 32 index <<< 1)=base+BitVec.ofNat 32 (2*(4+index)) := by
  simp only [Nat.mul_add,BitVec.ofNat_add,BitVec.ofNat_mul]
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  change base+(8#32)+(BitVec.ofNat 32 index)*(2#32)=base+((8#32)+(2#32)*BitVec.ofNat 32 index)
  rw [BitVec.add_assoc,BitVec.mul_comm (BitVec.ofNat 32 index)]

theorem e1m1_index_bound (x y : Int32) (inside : Collision.pathCellInside x y 36 23=true) :
    Collision.pathCellIndex x y 36<828 := by
  simp only [Collision.pathCellInside,Bool.and_eq_true,decide_eq_true_eq] at inside
  unfold Collision.pathCellIndex
  omega

/-- Derive the original lookup's offset read and signed-extension domain from
one certified map cell and its pre-lookup memory image. -/
theorem inputs_from_image (s : X86Memory.State) (base : Word) (words : Array Nat) (c : Cell)
    (x y : Int32) (width height : Nat) (context : Context s base x y width)
    (inside : Collision.pathCellInside x y width height=true)
    (valid : c.Valid words) (image : WordImage s.memory base words)
    (selected : words[4+Collision.pathCellIndex x y width]?=some c.offset) :
    OriginalLineCell.Inputs s x y width c.offset (base+(8#32)) base := by
  simp only [Collision.pathCellInside,Bool.and_eq_true,decide_eq_true_eq] at inside
  refine ⟨inside.1.1.1,inside.1.1.2,context.xReg,context.yReg,context.widthReg,
    context.tableGlobal,context.listGlobal,?_,valid.1⟩
  rw [table_address]
  exact image _ _ selected

/-- The executed lookup establishes the actual scan cursor and preserves the
entire map/geometry/collection memory, SP and the scan-header destination. -/
theorem lookup_ready (s : X86Memory.State) (base : Word) (words : Array Nat) (c : Cell)
    (x y : Int32) (width height : Nat) (context : Context s base x y width)
    (inside : Collision.pathCellInside x y width height=true)
    (valid : c.Valid words) (image : WordImage s.memory base words)
    (selected : words[4+Collision.pathCellIndex x y width]?=some c.offset) :
    (OriginalLineCell.lookup s).core.regs 2=base+BitVec.ofNat 32 (2*c.offset) ∧
    (OriginalLineCell.lookup s).core.memory=s.memory ∧
    (OriginalLineCell.lookup s).core.regs 4=s.regs 4 ∧
    (OriginalLineCell.lookup s).pc=0x2c57f := by
  have h := inputs_from_image s base words c x y width height context inside valid image selected
  exact ⟨by simpa only [Nat.mul_comm] using OriginalLineCell.live_lookup s x y width c.offset (base+(8#32)) base h,
    (OriginalLineCell.lookup_observe s).2⟩

/-- List facts required by the mixed scan, before any valid-count stamp write.
This intentionally does not assert its geometry, storage or seen invariant. -/
structure ScanWords (s : X86Memory.State) (lines : Word) (c : Cell) : Prop where
  items : ∀ i : Fin c.ids.length,
    OriginalLineCell.itemWord (OriginalLineInvariant.atIndex s i.val)=BitVec.ofNat 32 c.ids[i.val]
  nonlast : ∀ i : Fin c.ids.length,
    OriginalLineCell.itemWord (OriginalLineInvariant.atIndex s i.val)≠(0xffffffff#32)
  pointers : ∀ i : Fin c.ids.length, ∀ frac : Fixed,
    OriginalLineDispatch.pointer (OriginalLineInvariant.atIndex s i.val)=resolve lines ⟨frac,true,c.ids[i.val]⟩
  sentinel : load16 s.memory (OriginalLineInvariant.address s c.ids.length)=(0xffff#16)

/-- Eight real original instructions produce the scan-entry list contract.
No reached-state cursor or reached-state map-image premise is required. -/
theorem lookup_to_scan (s : X86Memory.State) (f : Option Flags) (base lines : Word)
    (words : Array Nat) (c : Cell) (x y : Int32) (width height : Nat)
    (context : Context s base x y width) (inside : Collision.pathCellInside x y width height=true)
    (valid : c.Valid words) (image : WordImage s.memory base words)
    (selected : words[4+Collision.pathCellIndex x y width]?=some c.offset)
    (lineBase : load32 s.memory 0x2c120=lines) :
    X86Routine.Prefix OriginalLineCell.program [] 8 ⟨s,f,0x2c541⟩ (OriginalLineCell.lookup s) ∧
    ScanWords (OriginalLineCell.lookup s).core lines c := by
  obtain ⟨cursor,memory,_⟩ := lookup_ready s base words c x y width height context inside valid image selected
  have retained : WordImage (OriginalLineCell.lookup s).core.memory base words := by rw [memory]; exact image
  have lb : load32 (OriginalLineCell.lookup s).core.memory 0x2c120=lines := by rw [memory]; exact lineBase
  refine ⟨OriginalLineCell.lookup_execution s f,?_,?_,?_,?_⟩
  · exact item_from_image _ base words c valid retained cursor
  · exact nonlast_from_image _ base words c valid retained cursor
  · exact pointer_from_image _ base lines words c valid retained cursor lb
  · exact sentinel_from_image _ base words c valid retained cursor

/-- Lookup cannot consume an intercept slot or damage an existing record. -/
theorem lookup_preserves_collection (s : X86Memory.State) (base : Word)
    (resolver : Collision.Intercept → Word) (hits : Array Collision.Intercept) (reserve : Nat)
    (tracked : OriginalLineCollection.Tracks s base resolver hits reserve) :
    OriginalLineCollection.Tracks (OriginalLineCell.lookup s).core base resolver hits reserve := by
  have memory := (OriginalLineCell.lookup_observe s).2.1
  refine ⟨?_,?_,tracked.room⟩
  · change OriginalLineFinish.Encodes (OriginalLineCell.lookup s).core.memory base resolver hits
    rw [memory]
    exact tracked.encoded
  · change load32 (OriginalLineCell.lookup s).core.memory 0x2c028=_
    rw [memory]
    exact tracked.cursor
end Doom.Proofs.E1M1PathMapLookup
