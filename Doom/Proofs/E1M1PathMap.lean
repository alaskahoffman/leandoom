import Doom.Proofs.OriginalLineScan
import Doom.Proofs.OriginalPathInit
set_option maxRecDepth 32768
namespace Doom.Proofs.E1M1PathMap
open Verification X86 X86Memory X86Control

/-- Entries include the original iterator's leading zero, without deduplication. -/
structure Cell where
  offset : Nat
  ids : List Nat
  deriving Repr, DecidableEq

/-- A cell is checked against the raw BLOCKMAP words, including its terminator. -/
def Cell.Valid (words : Array Nat) (c : Cell) : Prop :=
  c.offset < 32768 ∧ c.ids.head? = some 0 ∧ c.ids.length ≤ 13 ∧
  (∀ i : Fin c.ids.length, c.ids[i.val] < 475 ∧
    words[c.offset+i.val]? = some c.ids[i.val]) ∧
  words[c.offset+c.ids.length]? = some 65535
instance (words : Array Nat) (c : Cell) : Decidable (c.Valid words) := inferInstanceAs (Decidable (_ ∧ _))

/-- Linear certificate format: each original list occupies its exact contiguous
slice of the raw BLOCKMAP payload, including the trailing sentinel. -/
def payload (cells : List Cell) : List Nat := cells.flatMap (fun c => c.ids ++ [65535])

def checkSequence (start : Nat) : List Cell → Bool
  | [] => true
  | c::cs => decide (c.offset=start ∧ c.offset<32768 ∧ c.ids.head?=some 0 ∧
      c.ids.length≤13 ∧ ∀ id∈c.ids, id<475) && checkSequence (start+c.ids.length+1) cs

/-- Sequential decoding avoids repeated kernel evaluation of large indexed
arrays; it establishes exactly the same per-cell memory contract. -/
theorem sequence_valid (words : Array Nat) (start : Nat) (cells : List Cell)
    (encoded : words.toList.drop start=payload cells) (checked : checkSequence start cells=true) :
    ∀ c∈cells, c.Valid words := by
  induction cells generalizing start with
  | nil => simp
  | cons c cs ih =>
    simp only [checkSequence,Bool.and_eq_true] at checked
    obtain ⟨head,tail⟩ := checked
    obtain ⟨offset,bound,zero,room,ids⟩ := of_decide_eq_true head
    have image : words.toList.drop start=c.ids ++ (65535 :: payload cs) := by
      simpa [payload,List.append_assoc] using encoded
    have after := congrArg (List.drop (c.ids.length+1)) encoded
    have suffix : words.toList.drop (start+c.ids.length+1)=payload cs := by
      simpa only [payload,List.flatMap_cons,←List.length_append,
        show (1 : Nat)=[65535].length from rfl,List.drop_left,List.drop_drop,Nat.add_assoc] using after
    have rest := ih _ suffix tail
    intro x mem
    rcases List.mem_cons.mp mem with eq|mem
    · subst x
      refine ⟨bound,zero,room,?_,?_⟩
      · intro i
        refine ⟨ids _ (List.getElem_mem i.isLt),?_⟩
        have read := congrArg (fun xs : List Nat => xs[i.val]?) image
        simpa only [List.getElem?_drop,Array.getElem?_toList,
          List.getElem?_append_left i.isLt,List.getElem?_eq_getElem i.isLt,offset] using read
      · have read := congrArg (fun xs : List Nat => xs[c.ids.length]?) image
        simpa only [List.getElem?_drop,Array.getElem?_toList,
          List.getElem?_append_right (Nat.le_refl _),Nat.sub_self,List.getElem?_cons_zero,offset] using read
    · exact rest x mem

/-- The live loop prepends the dummy zero omitted by its parsed cell array.
No sorting or deduplication is permitted by this equality. -/
theorem live_visits (words : Array Nat) (c : Cell) (valid : c.Valid words) :
    #[0] ++ c.ids.tail.toArray = c.ids.toArray := by
  have head := valid.2.1
  cases ids : c.ids with
  | nil => simp [ids] at head
  | cons x xs =>
    simp only [ids,List.head?_cons,Option.some.injEq] at head
    subst x
    simp

/-- This is a representation premise, not a proved WAD allocator/loader. -/
def WordImage (memory : Memory) (base : Word) (words : Array Nat) : Prop :=
  ∀ i value, words[i]? = some value →
    load16 memory (base+BitVec.ofNat 32 (2*i)) = BitVec.ofNat 16 value

def resolve (base : Word) (hit : Collision.Intercept) : Word :=
  BitVec.ofNat 32 hit.id * 62 + base

theorem address_from_list (s : X86Memory.State) (base : Word) (c : Cell)
    (cursor : s.regs 2=base+BitVec.ofNat 32 (2*c.offset)) (i : Nat) :
    OriginalLineInvariant.address s i=base+BitVec.ofNat 32 (2*(c.offset+i)) := by
  simp only [OriginalLineInvariant.address,cursor,Nat.mul_add,BitVec.ofNat_add,BitVec.add_assoc]

theorem item_from_image (s : X86Memory.State) (base : Word) (words : Array Nat) (c : Cell)
    (valid : c.Valid words) (image : WordImage s.memory base words)
    (cursor : s.regs 2=base+BitVec.ofNat 32 (2*c.offset)) (i : Fin c.ids.length) :
    OriginalLineCell.itemWord (OriginalLineInvariant.atIndex s i.val)=BitVec.ofNat 32 c.ids[i.val] := by
  have bound := (valid.2.2.2.1 i).1
  have read := image _ _ (valid.2.2.2.1 i).2
  rw [←address_from_list s base c cursor i.val] at read
  change (load16 s.memory (OriginalLineInvariant.address s i.val)).signExtend 32=_
  rw [read,OriginalLineCell.short_nonnegative _ (by omega)]

theorem nonlast_from_image (s : X86Memory.State) (base : Word) (words : Array Nat) (c : Cell)
    (valid : c.Valid words) (image : WordImage s.memory base words)
    (cursor : s.regs 2=base+BitVec.ofNat 32 (2*c.offset)) (i : Fin c.ids.length) :
    OriginalLineCell.itemWord (OriginalLineInvariant.atIndex s i.val)≠(0xffffffff#32) := by
  rw [item_from_image s base words c valid image cursor i]
  have bound := (valid.2.2.2.1 i).1
  intro eq
  have num := congrArg BitVec.toNat eq
  simp only [BitVec.toNat_ofNat] at num
  omega

theorem sentinel_from_image (s : X86Memory.State) (base : Word) (words : Array Nat) (c : Cell)
    (valid : c.Valid words) (image : WordImage s.memory base words)
    (cursor : s.regs 2=base+BitVec.ofNat 32 (2*c.offset)) :
    load16 s.memory (OriginalLineInvariant.address s c.ids.length)=(0xffff#16) := by
  rw [address_from_list s base c cursor]
  exact image _ _ valid.2.2.2.2

theorem pointer_from_image (s : X86Memory.State) (base lines : Word) (words : Array Nat) (c : Cell)
    (valid : c.Valid words) (image : WordImage s.memory base words)
    (cursor : s.regs 2=base+BitVec.ofNat 32 (2*c.offset))
    (lineBase : load32 s.memory 0x2c120=lines) (i : Fin c.ids.length) (frac : Fixed) :
    OriginalLineDispatch.pointer (OriginalLineInvariant.atIndex s i.val)=
      resolve lines ⟨frac,true,c.ids[i.val]⟩ := by
  unfold OriginalLineDispatch.pointer
  rw [item_from_image s base words c valid image cursor i]
  change _+load32 s.memory 0x2c120=_
  rw [lineBase]
  rfl

/-- The original query initialization, rather than an assumed empty cursor,
provides the first cell's collection reserve. This is before grid-setup writes. -/
theorem initialized_collection (s : X86Memory.State) (ox oy sx sy ex ey : Fixed)
    (h : OriginalPathInit.Inputs s ox oy sx sy ex ey) (words : Array Nat) (c : Cell)
    (valid : c.Valid words) (resolver : Collision.Intercept → Word) :
    OriginalLineCollection.Tracks (OriginalPathInit.result s).core 0x2ba20 resolver #[] c.ids.length := by
  have globals := (OriginalPathInit.ready s ox oy sx sy ex ey h).globals
  have cursor := congrArg Prod.fst globals
  refine ⟨?_,?_,?_⟩
  · intro i hi
    simp at hi
  · change load32 (OriginalPathInit.result s).core.memory 0x2c028=0x2ba20
    exact cursor
  · have bound := valid.2.2.1
    simp only [Array.size_empty,Nat.zero_add]
    omega

/-- A later cell still needs enough room; the map bound alone cannot prove it. -/
theorem reserve_cell (s : X86Memory.State) (base : Word) (resolver : Collision.Intercept → Word)
    (hits : Array Collision.Intercept) (words : Array Nat) (c : Cell) (valid : c.Valid words)
    (tracked : OriginalLineCollection.Tracks s base resolver hits 13) :
    OriginalLineCollection.Tracks s base resolver hits c.ids.length := by
  refine ⟨tracked.encoded,tracked.cursor,?_⟩
  have bound := valid.2.2.1
  have room := tracked.room
  omega
end Doom.Proofs.E1M1PathMap
