import Doom.Proofs.E1M1FiringNextNumeric
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1CellMapInvariant
open Verification X86 X86Memory X86Control BlockSummary
attribute [local irreducible] load32

/-- A common immutable-read relation for scan, object and grid-step composition.
Mutable visit stamps and intersection records have their own invariants. -/
def Frame (sp lines : Word) (before after : Memory) : Prop :=
  ∀ a, E1M1FiringMapState.Safe sp lines a → load32 after a=load32 before a

/-- Map values and initialized option bits, independent of temporary iterator SP. -/
structure Image (m : Memory) (sp base lines : Word) (words : Array Nat) (w h : Nat) : Prop where
  width : load32 m 0x2c0fc=BitVec.ofNat 32 w
  height : load32 m 0x2c110=BitVec.ofNat 32 h
  widthBound : w<2^31
  heightBound : h<2^31
  table : load32 m 0x2c100=base+(8#32)
  lists : load32 m 0x2c10c=base
  lines : load32 m 0x2c120=lines
  encoded : E1M1PathMap.WordImage m base words
  options : load32 m (E1M1ThingGate.flagWord sp)=(3#32)

/-- Static separation can be reused at every cell; no reached values are assumed. -/
structure Layout (sp base lines : Word) (words : Array Nat) : Prop where
  globals : ∀ a∈[(0x2c0fc#32),0x2c110,0x2c100,0x2c10c,0x2c120], E1M1FiringMapState.Safe sp lines a
  image : ∀ i<words.size, E1M1FiringMapState.Safe sp lines (base+BitVec.ofNat 32 (2*i))
  flag : E1M1FiringMapState.Safe sp lines (E1M1ThingGate.flagWord sp)

theorem frame_trans (sp lines : Word) (a b c : Memory)
    (ab : Frame sp lines a b) (bc : Frame sp lines b c) : Frame sp lines a c :=
  fun p safe => (bc p safe).trans (ab p safe)

/-- A single frame fact transports the entire map invariant, including all
16-bit BLOCKMAP words and the initialized option byte. -/
theorem transport (m n : Memory) (sp base lines : Word) (words : Array Nat) (w h : Nat)
    (image : Image m sp base lines words w h) (layout : Layout sp base lines words)
    (frame : Frame sp lines m n) : Image n sp base lines words w h := by
  refine ⟨(frame _ (layout.globals _ (by simp))).trans image.width,
    (frame _ (layout.globals _ (by simp))).trans image.height,image.widthBound,image.heightBound,
    (frame _ (layout.globals _ (by simp))).trans image.table,
    (frame _ (layout.globals _ (by simp))).trans image.lists,
    (frame _ (layout.globals _ (by simp))).trans image.lines,?_,
    (frame _ layout.flag).trans image.options⟩
  intro i value hv
  obtain ⟨hi,_⟩ := Array.getElem?_eq_some_iff.mp hv
  have half := congrArg (fun v : Word => v.extractLsb' 0 16) (frame _ (layout.image i hi))
  rw [SectorDispatch.load_half,SectorDispatch.load_half] at half
  exact half.trans (image.encoded i value hv)

/-- Recover both enabled iterators at the restored caller SP. -/
theorem enabled (s : X86Memory.State) (sp base lines : Word) (words : Array Nat) (w h : Nat)
    (stack : s.regs 4=sp-(112#32)) (image : Image s.memory sp base lines words w h) (line : Bool) :
    OriginalPathCell.enabled line s=true := by
  have byte := congrArg (fun v : Word => v.extractLsb' 0 8) image.options
  rw [E1M1PathCell.low_byte] at byte
  unfold OriginalPathCell.enabled OriginalPathCell.optionBits
  rw [stack]
  have addr : sp-(112#32)+(64#32)=E1M1ThingGate.flagWord sp := by
    simp [E1M1ThingGate.flagWord,BitVec.sub_eq_add_neg,BitVec.add_assoc]
  change (s.memory (sp-(112#32)+(64#32)) &&& OriginalPathCell.mask line != 0)=true
  rw [addr,byte]
  cases line <;> decide

/-- Turn the persistent image into the actual next-lookup premises. -/
theorem inputs (s : X86Memory.State) (sp base lines : Word) (words : Array Nat) (w h : Nat)
    (stack : s.regs 4=sp-(112#32)) (image : Image s.memory sp base lines words w h)
    (layout : Layout sp base lines words) :
    E1M1PathMapCaller.Dimensions s w h ∧ E1M1PathMapCaller.Globals s base lines ∧
    E1M1PathMapCaller.ImageSafe s base words := by
  refine ⟨⟨image.width,image.height,image.widthBound,image.heightBound,?_⟩,
    ⟨image.table,image.lists,image.lines,?_⟩,?_⟩
  · intro a ha
    apply E1M1FiringMapState.caller_safe s sp lines a stack (layout.globals a ?_)
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl <;> simp
  · intro a ha
    apply E1M1FiringMapState.caller_safe s sp lines a stack (layout.globals a ?_)
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl <;> simp
  · intro i hi
    exact E1M1FiringMapState.caller_safe s sp lines _ stack (layout.image i hi)

/-- An arbitrary in-map gate executes the original lookup. The same immutable
image, mixed records, exact reserve and mutable visit history reach scan entry.
This supplies no new capacity and assumes no callback results. -/
theorem inside (s : X86Control.State) (sp base lines : Word) (words : Array Nat) (w h : Nat)
    (pc : s.pc=0x2ca7f) (stack : s.core.regs 4=sp-(112#32))
    (image : Image s.core.memory sp base lines words w h) (layout : Layout sp base lines words)
    (x y : Int32) (mapX : s.core.regs 6=x.toBitVec) (mapY : s.core.regs 1=y.toBitVec)
    (c : E1M1PathMap.Cell) (inMap : Collision.pathCellInside x y w h=true)
    (valid : c.Valid words) (selected : words[4+Collision.pathCellIndex x y w]?=some c.offset)
    (resolve : Collision.Intercept → Word) (hits : Array Collision.Intercept) (reserve : Nat)
    (tracked : OriginalLineCollection.Tracks s.core 0x2ba20 resolve hits reserve)
    (cursorSafe : E1M1PathMapCaller.Safe s.core (0x2c028#32))
    (recordsSafe : ∀ i<hits.size, ∀ off∈[(0#32),4,8],
      E1M1PathMapCaller.Safe s.core (OriginalLineCollection.slot 0x2ba20 i off))
    (epoch : Word) (seen : Array Bool)
    (represented : OriginalLineVisits.Represents s.core.memory lines epoch seen)
    (epochSafe : E1M1PathMapCaller.Safe s.core (0x13580#32))
    (stampSafe : ∀ j<seen.size, E1M1PathMapCaller.Safe s.core (OriginalLineVisits.stamp lines j)) :
    let out := E1M1PathMapCaller.scan s.core
    (∃ n≤30, X86CodeMemory.Prefix FloorCaller.cm E1M1FiringAdvance.program [] n s out) ∧
    E1M1PathMapLookup.ScanWords out.core lines c ∧ out.pc=0x2c57f ∧ out.core.regs 4=sp-(124#32) ∧
    Image out.core.memory sp base lines words w h ∧ Frame sp lines s.core.memory out.core.memory ∧
    OriginalLineCollection.Tracks out.core 0x2ba20 resolve hits reserve ∧
    OriginalLineVisits.Represents out.core.memory lines epoch seen := by
  have facts := inputs s.core sp base lines words w h stack image layout
  obtain ⟨⟨n,hn,run⟩,items,stop,outStack⟩ := E1M1PathMapCaller.inside_to_scan s.core s.flags base lines words c x y w h
    (enabled s.core sp base lines words w h stack image true) facts.1 mapX mapY facts.2.1 inMap valid image.encoded facts.2.2 selected
  rw [OriginalPathXStep.at_pc _ _ pc] at run
  have frame : Frame sp lines s.core.memory (E1M1PathMapCaller.scan s.core).core.memory :=
    fun a safe => E1M1NextCellMemory.caller_frame s.core a
      (E1M1FiringMapState.caller_safe s.core sp lines a stack safe)
  refine ⟨⟨n,hn,X86CodeMemory.lift_success
    (run.transfer _ [] E1M1NextCellScan.contains_caller (by simp)) FloorCaller.cm⟩,items,stop,
    by rw [outStack,stack]; simp [BitVec.sub_eq_add_neg,BitVec.add_assoc],
    transport _ _ sp base lines words w h image layout frame,frame,
    E1M1PathMapCaller.collection_preserved s.core 0x2ba20 resolve hits reserve tracked cursorSafe recordsSafe,?_,?_⟩
  · exact (E1M1NextCellMemory.caller_frame s.core _ epochSafe).trans represented.1
  · intro j hj
    rw [E1M1NextCellMemory.caller_frame s.core _ (stampSafe j hj)]
    exact represented.2 j hj
end Doom.Proofs.E1M1CellMapInvariant
