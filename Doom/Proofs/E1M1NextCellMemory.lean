import Doom.Proofs.E1M1FiringCollectionAdvance
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
namespace Doom.Proofs.E1M1NextCellMemory
open Verification X86 X86Memory X86Control BlockSummary
attribute [local irreducible] load32

abbrev advanced (s : X86Memory.State) := (OriginalPathAdvance.result s).core
abbrev scan (s : X86Memory.State) := E1M1PathMapCaller.scan (advanced s)

/-- The step's one possible store and the following CALL/prologue stores.
This is only address separation, not an assumed post-step memory image. -/
def Safe (s : X86Memory.State) (a : Word) : Prop :=
  Apart a (s.regs 4+(44#32)) ∧ E1M1PathMapCaller.Safe s a

theorem stack (s : X86Memory.State) : (advanced s).regs 4=s.regs 4 :=
  (E1M1PathAdvance.result_observe s).2.2

theorem caller_safe (s : X86Memory.State) (a : Word) (safe : E1M1PathMapCaller.Safe s a) :
    E1M1PathMapCaller.Safe (advanced s) a := by
  unfold E1M1PathMapCaller.Safe
  rw [stack]
  exact safe

/-- Lookup has no stores; only its CALL and prologue need framing. -/
theorem caller_frame (s : X86Memory.State) (a : Word) (safe : E1M1PathMapCaller.Safe s a) :
    load32 (E1M1PathMapCaller.scan s).core.memory a=load32 s.memory a := by
  change load32 (OriginalLineCell.lookup _).core.memory a=_
  rw [(OriginalLineCell.lookup_observe _).2.1]
  exact (E1M1PathMapBounds.result_frame _ a (E1M1PathMapCaller.safe_at_call s a safe)).trans
    (E1M1PathMapCaller.call_frame s a safe.1)

theorem frame (s : X86Memory.State) (a : Word) (safe : Safe s a) :
    load32 (scan s).core.memory a=load32 s.memory a :=
  (caller_frame (advanced s) a (caller_safe s a safe.2)).trans
    (E1M1AdvanceCollection.frame s a safe.1)

/-- The line/thing enable byte is a positive stack local, disjoint from the
Y-intercept store even for a wrapping, unaligned stack. -/
theorem enabled (s : X86Memory.State) (line : Bool) :
    OriginalPathCell.enabled line (advanced s)=OriginalPathCell.enabled line s := by
  have safe : Apart (s.regs 4+(64#32)) (s.regs 4+(44#32)) :=
    OriginalPathXStep.apart_translate _ _ _ (by unfold Apart; decide)
  have byte := congrArg (fun v : Word => v.extractLsb' 0 8) (E1M1AdvanceCollection.frame s _ safe)
  rw [E1M1PathCell.low_byte,E1M1PathCell.low_byte] at byte
  unfold OriginalPathCell.enabled OriginalPathCell.optionBits
  rw [stack]
  exact congrArg (fun b : BitVec 8 => b &&& OriginalPathCell.mask line != 0) byte

/-- Preserve a possibly nonempty visited set, including the epoch itself. -/
theorem visits (s : X86Memory.State) (lines epoch : Word) (seen : Array Bool)
    (represented : OriginalLineVisits.Represents s.memory lines epoch seen)
    (epochSafe : Safe s (0x13580#32))
    (stampsSafe : ∀ j<seen.size, Safe s (OriginalLineVisits.stamp lines j)) :
    OriginalLineVisits.Represents (scan s).core.memory lines epoch seen := by
  refine ⟨(frame s _ epochSafe).trans represented.1,?_⟩
  intro j hj
  rw [frame s _ (stampsSafe j hj)]
  exact represented.2 j hj

/-- Raw BLOCKMAP words survive both advancement and next-cell lookup. -/
theorem image (s : X86Memory.State) (base : Word) (words : Array Nat)
    (encoded : E1M1PathMap.WordImage s.memory base words)
    (safe : ∀ i<words.size, Safe s (base+BitVec.ofNat 32 (2*i))) :
    E1M1PathMap.WordImage (scan s).core.memory base words := by
  intro i value hv
  obtain ⟨hi,_⟩ := Array.getElem?_eq_some_iff.mp hv
  have half := congrArg (fun v : Word => v.extractLsb' 0 16) (frame s _ (safe i hi))
  rw [SectorDispatch.load_half,SectorDispatch.load_half] at half
  exact half.trans (encoded i value hv)

/-- No new capacity is manufactured: the exact existing reserve survives. -/
theorem collection (s : X86Memory.State) (base : Word) (resolve : Collision.Intercept → Word)
    (hits : Array Collision.Intercept) (reserve : Nat)
    (tracked : OriginalLineCollection.Tracks s base resolve hits reserve)
    (advanceSafe : OriginalLineMixedInvariant.ArraySafe base (s.regs 4+(44#32)))
    (cursorSafe : E1M1PathMapCaller.Safe s (0x2c028#32))
    (recordsSafe : ∀ i<hits.size, ∀ off∈[(0#32),4,8],
      E1M1PathMapCaller.Safe s (OriginalLineCollection.slot base i off)) :
    OriginalLineCollection.Tracks (scan s).core base resolve hits reserve := by
  exact E1M1PathMapCaller.collection_preserved (advanced s) base resolve hits reserve
    (E1M1AdvanceCollection.collection s base resolve hits reserve tracked advanceSafe)
    (caller_safe s _ cursorSafe) (fun i hi off ho => caller_safe s _ (recordsSafe i hi off ho))

/-- Map lookup facts are transported from before the grid step, rather than
postulated at the reached next-cell gate. -/
theorem map (s : X86Memory.State) (base lines : Word) (words : Array Nat) (w h : Nat)
    (dims : E1M1PathMapCaller.Dimensions s w h)
    (globals : E1M1PathMapCaller.Globals s base lines)
    (encoded : E1M1PathMap.WordImage s.memory base words)
    (globalsSafe : ∀ a∈[(0x2c0fc#32),0x2c110,0x2c100,0x2c10c,0x2c120], Apart a (s.regs 4+(44#32)))
    (imageSafe : ∀ i<words.size, Safe s (base+BitVec.ofNat 32 (2*i))) :
    E1M1PathMapCaller.Dimensions (advanced s) w h ∧
    E1M1PathMapCaller.Globals (advanced s) base lines ∧
    E1M1PathMap.WordImage (advanced s).memory base words ∧
    E1M1PathMapCaller.ImageSafe (advanced s) base words := by
  have keep (a : Word) (ha : a∈[(0x2c0fc#32),0x2c110,0x2c100,0x2c10c,0x2c120]) :=
    E1M1AdvanceCollection.frame s a (globalsSafe a ha)
  refine ⟨⟨(keep _ (by simp)).trans dims.width,(keep _ (by simp)).trans dims.height,
      dims.widthBound,dims.heightBound,fun a ha => caller_safe s a (dims.safe a ha)⟩,
    ⟨(keep _ (by simp)).trans globals.table,(keep _ (by simp)).trans globals.lists,
      (keep _ (by simp)).trans globals.lines,fun a ha => caller_safe s a (globals.safe a ha)⟩,?_,
    fun i hi => caller_safe s _ (imageSafe i hi).2⟩
  intro i value hv
  obtain ⟨hi,_⟩ := Array.getElem?_eq_some_iff.mp hv
  have half := congrArg (fun v : Word => v.extractLsb' 0 16)
    (E1M1AdvanceCollection.frame s _ (imageSafe i hi).1)
  rw [SectorDispatch.load_half,SectorDispatch.load_half] at half
  exact half.trans (encoded i value hv)
end Doom.Proofs.E1M1NextCellMemory
