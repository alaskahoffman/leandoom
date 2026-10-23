import Doom.Proofs.E1M1FiringNextLookup
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1NextObjectMemory
open Verification X86 X86Memory X86Control BlockSummary
open E1M1ScanContracts (LineData candidates)
open E1M1NextCallbackReady (Ready)
open OriginalLineMixedInvariant (Initial)
attribute [local irreducible] load32

/-- A mixed scan adds at most one record per candidate, regardless of the
incoming line/object mix. This bound is reusable at every subsequent cell. -/
theorem scan_size (s : X86Memory.State) (lines : Word) (trace : Collision.Divline)
    (c : E1M1PathMap.Cell) (data : Nat → LineData) (f : Option Flags) (r : Collision.PathResult) :
    (E1M1NextLineScan.result s lines trace c data f r).2.collected.size≤r.collected.size+c.ids.length :=
  E1M1ScanCapacity.run_size _ _ _ _ _

/-- The real line return, object CALL and iterator lookup share this endpoint. -/
def result (s : X86Memory.State) (lines : Word) (trace : Collision.Divline)
    (c : E1M1PathMap.Cell) (data : Nat → LineData) (f : Option Flags) (r : Collision.PathResult) :=
  OriginalThingEntry.result (E1M1FiringNextThings.called (E1M1NextLineScan.result s lines trace c data f r).1).core

section Scan
variable (s : X86Memory.State) (sp cursor lines : Word) (objects : Nat → Word)
    (trace : Collision.Divline) (c : E1M1PathMap.Cell) (data : Nat → LineData)
    (stack : s.regs 4=sp-(124#32)) (list : s.regs 2=cursor)
    (items : E1M1PathMapLookup.ScanWords s lines c)
    (ids : ∀ i : Fin c.ids.length, c.ids[i.val]<475)
    (ready : Ready s lines trace c data)
    (layout : E1M1ScanContracts.Layout sp cursor lines c.ids.length (candidates trace lines c.ids data))
include stack list items ids ready layout


variable (returns : E1M1ScanReturn.ReturnSafe sp lines) (f : Option Flags) (r : Collision.PathResult)
    (tracked : OriginalLineCollection.Tracks s 0x2ba20 (E1M1ThingFinish.resolve lines objects) r.collected c.ids.length)
include returns tracked

/-- Transport a protected read across the remaining line scan and both actual
stores. This also transports newly initialized trace words without confusing
their values with the contents before firing setup. -/
theorem read_word (a : Word) (safe : E1M1FiringMapState.Safe sp lines a) :
    load32 (result s lines trace c data f r).core.memory a=load32 s.memory a := by
  let scan := E1M1NextLineScan.result s lines trace c data f r
  let call := E1M1FiringNextThings.called scan.1
  have ret := E1M1NextLineReturn.parent_return s sp cursor lines objects trace c data stack list items ids ready layout returns f r tracked
  have callSP : call.core.regs 4=sp-(116#32) := by
    have obs := (OriginalPathCell.call_inputs false scan.1.core (OriginalPathCell.gateFlags false scan.1.core)).2.2.2.1
    rw [ret.2.1] at obs
    simpa [call,E1M1FiringNextThings.called,BitVec.sub_eq_add_neg,BitVec.add_assoc] using obs
  apply (OriginalThingEntry.frame call.core a ?_).trans
  · apply (OriginalPathCell.call_frame false scan.1.core _ a ?_).trans
      (E1M1NextLineReturn.read_word s sp cursor lines objects trace c data stack list items ids ready layout f r tracked a safe.scan)
    change Apart a (scan.1.core.regs 4-(4#32))
    rw [ret.2.1]
    simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe.caller 116 (by simp)
  · rw [callSP]
    simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe.caller 120 (by simp)

/-- The caller word is produced by CALL and survives the iterator prologue;
it is never assumed in the incoming memory image. -/
theorem caller_word :
    load32 (result s lines trace c data f r).core.memory (sp-(116#32))=(0x2cab1#32) := by
  let scan := E1M1NextLineScan.result s lines trace c data f r
  let call := E1M1FiringNextThings.called scan.1
  have ret := E1M1NextLineReturn.parent_return s sp cursor lines objects trace c data stack list items ids ready layout returns f r tracked
  have obs := OriginalPathCell.call_inputs false scan.1.core (OriginalPathCell.gateFlags false scan.1.core)
  have callSP : call.core.regs 4=sp-(116#32) := by
    have h := obs.2.2.2.1
    rw [ret.2.1] at h
    simpa [call,E1M1FiringNextThings.called,BitVec.sub_eq_add_neg,BitVec.add_assoc] using h
  change load32 (OriginalThingEntry.result call.core).core.memory _=_
  rw [←callSP,OriginalThingEntry.result_memory,OriginalThingEntry.return_word]
  dsimp only [call,E1M1FiringNextThings.called]
  rw [obs.2.2.2.1]
  exact obs.2.2.2.2.1
end Scan
end Doom.Proofs.E1M1NextObjectMemory
