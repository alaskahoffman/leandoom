import Doom.Proofs.E1M1CellObjectAdvance
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1CellLineBoundary
open Verification X86 X86Memory X86Control BlockSummary
open E1M1ScanContracts (LineData candidates)
open E1M1NextCallbackReady (Ready)
attribute [local irreducible] load32

/-- Recover caller locals and the saved grid counter from a line-scan entry.
EDI itself is the temporary iterator cursor at that boundary. -/
def view (s : X86Memory.State) (sp : Word) :=
  put (put s 4 (sp-(112#32))) 7 (load32 s.memory (sp-(120#32)))

/-- At a real lookup, the saved-counter view equals the incoming grid state.
The saved word comes from CALL/PUSH rather than a reached-state hypothesis. -/
theorem lookup_view (s : X86Memory.State) (sp : Word) (stack : s.regs 4=sp-(112#32)) :
    E1M1PathAdvance.observe (view (E1M1PathMapCaller.scan s).core sp)=E1M1PathAdvance.observe s := by
  apply E1M1FiringGridState.transport
  · intro reg member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl
    · exact E1M1ThingCoordinates.caller_coordinate s false
    · exact E1M1FiringGridRegisters.caller_intercept s
    · exact E1M1ThingCoordinates.caller_coordinate s true
    · have saved := (E1M1ScanReturn.caller_words s).1
      rw [stack] at saved
      simpa [view,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc] using saved
  · intro off member
    change load32 (E1M1PathMapCaller.scan s).core.memory (sp-(112#32)+off)=load32 s.memory (s.regs 4+off)
    rw [stack]
    exact E1M1NextScanGrid.caller_local s sp stack off member

section Scan
variable (s : X86Memory.State) (sp cursor lines : Word) (objects : Nat → Word)
    (trace : Collision.Divline) (c : E1M1PathMap.Cell) (data : Nat → LineData)
    (stack : s.regs 4=sp-(124#32)) (list : s.regs 2=cursor)
    (items : E1M1PathMapLookup.ScanWords s lines c)
    (ids : ∀ i : Fin c.ids.length, c.ids[i.val]<475)
    (ready : Ready s lines trace c data)
    (layout : E1M1ScanContracts.Layout sp cursor lines c.ids.length (candidates trace lines c.ids data))
    (f : Option Flags) (r : Collision.PathResult)
    (tracked : OriginalLineCollection.Tracks s 0x2ba20 (E1M1ThingFinish.resolve lines objects) r.collected c.ids.length)
include stack list items ids ready layout tracked

/-- Every protected map, selection and callback word survives the complete scan. -/
theorem frame :
    E1M1CellMapInvariant.Frame sp lines s.memory (E1M1NextLineScan.result s lines trace c data f r).1.core.memory :=
  fun a safe => E1M1NextLineReturn.read_word s sp cursor lines objects trace c data stack list items ids ready layout f r tracked a safe.scan

/-- All eleven numeric fields survive the line scan and sentinel epilogue.
The counter is restored from the saved word, not the temporary iterator value. -/
theorem observe (returns : E1M1ScanReturn.ReturnSafe sp lines) (locals : E1M1GridLocals.Safe sp lines) :
    E1M1PathAdvance.observe (E1M1NextLineScan.result s lines trace c data f r).1.core=
      E1M1PathAdvance.observe (view s sp) := by
  let contract := E1M1NextLineScan.initial s sp cursor lines objects trace c data stack list items ids ready layout
  have intercept := OriginalLineInterceptRegister.finished_intercept s c.ids.length 0x2ba20
    (E1M1ThingFinish.resolve lines objects) contract r f tracked
    (fun j _ _ => E1M1ScanContracts.candidate_continues trace lines c.ids[j]! (data j))
  have coord (axis : Bool) := E1M1NextCoordinates.scan_coordinate s sp cursor lines objects trace c data stack list items ids ready layout f r tracked axis
  have ret := E1M1NextLineReturn.parent_return s sp cursor lines objects trace c data stack list items ids ready layout returns f r tracked
  apply E1M1FiringGridState.transport
  · intro reg member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl
    · exact coord false
    · exact intercept
    · exact coord true
    · exact ret.2.2.1
  · intro off member
    change load32 _ ((E1M1NextLineScan.result s lines trace c data f r).1.core.regs 4+off)=
      load32 s.memory (sp-(112#32)+off)
    rw [ret.2.1]
    exact E1M1NextLineReturn.read_word s sp cursor lines objects trace c data stack list items ids ready layout f r tracked _
      (E1M1GridLocals.scan_safe sp lines off member locals)
end Scan
end Doom.Proofs.E1M1CellLineBoundary
