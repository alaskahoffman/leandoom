import Doom.Proofs.E1M1FiringNextBoundary
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1NextScanGrid
open Verification X86 X86Memory X86Control BlockSummary
open E1M1ScanContracts (LineData candidates)
open E1M1NextCallbackReady (Ready)
open OriginalLineMixedInvariant (Initial)
attribute [local irreducible] load32

open E1M1NextObjectMemory (result)

/-- Object CALL, bounds, table lookup and empty return retain all four live
grid registers. Callback execution is covered by ObjectBoundary separately. -/
theorem lookup_register (s : X86Control.State) (reg : Fin 8)
    (member : reg∈([1,5,6,7] : List (Fin 8))) :
    (OriginalThingEntry.result (E1M1FiringNextThings.called s).core).core.regs reg=s.core.regs reg := by
  have callKeep : (E1M1FiringNextThings.called s).core.regs reg=s.core.regs reg := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl <;>
      simp [E1M1FiringNextThings.called,OriginalPathCell.called,OriginalPathCell.c3,
        OriginalPathCell.c2,OriginalPathCell.c1,X86Routine.pushWord,put,write]
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl
  · exact (E1M1ThingPreservation.lookup_coordinate _ false).trans callKeep
  · exact (E1M1ThingGridRegisters.lookup_register _ false).trans callKeep
  · exact (E1M1ThingPreservation.lookup_coordinate _ true).trans callKeep
  · exact (E1M1ThingGridRegisters.lookup_register _ true).trans callKeep

/-- The line-iterator CALL/prologue preserve grid locals after advancement.
In particular the updated Y intercept is retained, not its old pre-step value. -/
theorem caller_local (s : X86Memory.State) (sp : Word) (stack : s.regs 4=sp-(112#32))
    (off : Word) (member : off∈E1M1GridLocals.offsets) :
    load32 (E1M1PathMapCaller.scan s).core.memory (E1M1GridLocals.address sp off)=
      load32 s.memory (E1M1GridLocals.address sp off) := by
  apply E1M1NextCellMemory.caller_frame
  unfold E1M1PathMapCaller.Safe
  rw [stack]
  exact ⟨by simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using E1M1GridLocals.below sp off member ⟨0,by decide⟩,
    by simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using E1M1GridLocals.below sp off member ⟨1,by decide⟩,
    by simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using E1M1GridLocals.below sp off member ⟨2,by decide⟩⟩

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

/-- Only scan and following CALL/prologue separation is needed here. No
separation from an earlier advance store is required, so this applies to the
updated Y-intercept slot itself. -/
theorem read_word (a : Word) (scanSafe : E1M1ThingGeometry.ScanSafe sp lines a)
    (callSafe : Apart a (sp-(116#32))) (entrySafe : Apart a (sp-(120#32))) :
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
      (E1M1NextLineReturn.read_word s sp cursor lines objects trace c data stack list items ids ready layout f r tracked a scanSafe)
    change Apart a (scan.1.core.regs 4-(4#32))
    rw [ret.2.1]
    simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using callSafe
  · rw [callSP]
    simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using entrySafe

/-- All seven positive grid locals survive the next line scan and object lookup. -/
theorem local_word (locals : E1M1GridLocals.Safe sp lines)
    (off : Word) (member : off∈E1M1GridLocals.offsets) :
    load32 (result s lines trace c data f r).core.memory (E1M1GridLocals.address sp off)=
      load32 s.memory (E1M1GridLocals.address sp off) :=
  read_word s sp cursor lines objects trace c data stack list items ids ready layout returns f r tracked _
    (E1M1GridLocals.scan_safe sp lines off member locals)
    (E1M1GridLocals.below sp off member ⟨0,by decide⟩)
    (E1M1GridLocals.below sp off member ⟨1,by decide⟩)

/-- Coordinates and EBP survive callbacks; EDI is restored from the saved
iterator-prologue word. This does not assume the reached counter's value. -/
theorem registers :
    let out := result s lines trace c data f r
    (∀ reg∈([1,5,6] : List (Fin 8)), out.core.regs reg=s.regs reg) ∧
    out.core.regs 7=load32 s.memory (sp-(120#32)) := by
  let scan := E1M1NextLineScan.result s lines trace c data f r
  let contract := E1M1NextLineScan.initial s sp cursor lines objects trace c data stack list items ids ready layout
  have intercept := OriginalLineInterceptRegister.finished_intercept s c.ids.length 0x2ba20
    (E1M1ThingFinish.resolve lines objects) contract r f tracked
    (fun j _ _ => E1M1ScanContracts.candidate_continues trace lines c.ids[j]! (data j))
  have coord (axis : Bool) := E1M1NextCoordinates.scan_coordinate s sp cursor lines objects trace c data stack list items ids ready layout f r tracked axis
  have ret := E1M1NextLineReturn.parent_return s sp cursor lines objects trace c data stack list items ids ready layout returns f r tracked
  constructor
  · intro reg member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl
    · exact (lookup_register scan.1 1 (by simp)).trans (coord false)
    · exact (lookup_register scan.1 5 (by simp)).trans intercept
    · exact (lookup_register scan.1 6 (by simp)).trans (coord true)
  · exact (lookup_register scan.1 7 (by simp)).trans ret.2.2.1
end Scan
end Doom.Proofs.E1M1NextScanGrid
