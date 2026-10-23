import Doom.Proofs.E1M1AimStampScan
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimStampNextScan
open Verification X86 X86Memory X86Control BlockSummary
open E1M1ScanContracts (LineData candidates)
open E1M1NextCallbackReady (Ready)
open OriginalLineMixedInvariant (Initial)
open OriginalLineVisits (Represents markPrefix)
open E1M1AimStampImage (Image Fresh)
open E1M1NextLineScan (result)
attribute [local irreducible] load32 store32

/-- The actual next-cell line scan and sentinel retain original stamp values
alongside source hits and instruction execution. Later-epoch freshness is derived
conditionally from original words, not postulated at the reached state. -/
theorem execution (s : X86Memory.State) (sp cursor lines : Word) (objects : Nat → Word)
    (trace : Collision.Divline) (c : E1M1PathMap.Cell) (data : Nat → LineData)
    (stack : s.regs 4=sp-(124#32)) (list : s.regs 2=cursor)
    (items : E1M1PathMapLookup.ScanWords s lines c)
    (ids : ∀ i : Fin c.ids.length, c.ids[i.val]<475)
    (ready : Ready s lines trace c data)
    (layout : E1M1ScanContracts.Layout sp cursor lines c.ids.length (candidates trace lines c.ids data))
    (stamps : E1M1ScanContracts.Stamps sp lines) (f : Option Flags)
    (r : Collision.PathResult)
    (tracked : OriginalLineCollection.Tracks s 0x2ba20 (E1M1ThingFinish.resolve lines objects) r.collected c.ids.length)
    (epoch : Word) (seen : Array Bool) (size : seen.size=475)
    (represented : Represents s.memory lines epoch seen)
    (origin : Memory) (image : Image origin s.memory lines epoch seen) :
    let out := result s lines trace c data f r
    (∃ steps≤281*c.ids.length+7, X86ReturnCleanup.Prefix FloorCaller.cm E1M1AimProgramLink.program [] steps
      ⟨s,f,0x2c57f⟩ out.1) ∧
    OriginalLineTraversal.Runs ⟨s,f,0x2c57f⟩ out.1 c.ids.length ∧
    OriginalLineCollection.Tracks out.1.core 0x2ba20 (E1M1ThingFinish.resolve lines objects) out.2.collected 0 ∧
    Represents out.1.core.memory lines epoch (markPrefix (candidates trace lines c.ids data) c.ids.length 0 seen) ∧
    (∀ a∈E1M1ScanContracts.protectedWords sp cursor c.ids.length (candidates trace lines c.ids data),
      load32 out.1.core.memory a=load32 s.memory a) ∧
    (∃ added : List Collision.Intercept, out.2.collected.toList=r.collected.toList++added) ∧
    Image origin out.1.core.memory lines epoch
      (markPrefix (candidates trace lines c.ids data) c.ids.length 0 seen) ∧
    (Fresh origin lines (epoch+1) seen.size →
      Fresh out.1.core.memory lines (load32 out.1.core.memory 0x13580+1) seen.size) := by
  have old := E1M1NextLineScan.execution s sp cursor lines objects trace c data stack list items ids ready layout
    stamps f r tracked epoch seen size represented
  let h := E1M1NextLineScan.initial s sp cursor lines objects trace c data stack list items ids ready layout
  have keep : ∀ j<c.ids.length, (h.candidates j).crosses=true → (h.candidates j).Continues := by
    intro j _ _
    exact E1M1ScanContracts.candidate_continues trace lines c.ids[j]! (data j)
  have exactImage := E1M1AimStampScan.finished_image s c.ids.length 0x2ba20
    (E1M1ThingFinish.resolve lines objects) h lines 475
    (E1M1NextLineScan.visit_layout s sp cursor lines objects trace c data stack list items ids ready layout stamps)
    f r tracked keep origin epoch seen size represented image
  change Image origin (result s lines trace c data f r).1.core.memory lines epoch
    (markPrefix (candidates trace lines c.ids data) c.ids.length 0 seen) at exactImage
  obtain ⟨steps,bound,run⟩ := old.1
  have query := (run.transfer E1M1TraversalEntry.program []
    E1M1TraversalEntry.contains_collection (by simp)).transfer E1M1FirstIntercept.program []
      E1M1FirstIntercept.contains_entry (by simp)
  have linked := (X86ReturnCleanup.lift query).transfer E1M1AimProgramLink.program
    E1M1AimProgramLink.contains_query
  refine ⟨⟨steps,bound,linked⟩,old.2.1,old.2.2.1,old.2.2.2.1,old.2.2.2.2.1,old.2.2.2.2.2,exactImage,?_⟩
  intro fresh
  have next := E1M1AimStampImage.next_fresh origin _ lines epoch _ exactImage
    (by simpa only [OriginalLineVisitedRun.mark_size] using fresh)
  simpa only [OriginalLineVisitedRun.mark_size] using next

/-- Specialize to the actual entry memory without requiring a separate stamp
image premise. This still needs future-epoch freshness of original words. -/
theorem from_entry (s : X86Memory.State) (sp cursor lines : Word) (objects : Nat → Word)
    (trace : Collision.Divline) (c : E1M1PathMap.Cell) (data : Nat → LineData)
    (stack : s.regs 4=sp-(124#32)) (list : s.regs 2=cursor)
    (items : E1M1PathMapLookup.ScanWords s lines c)
    (ids : ∀ i : Fin c.ids.length, c.ids[i.val]<475)
    (ready : Ready s lines trace c data)
    (layout : E1M1ScanContracts.Layout sp cursor lines c.ids.length (candidates trace lines c.ids data))
    (stamps : E1M1ScanContracts.Stamps sp lines) (f : Option Flags)
    (r : Collision.PathResult)
    (tracked : OriginalLineCollection.Tracks s 0x2ba20 (E1M1ThingFinish.resolve lines objects) r.collected c.ids.length)
    (epoch : Word) (seen : Array Bool) (size : seen.size=475)
    (represented : Represents s.memory lines epoch seen)
 :
    let out := result s lines trace c data f r
    (∃ steps≤281*c.ids.length+7, X86ReturnCleanup.Prefix FloorCaller.cm E1M1AimProgramLink.program [] steps
      ⟨s,f,0x2c57f⟩ out.1) ∧
    OriginalLineTraversal.Runs ⟨s,f,0x2c57f⟩ out.1 c.ids.length ∧
    OriginalLineCollection.Tracks out.1.core 0x2ba20 (E1M1ThingFinish.resolve lines objects) out.2.collected 0 ∧
    Represents out.1.core.memory lines epoch (markPrefix (candidates trace lines c.ids data) c.ids.length 0 seen) ∧
    (∀ a∈E1M1ScanContracts.protectedWords sp cursor c.ids.length (candidates trace lines c.ids data),
      load32 out.1.core.memory a=load32 s.memory a) ∧
    (∃ added : List Collision.Intercept, out.2.collected.toList=r.collected.toList++added) ∧
    Image s.memory out.1.core.memory lines epoch
      (markPrefix (candidates trace lines c.ids data) c.ids.length 0 seen) ∧
    (Fresh s.memory lines (epoch+1) seen.size →
      Fresh out.1.core.memory lines (load32 out.1.core.memory 0x13580+1) seen.size) := by
  exact execution s sp cursor lines objects trace c data stack list items ids ready layout
    stamps f r tracked epoch seen size represented s.memory
    (E1M1AimStampImage.start s.memory lines epoch seen represented)
end Doom.Proofs.E1M1AimStampNextScan
