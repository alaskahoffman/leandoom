import Doom.Proofs.E1M1NextCursor
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1NextLineScan
open Verification X86 X86Memory X86Control BlockSummary
open E1M1ScanContracts (LineData candidates)
open E1M1NextCallbackReady (Ready)
open OriginalLineMixedInvariant (Initial)
open OriginalLineVisits (Represents markPrefix)
attribute [local irreducible] load32

/-- Include the original line scan in the same authenticated program as firing. -/
theorem contains_scan (pc : Nat) (h : OriginalLineMixedInvariant.program pc≠none) :
    E1M1FiringAdvance.program pc=OriginalLineMixedInvariant.program pc := by
  have a := E1M1ThingEntry.contains_prior pc h
  have b := E1M1FiringThings.contains_entry pc (by rw [a]; exact h)
  exact (E1M1FiringAdvance.contains_prior pc (by
    change E1M1FiringThings.program pc≠none
    rw [b,a]; exact h)).trans (b.trans a)

/-- Every branch retains incoming records in order; only an accepted hit appends. -/
theorem step_prefix (c : OriginalLineMixedInvariant.Candidate) (s : X86Memory.State)
    (r : Collision.PathResult) :
    ∃ added : List Collision.Intercept, (OriginalLineMixedInvariant.step c s r).2.collected.toList=r.collected.toList++added := by
  unfold OriginalLineMixedInvariant.step
  split
  · exact ⟨[],by simp⟩
  · split
    · split
      · exact ⟨[],by simp⟩
      · split
        · exact ⟨[],by simp⟩
        · exact ⟨[c.hit],by simp⟩
    · exact ⟨[],by simp⟩

/-- This preservation applies to an arbitrary mixed input array, including objects. -/
theorem run_prefix (cs : Nat → OriginalLineMixedInvariant.Candidate) (k i : Nat)
    (s : X86Control.State) (r : Collision.PathResult) :
    ∃ added : List Collision.Intercept, (OriginalLineMixedInvariant.run cs k i s r).2.collected.toList=r.collected.toList++added := by
  induction k generalizing i s r with
  | zero => exact ⟨[],by simp [OriginalLineMixedInvariant.run]⟩
  | succ k ih =>
    obtain ⟨a,first⟩ := step_prefix (cs i) s.core r
    obtain ⟨b,rest⟩ := ih (i+1) (OriginalLineMixedInvariant.step (cs i) s.core r).1 (OriginalLineMixedInvariant.step (cs i) s.core r).2
    refine ⟨a++b,?_⟩
    change (OriginalLineMixedInvariant.run cs k (i+1) _ _).2.collected.toList=_
    rw [rest,first,List.append_assoc]

section Scan
variable (s : X86Memory.State) (sp cursor lines : Word) (objects : Nat → Word)
    (trace : Collision.Divline) (c : E1M1PathMap.Cell) (data : Nat → LineData)
    (stack : s.regs 4=sp-(124#32)) (list : s.regs 2=cursor)
    (items : E1M1PathMapLookup.ScanWords s lines c)
    (ids : ∀ i : Fin c.ids.length, c.ids[i.val]<475)
    (ready : Ready s lines trace c data)
    (layout : E1M1ScanContracts.Layout sp cursor lines c.ids.length (candidates trace lines c.ids data))
include stack list items ids ready layout

/-- Assemble the existing invariant without relabeling or discarding prior
object hits. The new candidates are lines, but the retained array is mixed. -/
def initial : Initial s c.ids.length 0x2ba20 (E1M1ThingFinish.resolve lines objects) := by
  let original := E1M1ScanContracts.initial s sp cursor lines trace c data stack list items ids
    ready.target ready.active ready.geometry ready.computed ready.back layout
  exact { original with pointer := fun _ _ _ => rfl }

/-- The mutable stamp layout is unchanged by the mixed-hit resolver. -/
theorem visit_layout (stamps : E1M1ScanContracts.Stamps sp lines) :
    OriginalLineVisits.Layout s (initial s sp cursor lines objects trace c data stack list items ids ready layout) lines 475 := by
  have h := E1M1ScanContracts.visit_layout s sp cursor lines trace c data stack list items ids
    ready.target ready.active ready.geometry ready.computed ready.back layout stamps
  exact ⟨h.countBound,h.ids,h.pointers,h.call,h.side,h.scratch,h.records⟩

omit stack list items ids ready layout in
/-- The output is independent of the proof record, and starts with all incoming hits. -/
def result (f : Option Flags) (r : Collision.PathResult) :=
  let endScan := OriginalLineMixedInvariant.run (candidates trace lines c.ids data) c.ids.length 0 ⟨s,f,0x2c57f⟩ r
  (OriginalLineBounds.returned (OriginalLineCell.header endScan.1.core).core,endScan.2)

/-- Execute every remaining candidate and the sentinel under an explicit budget,
retaining the ordered mixed collection and updated visited history. -/
theorem execution (stamps : E1M1ScanContracts.Stamps sp lines) (f : Option Flags)
    (r : Collision.PathResult)
    (tracked : OriginalLineCollection.Tracks s 0x2ba20 (E1M1ThingFinish.resolve lines objects) r.collected c.ids.length)
    (epoch : Word) (seen : Array Bool) (size : seen.size=475)
    (represented : Represents s.memory lines epoch seen) :
    let out := result s lines trace c data f r
    (∃ steps≤281*c.ids.length+7, X86CodeMemory.Prefix FloorCaller.cm E1M1FiringAdvance.program [] steps
      ⟨s,f,0x2c57f⟩ out.1) ∧
    OriginalLineTraversal.Runs ⟨s,f,0x2c57f⟩ out.1 c.ids.length ∧
    OriginalLineCollection.Tracks out.1.core 0x2ba20 (E1M1ThingFinish.resolve lines objects) out.2.collected 0 ∧
    Represents out.1.core.memory lines epoch (markPrefix (candidates trace lines c.ids data) c.ids.length 0 seen) ∧
    (∀ a∈E1M1ScanContracts.protectedWords sp cursor c.ids.length (candidates trace lines c.ids data),
      load32 out.1.core.memory a=load32 s.memory a) ∧
    (∃ added : List Collision.Intercept, out.2.collected.toList=r.collected.toList++added) := by
  let h := initial s sp cursor lines objects trace c data stack list items ids ready layout
  have keep : ∀ j<c.ids.length, (h.candidates j).crosses=true → (h.candidates j).Continues := by
    intro j _ _
    exact E1M1ScanContracts.candidate_continues trace lines c.ids[j]! (data j)
  obtain ⟨⟨n,hn,path⟩,runs,collected,frame⟩ :=
    OriginalLineMixedInvariant.through_sentinel s c.ids.length 0x2ba20 (E1M1ThingFinish.resolve lines objects) h r f tracked keep items.sentinel
  have visits := OriginalLineVisitedRun.finished_represents s c.ids.length 0x2ba20
    (E1M1ThingFinish.resolve lines objects) h lines 475
    (visit_layout s sp cursor lines objects trace c data stack list items ids ready layout stamps)
    f r tracked keep epoch seen size represented
  exact ⟨⟨n,hn,X86CodeMemory.lift_success (path.transfer _ [] contains_scan (by simp)) FloorCaller.cm⟩,
    runs,collected,visits,frame,run_prefix _ _ _ _ _⟩
end Scan
end Doom.Proofs.E1M1NextLineScan
