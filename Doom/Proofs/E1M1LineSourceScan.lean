import Doom.Proofs.E1M1LineSourceLoop
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1LineSourceScan
open Verification X86 X86Memory X86Control BlockSummary
open E1M1ScanContracts (LineData candidates candidate)
open E1M1NextCallbackReady (Ready)
open OriginalLineVisits (Represents markPrefix)
attribute [local irreducible] load32

/-- The scan's source list includes every raw entry, including the leading zero
and any repeats. It is not a list of just the accepted intersections. -/
theorem candidate_ids (trace : Collision.Divline) (lines : Word) (ids : List Nat)
    (data : Nat → LineData) :
    ((List.range' 0 ids.length).map (candidates trace lines ids data)).map
      OriginalLineMixedInvariant.Candidate.id=ids := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp [candidates,candidate,getElem!_pos, h₂]

section Scan
variable (s : X86Memory.State) (sp cursor lines : Word) (objects : Nat → Word)
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
    (sceneLines : Array Collision.Line)
    (lookup : ∀ i : Fin c.ids.length, sceneLines[c.ids[i.val]]?=some (data i.val).line)
include stack list items ids ready layout stamps tracked size represented lookup

/-- The actual DOS scan result agrees with the aiming line-cell source fragment,
including the visited array and complete PathResult, under initial contracts. -/
theorem source_result :
    E1M1LineSourceLoop.lineCell trace sceneLines c.ids.toArray seen r=.ok
      (markPrefix (candidates trace lines c.ids data) c.ids.length 0 seen,
       (E1M1NextLineScan.result s lines trace c data f r).2) := by
  let h := E1M1NextLineScan.initial s sp cursor lines objects trace c data stack list items ids ready layout
  have vl := E1M1NextLineScan.visit_layout s sp cursor lines objects trace c data stack list items ids ready layout stamps
  have inv := OriginalLineMixedInvariant.start s c.ids.length 0x2ba20 (E1M1ThingFinish.resolve lines objects) h r f tracked
  have collected := E1M1LineCollect.collect_run s c.ids.length 0x2ba20 lines
    (E1M1ThingFinish.resolve lines objects) h 475 vl 0 ⟨s,f,0x2c57f⟩ r inv
    c.ids.length (by omega) (by intros; rfl) epoch seen size represented
  have member : ∀ x∈(List.range' 0 c.ids.length).map h.candidates,
      ∃ i, i<c.ids.length ∧ x=candidates trace lines c.ids data i := by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
    exact ⟨i,by simpa using hi,rfl⟩
  have source := E1M1LineSourceLoop.source_collect trace sceneLines
    ((List.range' 0 c.ids.length).map h.candidates) seen r
    (by intro x hx; obtain ⟨i,hi,rfl⟩ := member x hx; rfl)
    (by
      intro x hx; obtain ⟨i,hi,rfl⟩ := member x hx
      have bound : c.ids[i]<475 := ids ⟨i,hi⟩
      simpa [candidates,candidate,getElem!_pos,hi] using (show c.ids[i]<32768 by omega))
    (by
      intro x hx; obtain ⟨i,hi,rfl⟩ := member x hx
      simpa [candidates,candidate,getElem!_pos,hi] using lookup ⟨i,hi⟩)
  change E1M1LineSourceLoop.lineCell trace sceneLines
    (((List.range' 0 c.ids.length).map (candidates trace lines c.ids data)).map
      OriginalLineMixedInvariant.Candidate.id).toArray seen r=_ at source
  rw [candidate_ids] at source
  exact source.trans collected

/-- Execution and source result share the same output, not merely matching hit
counts. Machine record representation and stamp representation are retained. -/
theorem execution :
    let out := E1M1NextLineScan.result s lines trace c data f r
    (∃ steps≤281*c.ids.length+7, X86CodeMemory.Prefix FloorCaller.cm E1M1FiringAdvance.program [] steps
      ⟨s,f,0x2c57f⟩ out.1) ∧
    E1M1LineSourceLoop.lineCell trace sceneLines c.ids.toArray seen r=.ok
      (markPrefix (candidates trace lines c.ids data) c.ids.length 0 seen,out.2) ∧
    OriginalLineCollection.Tracks out.1.core 0x2ba20 (E1M1ThingFinish.resolve lines objects) out.2.collected 0 ∧
    Represents out.1.core.memory lines epoch (markPrefix (candidates trace lines c.ids data) c.ids.length 0 seen) := by
  have machine := E1M1NextLineScan.execution s sp cursor lines objects trace c data stack list items ids ready layout stamps f r tracked epoch seen size represented
  exact ⟨machine.1,source_result s sp cursor lines objects trace c data stack list items ids ready layout stamps f r tracked epoch seen size represented sceneLines lookup,machine.2.2.1,machine.2.2.2.1⟩
end Scan
end Doom.Proofs.E1M1LineSourceScan
