import Doom.Proofs.E1M1FiringNextScan
import Doom.Proofs.OriginalLineVisitedRun
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1FiringLineVisits
open Verification X86 X86Memory X86Control BlockSummary
open E1M1ScanMemory (firstScan)
open E1M1ScanGeometry (path linePointer)
open E1M1ScanContracts (LineData candidates)
open OriginalLineVisits (Represents markPrefix stamp)
attribute [local irreducible] load32

/-- The initial query starts with all bits false; mark every visited candidate
in original order, including the BLOCKMAP's leading linedef zero. -/
def seenAfter (trace : Collision.Divline) (lines : Word) (c : E1M1PathMap.Cell)
    (data : Nat → LineData) : Array Bool :=
  markPrefix (candidates trace lines c.ids data) c.ids.length 0 (Array.replicate 475 false)

theorem seen_size (trace : Collision.Divline) (lines : Word) (c : E1M1PathMap.Cell)
    (data : Nat → LineData) : (seenAfter trace lines c data).size=475 := by
  simp only [seenAfter,OriginalLineVisitedRun.mark_size,Array.size_replicate]

/-- The original leading linedef zero is marked by the first cell, whether
or not it contributed an intercept. Every later cell can reuse this fact. -/
theorem seen_zero (trace : Collision.Divline) (lines : Word) (c : E1M1PathMap.Cell)
    (data : Nat → LineData) (words : Array Nat) (valid : c.Valid words) :
    (seenAfter trace lines c data)[0]! =true := by
  have head := valid.2.1
  cases ids : c.ids with
  | nil => simp [ids] at head
  | cons id rest =>
    have zero : id=0 := by simpa [ids] using head
    subst id
    have marked := OriginalLineVisitedRun.first_marked (candidates trace lines c.ids data)
      rest.length 0 (Array.replicate 475 false) (by simp [candidates,E1M1ScanContracts.candidate,ids])
    simpa [seenAfter,ids,candidates,E1M1ScanContracts.candidate] using marked

section Firing
variable (gun : Fire.Gun) (s : X86Memory.State) (weapon : Weapon.Context)
    (actor : Word) (thing : Collision.SolidThing) (angle : Angle) (ox oy : Fixed)
    (xout yout : Int32 × Fixed × Fixed) (base lines : Word) (words : Array Nat)
    (c : E1M1PathMap.Cell) (w h : Nat) (data : Nat → LineData)
    (input : E1M1FiringScan.Inputs gun s weapon actor thing angle ox oy xout yout base lines words c w h data)
include input


attribute [local irreducible] Collision.SolidThing.attackEndpoint


/-- Reuse the assembled first-scan contract and its initial layout. There is
no assumed reached stamp pointer, callback stack or per-line result. -/
theorem visit_layout (stamps : E1M1ScanContracts.Stamps (s.regs 4) lines) :
    OriginalLineVisits.Layout (firstScan gun s).core
      (E1M1FiringScan.initial gun s weapon actor thing angle ox oy xout yout base lines words c w h data input) lines 475 := by
  have run := E1M1FiringGeometry.first_scan_execution gun s none weapon input.firing actor thing angle ox oy input.geometry
    xout yout input.okX input.okY base lines words c w h input.map input.cursorSafe input.inside input.valid input.selected
  have sp := E1M1ScanGeometry.firing_stack gun s actor thing angle ox oy input.geometry xout yout input.okX input.okY
    base lines words w h input.map input.inside
  refine ⟨by decide,?_,?_,?_,?_,?_,?_⟩
  · intro i hi
    change c.ids[i]!<475
    rw [getElem!_pos c.ids i hi]
    exact (input.valid.2.2.2.1 ⟨i,hi⟩).1
  · intro i hi
    change OriginalLineDispatch.pointer (OriginalLineMixedInvariant.atIndex (firstScan gun s).core i)=linePointer lines c.ids[i]!
    rw [getElem!_pos c.ids i hi]
    exact run.2.1.pointers ⟨i,hi⟩ (Fixed.ofInt 0)
  · intro j hj
    rw [sp]
    simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using input.layout.stampCall j hj
  · intro i _ j hj
    exact E1M1ScanGeometry.side_safe (firstScan gun s).core (s.regs 4) sp i _ (stamps.side j hj)
  · intro i _ j hj
    exact E1M1ScanGeometry.scratch_safe (firstScan gun s).core (s.regs 4) sp i _ (stamps.scratch j hj)
  · intro j hj
    exact ⟨fun k hk off ho => FloorCaller.apart_symm (input.layout.storage.stamps k hk off ho j hj),stamps.metadata j hj⟩

set_option backward.isDefEq.respectTransparency true
/-- The complete continuing line scan updates the represented bitset. Initial
bits refer to the incremented epoch, before any firing code executes. -/
theorem scan_seen (stamps : E1M1ScanContracts.Stamps (s.regs 4) lines)
    (epochBefore : E1M1ScanMemory.BeforeInit gun s (0x13580#32))
    (epochAfter : E1M1PathMapSetup.StackSafe (s.regs 4-(112#32)) (0x13580#32))
    (stampSetup : ∀ j<475, E1M1PathMapFiring.Safe gun s (stamp lines j))
    (seen : Array Bool) (size : seen.size=475)
    (bits : ∀ j<475, (load32 s.memory (stamp lines j)=load32 s.memory 0x13580+1 ↔ seen[j]! = true)) :
    Represents (E1M1ScanReturn.finished gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).1.core.memory lines
      (load32 s.memory 0x13580+1)
      (markPrefix (candidates (path thing angle ox oy).trace lines c.ids data) c.ids.length 0 seen) := by
  have represented := OriginalLineVisits.firing_represents gun s actor thing angle ox oy input.geometry
    epochBefore epochAfter lines seen (fun j hj => stampSetup j (by omega)) (fun j hj => bits j (by omega))
  have run := E1M1FiringGeometry.first_scan_execution gun s none weapon input.firing actor thing angle ox oy input.geometry
    xout yout input.okX input.okY base lines words c w h input.map input.cursorSafe input.inside input.valid input.selected
  let contract := E1M1FiringScan.initial gun s weapon actor thing angle ox oy xout yout base lines words c w h data input
  have keep : ∀ j<c.ids.length, (contract.candidates j).crosses=true → (contract.candidates j).Continues := by
    intro j _ _
    exact E1M1ScanContracts.candidate_continues (path thing angle ox oy).trace lines c.ids[j]! (data j)
  exact OriginalLineVisitedRun.finished_represents (firstScan gun s).core c.ids.length 0x2ba20
    (E1M1PathMap.resolve lines) contract lines 475 (visit_layout gun s weapon actor thing angle ox oy xout yout base lines words c w h data input stamps)
    (firstScan gun s).flags {trace := (path thing angle ox oy).trace} run.2.2 keep
    (load32 s.memory 0x13580+1) seen size represented

/-- Freshness must be supplied for the *incremented* epoch. Counter wrap alone
cannot establish it. With freshness the source's all-false bitset is justified. -/
theorem fresh_scan (stamps : E1M1ScanContracts.Stamps (s.regs 4) lines)
    (epochBefore : E1M1ScanMemory.BeforeInit gun s (0x13580#32))
    (epochAfter : E1M1PathMapSetup.StackSafe (s.regs 4-(112#32)) (0x13580#32))
    (stampSetup : ∀ j<475, E1M1PathMapFiring.Safe gun s (stamp lines j))
    (fresh : ∀ j<475, load32 s.memory (stamp lines j)≠load32 s.memory 0x13580+1) :
    Represents (E1M1ScanReturn.finished gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).1.core.memory lines
      (load32 s.memory 0x13580+1) (seenAfter (path thing angle ox oy).trace lines c data) := by
  apply scan_seen gun s weapon actor thing angle ox oy xout yout base lines words c w h data input stamps epochBefore epochAfter stampSetup (Array.replicate 475 false) (by simp)
  intro j hj
  rw [getElem!_pos _ j (by simpa using hj),Array.getElem_replicate]
  simp only [Bool.false_eq_true,iff_false]
  exact fresh j hj
end Firing
end Doom.Proofs.E1M1FiringLineVisits
