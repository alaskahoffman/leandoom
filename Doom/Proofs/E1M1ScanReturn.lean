import Doom.Proofs.E1M1FiringScan
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1ScanReturn
open Verification X86 X86Memory X86Control BlockSummary
open E1M1ScanMemory (firstScan)
open E1M1ScanGeometry (path linePointer)
open E1M1ScanContracts (LineData candidates)
open OriginalLineMixedInvariant (Initial ArraySafe atIndex)

/-- Extend immutable-word preservation without changing any candidate or scan. -/
def protect (s : X86Memory.State) (n : Nat) (base : Word) (resolve : Collision.Intercept → Word)
    (h : Initial s n base resolve) (extra : List Word)
    (separated : ∀ i<n, ∀ a∈extra,
      OriginalLineDispatch.Safe (atIndex s i) a ∧
      OriginalLineCrossing.SideSafe (OriginalLineDispatch.view (atIndex s i)) a ∧
      OriginalLineCrossing.ScratchSafe (OriginalLineDispatch.view (atIndex s i)) a)
    (array : ∀ a∈extra, ArraySafe base a) : Initial s n base resolve :=
  { h with words := h.words++extra
           listWords := fun i hi => List.mem_append_left _ (h.listWords i hi)
           fixedWords := fun a ha => List.mem_append_left _ (h.fixedWords a ha)
           reads := fun i hi a ha => List.mem_append_left _ (h.reads i hi a ha)
           separated := fun i hi a ha => (List.mem_append.mp ha).elim (h.separated i hi a) (separated i hi a)
           arrayWords := fun a ha => (List.mem_append.mp ha).elim (h.arrayWords a) (array a) }

theorem protect_finished (s : X86Memory.State) (n : Nat) (base : Word) (resolve : Collision.Intercept → Word)
    (h : Initial s n base resolve) (extra : List Word)
    (separated : ∀ i<n, ∀ a∈extra,
      OriginalLineDispatch.Safe (atIndex s i) a ∧
      OriginalLineCrossing.SideSafe (OriginalLineDispatch.view (atIndex s i)) a ∧
      OriginalLineCrossing.ScratchSafe (OriginalLineDispatch.view (atIndex s i)) a)
    (array : ∀ a∈extra, ArraySafe base a) (f : Option Flags) (r : Collision.PathResult) :
    OriginalLineMixedInvariant.finished s n base resolve (protect s n base resolve h extra separated array) f r=
      OriginalLineMixedInvariant.finished s n base resolve h f r := rfl

def returnWords (sp : Word) : List Word := [sp-(120#32),sp-(116#32)]

/-- Only heap/metadata separation is additional: callback stack writes are
strictly below the two saved words, even with modular stack wraparound. -/
structure ReturnSafe (sp lines : Word) : Prop where
  stamps : ∀ a∈returnWords sp, ∀ id<475, Apart a (OriginalLineVisits.stamp lines id)
  array : ∀ a∈returnWords sp, ArraySafe 0x2ba20 a

theorem stack_protected (sp lines a : Word) (member : a∈returnWords sp)
    (stamps : ∀ id<475, Apart a (OriginalLineVisits.stamp lines id)) :
    E1M1ScanContracts.Protected sp lines a := by
  refine ⟨stamps,?_,?_,?_⟩
  all_goals simp only [returnWords,List.mem_cons,List.not_mem_nil,or_false] at member
  · rcases member with rfl|rfl
    all_goals simpa only [BitVec.sub_eq_add_neg] using
      OriginalPathXStep.apart_translate sp _ _ (by unfold Apart; decide)
  · intro off ho
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
    rcases member with rfl|rfl <;> rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simpa only [BitVec.sub_eq_add_neg,BitVec.add_assoc] using
      OriginalPathXStep.apart_translate sp _ _ (by unfold Apart; decide)
  · intro off ho
    simp only [OriginalLineTail.stackOffsets,List.mem_cons,List.not_mem_nil,or_false] at ho
    rcases member with rfl|rfl <;> rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simpa only [BitVec.sub_eq_add_neg,BitVec.add_assoc] using
      OriginalPathXStep.apart_translate sp _ _ (by unfold Apart; decide)

/-- Prologue stores preserve their distinct neighboring saved words. -/
theorem prologue_words (s : X86Memory.State) :
    load32 (OriginalLineBounds.entry s).memory (s.regs 4-(4#32))=s.regs 7 ∧
    load32 (OriginalLineBounds.entry s).memory (s.regs 4)=load32 s.memory (s.regs 4) := by
  have apart (a b : Word) (h : Apart a b) : Apart (s.regs 4+a) (s.regs 4+b) :=
    OriginalPathXStep.apart_translate _ a b h
  constructor
  · change load32 (store32 (store32 _ (s.regs 4-4) _) (s.regs 4-8) _) (s.regs 4-4)=_
    rw [load_store_apart _ _ _ _ (by simpa only [BitVec.sub_eq_add_neg] using apart (-4) (-8) (by unfold Apart; decide)),load_store]
  · exact OriginalLineBounds.entry_frame s (s.regs 4)
      (by change Apart (s.regs 4) (s.regs 4-(4#32)); simpa [BitVec.sub_eq_add_neg] using apart (0#32) (-(4#32)) (by unfold Apart; decide))
      (by change Apart (s.regs 4) (s.regs 4-(8#32)); simpa [BitVec.sub_eq_add_neg] using apart (0#32) (-(8#32)) (by unfold Apart; decide))

/-- These are values written by CALL/PUSH, not values assumed in memory. -/
theorem caller_words (s : X86Memory.State) :
    load32 (E1M1PathMapCaller.scan s).core.memory (s.regs 4-(8#32))=s.regs 7 ∧
    load32 (E1M1PathMapCaller.scan s).core.memory (s.regs 4-(4#32))=(0x2ca94#32) := by
  have mem : (E1M1PathMapCaller.scan s).core.memory=(OriginalLineBounds.entry (E1M1PathMapCaller.call s).core).memory :=
    (OriginalLineCell.lookup_observe _).2.1.trans (E1M1PathMapBounds.result_memory _)
  rw [mem]
  have words := prologue_words (E1M1PathMapCaller.call s).core
  rw [E1M1PathMapCaller.call_stack] at words
  have saved : (E1M1PathMapCaller.call s).core.regs 7=s.regs 7 := by
    simp [E1M1PathMapCaller.call,OriginalPathCell.called,OriginalPathCell.c3,OriginalPathCell.c2,
      OriginalPathCell.c1,X86Routine.pushWord,put,write]
  exact ⟨by simpa only [BitVec.sub_sub,show (4#32)+(4#32)=(8#32) by decide,saved] using words.1,
    words.2.trans (E1M1PathMapCaller.call_return s)⟩

/-- Both instructions of the caller's success test are in the existing program. -/
theorem contains_dispatch (pc : Nat) (h : OriginalPathCell.program pc≠none) :
    OriginalLineMixedInvariant.program pc=OriginalPathCell.program pc := by
  have a := E1M1PathMapCaller.contains_dispatch pc h
  have b := E1M1PathMapCaller.contains_caller pc (by rw [a]; exact h)
  exact ((E1M1FiringScan.contains_firing pc (by rw [b,a]; exact h)).trans b).trans a

section Firing
variable (gun : Fire.Gun) (s : X86Memory.State) (weapon : Weapon.Context)
    (actor : Word) (thing : Collision.SolidThing) (angle : Angle) (ox oy : Fixed)
    (xout yout : Int32 × Fixed × Fixed) (base lines : Word) (words : Array Nat)
    (c : E1M1PathMap.Cell) (w h : Nat) (data : Nat → LineData)
    (input : E1M1FiringScan.Inputs gun s weapon actor thing angle ox oy xout yout base lines words c w h data)
include input


/-- Actual saved-frame contents at first scan entry, derived from the caller. -/
theorem firing_frame :
    load32 (firstScan gun s).core.memory ((firstScan gun s).core.regs 4+(4#32))=
      (E1M1PathGridSetup.firstGrid gun s).core.regs 7 ∧
    load32 (firstScan gun s).core.memory ((firstScan gun s).core.regs 4+(8#32))=(0x2ca94#32) := by
  have geo := E1M1AimGeometry.path_inputs _ thing angle _ ox oy
    (E1M1FiringGeometry.query_geometry gun s actor thing angle ox oy input.geometry)
  have maps := E1M1PathMapSetup.map_at_grid _ ox oy _ _ _ _ geo base lines words w h
    (E1M1PathMapQuery.map_at_traversal _ base lines words w h
      (E1M1PathMapFiring.map_at_query gun s base lines words w h input.map))
  have grid := (E1M1PathGridSetup.grid_observation_from_init _ ox oy _ _ _ _ geo xout yout input.okX input.okY).2
  have sp := E1M1ScanGeometry.caller_stack _ _ _ w h maps.1 grid.mapX grid.mapY input.inside
  change (firstScan gun s).core.regs 4=(E1M1PathGridSetup.firstGrid gun s).core.regs 4-(12#32) at sp
  rw [sp]
  simpa [E1M1ScanMemory.firstScan,BitVec.sub_eq_add_neg,BitVec.add_assoc] using caller_words (E1M1PathGridSetup.firstGrid gun s).core

/-- Add protection for the saved EDI and return PC using firing-entry addresses. -/
def framed (safe : ReturnSafe (s.regs 4) lines) :
    Initial (firstScan gun s).core c.ids.length 0x2ba20 (E1M1PathMap.resolve lines) := by
  let original := E1M1FiringScan.initial gun s weapon actor thing angle ox oy xout yout base lines words c w h data input
  apply protect _ _ _ _ original (returnWords (s.regs 4)) _ safe.array
  have run := E1M1FiringGeometry.first_scan_execution gun s none weapon input.firing actor thing angle ox oy input.geometry
    xout yout input.okX input.okY base lines words c w h input.map input.cursorSafe input.inside input.valid input.selected
  have sp := E1M1ScanGeometry.firing_stack gun s actor thing angle ox oy input.geometry xout yout input.okX input.okY
    base lines words w h input.map input.inside
  intro i hi a ha
  exact E1M1ScanContracts.protection _ (s.regs 4) lines sp i _ (input.valid.2.2.2.1 ⟨i,hi⟩).1
    (run.2.1.pointers ⟨i,hi⟩ (Fixed.ofInt 0)) a (stack_protected _ _ _ ha (safe.stamps a ha))

def finished : X86Control.State × Collision.PathResult :=
  OriginalLineMixedInvariant.finished (firstScan gun s).core c.ids.length 0x2ba20 (E1M1PathMap.resolve lines)
    (E1M1FiringScan.initial gun s weapon actor thing angle ox oy xout yout base lines words c w h data input)
    (firstScan gun s).flags { trace := (path thing angle ox oy).trace }

set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] Collision.SolidThing.attackEndpoint

/-- Extending preservation has no effect on the executed scan or pure result. -/
theorem framed_finished (safe : ReturnSafe (s.regs 4) lines) :
    OriginalLineMixedInvariant.finished (firstScan gun s).core c.ids.length 0x2ba20 (E1M1PathMap.resolve lines)
      (framed gun s weapon actor thing angle ox oy xout yout base lines words c w h data input safe)
      (firstScan gun s).flags { trace := (path thing angle ox oy).trace }=
    finished gun s weapon actor thing angle ox oy xout yout base lines words c w h data input := rfl

/-- The real sentinel restores the caller's SP and EDI and returns true to the
actual line-return instruction, rather than to an assumed address. -/
theorem parent_return (safe : ReturnSafe (s.regs 4) lines) :
    let out := (finished gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).1
    out.core.regs 0=(1#32) ∧ out.core.regs 4=s.regs 4-(112#32) ∧
    out.core.regs 7=(E1M1PathGridSetup.firstGrid gun s).core.regs 7 ∧ out.pc=0x2ca94 := by
  let contract := framed gun s weapon actor thing angle ox oy xout yout base lines words c w h data input safe
  have run := E1M1FiringGeometry.first_scan_execution gun s none weapon input.firing actor thing angle ox oy input.geometry
    xout yout input.okX input.okY base lines words c w h input.map input.cursorSafe input.inside input.valid input.selected
  have sp := E1M1ScanGeometry.firing_stack gun s actor thing angle ox oy input.geometry xout yout input.okX input.okY
    base lines words w h input.map input.inside
  have keeps : ∀ i<c.ids.length, (contract.candidates i).crosses=true → (contract.candidates i).Continues := by
    intro i _ _
    dsimp only [contract,framed,protect,E1M1FiringScan.initial,E1M1ScanContracts.initial]
    exact E1M1ScanContracts.candidate_continues (path thing angle ox oy).trace lines c.ids[i]! (data i)
  have member (off : Word) (ho : off∈[(4#32),8]) : (firstScan gun s).core.regs 4+off∈contract.words := by
    apply List.mem_append_right
    rw [sp]
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
    rcases ho with rfl|rfl <;> simp [returnWords,BitVec.sub_eq_add_neg,BitVec.add_assoc]
  have ret := OriginalLineMixedInvariant.parent_return (firstScan gun s).core c.ids.length 0x2ba20
    (E1M1PathMap.resolve lines) contract { trace := (path thing angle ox oy).trace } (firstScan gun s).flags
    run.2.2 keeps (member 4 (by simp)) (member 8 (by simp))
  have frame := firing_frame gun s weapon actor thing angle ox oy xout yout base lines words c w h data input
  change _ ∧ _ ∧ _ ∧ _ at ret
  dsimp only [contract] at ret
  rw [framed_finished,frame.1,frame.2,sp] at ret
  simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using ret

/-- Continuous execution reaches the thing-iterator gate after the first line
list, preserving its collected intercepts. This does not execute thing scanning. -/
theorem firing_to_things (safe : ReturnSafe (s.regs 4) lines) (f : Option Flags) :
    let scan := finished gun s weapon actor thing angle ox oy xout yout base lines words c w h data input
    let out := OriginalPathCell.resumed true scan.1.core
    (∃ steps≤377+281*c.ids.length, X86CodeMemory.Prefix FloorCaller.cm OriginalLineMixedInvariant.program [] steps
      ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ out) ∧
    out.pc=0x2ca9c ∧ out.core.regs 4=s.regs 4-(112#32) ∧
    out.core.regs 7=(E1M1PathGridSetup.firstGrid gun s).core.regs 7 ∧
    OriginalLineCollection.Tracks out.core 0x2ba20 (E1M1PathMap.resolve lines) scan.2.collected 0 := by
  let scan := finished gun s weapon actor thing angle ox oy xout yout base lines words c w h data input
  obtain ⟨⟨n,hn,setup⟩,_,collected⟩ :=
    E1M1FiringScan.firing_through_sentinel gun s weapon actor thing angle ox oy xout yout base lines words c w h data input f
  have ret := parent_return gun s weapon actor thing angle ox oy xout yout base lines words c w h data input safe
  change scan.1.core.regs 0=_ ∧ _ ∧ _ ∧ scan.1.pc=_ at ret
  have tail := (OriginalPathCell.resume_execution true scan.1.core scan.1.flags).transfer
    OriginalLineMixedInvariant.program [] contains_dispatch (by simp)
  change X86Routine.Prefix _ [] 2 ⟨_,_,0x2ca94⟩ _ at tail
  rw [OriginalPathXStep.at_pc _ _ ret.2.2.2] at tail
  refine ⟨⟨n+2,by omega,E1M1PspriteStep.prefix_trans setup (X86CodeMemory.lift_success tail FloorCaller.cm)⟩,?_,ret.2.1,ret.2.2.1,collected⟩
  change (if scan.1.core.regs 0=0 then 0x2cb0b else 0x2ca9c)=_
  rw [ret.1]; decide
end Firing
end Doom.Proofs.E1M1ScanReturn
