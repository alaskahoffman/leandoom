import Doom.Proofs.E1M1ScanReturn
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1ThingGate
open Verification X86 X86Memory X86Control BlockSummary
open E1M1ScanMemory (firstScan)
open E1M1ScanGeometry (path)
open E1M1ScanContracts (LineData)
open OriginalLineMixedInvariant (Initial ArraySafe)

def flagWord (sp : Word) : Word := sp-(48#32)

/-- The option word lies above every stack write in the first line scan. -/
theorem flag_protected (sp lines : Word)
    (stamps : ∀ id<475, Apart (flagWord sp) (OriginalLineVisits.stamp lines id)) :
    E1M1ScanContracts.Protected sp lines (flagWord sp) := by
  refine ⟨stamps,?_,?_,?_⟩
  · simpa only [flagWord,BitVec.sub_eq_add_neg] using
      OriginalPathXStep.apart_translate sp _ _ (by unfold Apart; decide)
  · intro off ho
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
    rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simpa only [flagWord,BitVec.sub_eq_add_neg,BitVec.add_assoc] using
      OriginalPathXStep.apart_translate sp _ _ (by unfold Apart; decide)
  · intro off ho
    simp only [OriginalLineTail.stackOffsets,List.mem_cons,List.not_mem_nil,or_false] at ho
    rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simpa only [flagWord,BitVec.sub_eq_add_neg,BitVec.add_assoc] using
      OriginalPathXStep.apart_translate sp _ _ (by unfold Apart; decide)

structure FlagSafe (sp lines : Word) : Prop where
  stamps : ∀ id<475, Apart (flagWord sp) (OriginalLineVisits.stamp lines id)
  array : ArraySafe 0x2ba20 (flagWord sp)

/-- The line iterator's CALL and prologue cannot overwrite the caller's options. -/
theorem caller_flag (s : X86Memory.State) :
    load32 (E1M1PathMapCaller.scan s).core.memory (s.regs 4+(64#32))=
      load32 s.memory (s.regs 4+(64#32)) := by
  apply E1M1ScanMemory.caller_frame
  constructor
  · simpa only [BitVec.sub_eq_add_neg] using OriginalPathXStep.apart_translate (s.regs 4) _ _ (by unfold Apart; decide)
  constructor
  · simpa only [BitVec.sub_eq_add_neg] using OriginalPathXStep.apart_translate (s.regs 4) _ _ (by unfold Apart; decide)
  · simpa only [BitVec.sub_eq_add_neg] using OriginalPathXStep.apart_translate (s.regs 4) _ _ (by unfold Apart; decide)

/-- A thing CALL only stores its return word. Existing line intercepts and their
cursor survive under the same bounded-array separation used for the saved PC. -/
theorem call_collection (s : X86Memory.State) (f : Option Flags) (base : Word)
    (resolve : Collision.Intercept → Word) (hits : Array Collision.Intercept) (reserve : Nat)
    (tracked : OriginalLineCollection.Tracks s base resolve hits reserve)
    (safe : ArraySafe base (s.regs 4-(4#32))) :
    OriginalLineCollection.Tracks (OriginalPathCell.called false s f).core base resolve hits reserve := by
  have cursor := FloorCaller.apart_symm safe.2
  have record (i : Nat) (hi : i<hits.size) (off : Word) (ho : off∈[(0#32),4,8]) :
      Apart (OriginalLineCollection.slot base i off) (s.regs 4-(4#32)) :=
    FloorCaller.apart_symm (safe.1 i (by have room:=tracked.room; omega) off ho)
  refine ⟨?_,?_,tracked.room⟩
  · intro i hi
    have old := tracked.encoded i hi
    unfold OriginalLineFinish.RecordAt at old ⊢
    refine ⟨?_,?_,?_⟩
    · exact (OriginalPathCell.call_frame false s f _ (by
        change Apart (base+BitVec.ofNat 32 (12*i)) (s.regs 4-(4#32))
        simpa only [OriginalLineCollection.slot,BitVec.add_zero] using record i hi (0#32) (by simp))).trans old.1
    · exact (OriginalPathCell.call_frame false s f _ (record i hi (4#32) (by simp))).trans old.2.1
    · exact (OriginalPathCell.call_frame false s f _ (record i hi (8#32) (by simp))).trans old.2.2
  · change load32 (OriginalPathCell.called false s f).core.memory (0x2c028#32)=_
    rw [OriginalPathCell.call_frame false s f _ cursor]
    exact tracked.cursor

section Firing
variable (gun : Fire.Gun) (s : X86Memory.State) (weapon : Weapon.Context)
    (actor : Word) (thing : Collision.SolidThing) (angle : Angle) (ox oy : Fixed)
    (xout yout : Int32 × Fixed × Fixed) (base lines : Word) (words : Array Nat)
    (c : E1M1PathMap.Cell) (w h : Nat) (data : Nat → LineData)
    (input : E1M1FiringScan.Inputs gun s weapon actor thing angle ox oy xout yout base lines words c w h data)
include input

/-- First grid SP is derived from aim and path setup, not assumed at the gate. -/
theorem grid_stack : (E1M1PathGridSetup.firstGrid gun s).core.regs 4=s.regs 4-(112#32) := by
  have geo := E1M1AimGeometry.path_inputs _ thing angle _ ox oy
    (E1M1FiringGeometry.query_geometry gun s actor thing angle ox oy input.geometry)
  have sp := E1M1PathMapSetup.grid_stack _ ox oy _ _ _ _ geo
  change (E1M1PathGridSetup.firstGrid gun s).core.regs 4=(E1M1AimSetup.firstTraversal gun s).core.regs 4-(60#32) at sp
  rw [E1M1ScanMemory.firing_stack] at sp
  simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using sp

/-- Aim setup supplies both traversal bits, and every setup stage retains them. -/
theorem first_flag : load32 (firstScan gun s).core.memory (flagWord (s.regs 4))=(3#32) := by
  have query := E1M1FiringGeometry.query_geometry gun s actor thing angle ox oy input.geometry
  have geo := E1M1AimGeometry.path_inputs _ thing angle _ ox oy query
  have frame := E1M1PathCell.flags_from_init _ ox oy _ _ _ _ geo
  have supplied := congrArg (fun v => v.2.1)
    (OriginalAimSetup.call_frame _ (E1M1AimGeometry.setup_inputs _ thing angle _ ox oy query).separated)
  have word : load32 (E1M1PathGridSetup.firstGrid gun s).core.memory
      ((E1M1PathGridSetup.firstGrid gun s).core.regs 4+(64#32))=(3#32) := frame.trans supplied
  have keep := caller_flag (E1M1PathGridSetup.firstGrid gun s).core
  have sp := grid_stack gun s weapon actor thing angle ox oy xout yout base lines words c w h data input
  have value := keep.trans word
  rw [sp] at value
  simpa [firstScan,flagWord,BitVec.sub_eq_add_neg,BitVec.add_assoc] using value

/-- Preserve one extra caller-owned word without changing any scan candidate. -/
def flagged (safe : FlagSafe (s.regs 4) lines) :
    Initial (firstScan gun s).core c.ids.length 0x2ba20 (E1M1PathMap.resolve lines) := by
  let original := E1M1FiringScan.initial gun s weapon actor thing angle ox oy xout yout base lines words c w h data input
  apply E1M1ScanReturn.protect _ _ _ _ original [flagWord (s.regs 4)]
  · have run := E1M1FiringGeometry.first_scan_execution gun s none weapon input.firing actor thing angle ox oy input.geometry
      xout yout input.okX input.okY base lines words c w h input.map input.cursorSafe input.inside input.valid input.selected
    have sp := E1M1ScanGeometry.firing_stack gun s actor thing angle ox oy input.geometry xout yout input.okX input.okY
      base lines words w h input.map input.inside
    intro i hi a ha
    have eq : a=flagWord (s.regs 4) := by simpa using ha
    subst a
    exact E1M1ScanContracts.protection _ (s.regs 4) lines sp i _ (input.valid.2.2.2.1 ⟨i,hi⟩).1
      (run.2.1.pointers ⟨i,hi⟩ (Fixed.ofInt 0)) _ (flag_protected _ _ safe.stamps)
  · intro a ha
    have eq : a=flagWord (s.regs 4) := by simpa using ha
    subst a
    exact safe.array

set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] Collision.SolidThing.attackEndpoint

theorem flagged_finished (safe : FlagSafe (s.regs 4) lines) :
    OriginalLineMixedInvariant.finished (firstScan gun s).core c.ids.length 0x2ba20 (E1M1PathMap.resolve lines)
      (flagged gun s weapon actor thing angle ox oy xout yout base lines words c w h data input safe)
      (firstScan gun s).flags { trace := (path thing angle ox oy).trace }=
    E1M1ScanReturn.finished gun s weapon actor thing angle ox oy xout yout base lines words c w h data input := rfl

/-- All line-callback outcomes retain the option word, including insertion. -/
theorem scan_flag (safe : FlagSafe (s.regs 4) lines) :
    let out := E1M1ScanReturn.finished gun s weapon actor thing angle ox oy xout yout base lines words c w h data input
    load32 out.1.core.memory (flagWord (s.regs 4))=(3#32) := by
  let contract := flagged gun s weapon actor thing angle ox oy xout yout base lines words c w h data input safe
  have run := E1M1FiringGeometry.first_scan_execution gun s none weapon input.firing actor thing angle ox oy input.geometry
    xout yout input.okX input.okY base lines words c w h input.map input.cursorSafe input.inside input.valid input.selected
  have keeps : ∀ i<c.ids.length, (contract.candidates i).crosses=true → (contract.candidates i).Continues := by
    intro i _ _
    dsimp only [contract,flagged,E1M1ScanReturn.protect,E1M1FiringScan.initial,E1M1ScanContracts.initial]
    exact E1M1ScanContracts.candidate_continues (path thing angle ox oy).trace lines c.ids[i]! (data i)
  have ret := OriginalLineMixedInvariant.through_sentinel (firstScan gun s).core c.ids.length 0x2ba20
    (E1M1PathMap.resolve lines) contract { trace := (path thing angle ox oy).trace } (firstScan gun s).flags
    run.2.2 keeps run.2.1.sentinel
  have preserved := ret.2.2.2 (flagWord (s.regs 4)) (List.mem_append_right _ (by simp))
  dsimp only [contract] at preserved
  rw [flagged_finished] at preserved
  exact preserved.trans (first_flag gun s weapon actor thing angle ox oy xout yout base lines words c w h data input)

def gate := OriginalPathCell.resumed true
  (E1M1ScanReturn.finished gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).1.core

def called := OriginalPathCell.called false
  (gate gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).core
  (OriginalPathCell.gateFlags false (gate gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).core)

/-- The thing flag is derived after scanning, rather than assumed at the CALL. -/
theorem enabled (returns : E1M1ScanReturn.ReturnSafe (s.regs 4) lines) (safe : FlagSafe (s.regs 4) lines) :
    OriginalPathCell.enabled false (gate gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).core=true := by
  let out := E1M1ScanReturn.finished gun s weapon actor thing angle ox oy xout yout base lines words c w h data input
  have value := scan_flag gun s weapon actor thing angle ox oy xout yout base lines words c w h data input safe
  have sp := (E1M1ScanReturn.parent_return gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns).2.1
  have byte := congrArg (fun v : Word => v.extractLsb' 0 8) value
  rw [E1M1PathCell.low_byte] at byte
  change out.1.core.memory (flagWord (s.regs 4))=(3#8) at byte
  change (out.1.core.memory (out.1.core.regs 4+(64#32)) &&& (2#8) != 0)=true
  change out.1.core.regs 4=s.regs 4-(112#32) at sp
  rw [sp]
  have addr : s.regs 4-(112#32)+(64#32)=flagWord (s.regs 4) := by
    simp [flagWord,BitVec.sub_eq_add_neg,BitVec.add_assoc]
  rw [addr,byte]; decide

/-- Continuous execution now enters P_BlockThingsIterator. Coordinates are the
actual retained ESI/ECX values; identifying them with the intended map cell is
still a separate preservation obligation. No thing-list body is executed here. -/
theorem firing_call (returns : E1M1ScanReturn.ReturnSafe (s.regs 4) lines)
    (safe : FlagSafe (s.regs 4) lines) (f : Option Flags) :
    let prior := gate gun s weapon actor thing angle ox oy xout yout base lines words c w h data input
    let out := called gun s weapon actor thing angle ox oy xout yout base lines words c w h data input
    let hits := (E1M1ScanReturn.finished gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).2.collected
    (∃ steps≤383+281*c.ids.length, X86CodeMemory.Prefix FloorCaller.cm OriginalLineMixedInvariant.program [] steps
      ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ out) ∧
    out.pc=0x2c5a0 ∧ out.core.regs 4=s.regs 4-(116#32) ∧
    out.core.regs 0=prior.core.regs 6 ∧ out.core.regs 2=prior.core.regs 1 ∧ out.core.regs 3=(0x2c720#32) ∧
    load32 out.core.memory (out.core.regs 4)=(0x2cab1#32) ∧
    OriginalLineCollection.Tracks out.core 0x2ba20 (E1M1PathMap.resolve lines) hits 0 := by
  let prior := gate gun s weapon actor thing angle ox oy xout yout base lines words c w h data input
  obtain ⟨⟨n,hn,setup⟩,pc,sp,_,collection⟩ :=
    E1M1ScanReturn.firing_to_things gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns f
  have on := enabled gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns safe
  change OriginalPathCell.enabled false prior.core=true at on
  obtain ⟨m,hm,tail⟩ := OriginalPathCell.enter_execution false prior.core prior.flags
  simp only [OriginalPathCell.enter,on,↓reduceIte] at tail
  have tail := X86CodeMemory.lift_success (tail.transfer OriginalLineMixedInvariant.program [] E1M1ScanReturn.contains_dispatch (by simp)) FloorCaller.cm
  change X86CodeMemory.Prefix _ _ [] m ⟨_,_,0x2ca9c⟩ _ at tail
  change prior.pc=0x2ca9c at pc
  rw [OriginalPathXStep.at_pc _ _ pc] at tail
  have args := OriginalPathCell.call_inputs false prior.core (OriginalPathCell.gateFlags false prior.core)
  have array : ArraySafe (0x2ba20#32) (prior.core.regs 4-(4#32)) := by
    change prior.core.regs 4=s.regs 4-(112#32) at sp
    rw [sp]
    simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using
      returns.array (s.regs 4-(116#32)) (by simp [E1M1ScanReturn.returnWords])
  refine ⟨⟨n+m,by omega,E1M1PspriteStep.prefix_trans setup tail⟩,args.2.2.2.2.2,?_,args.1,args.2.1,args.2.2.1,?_,
    call_collection prior.core _ _ _ _ 0 collection array⟩
  · change prior.core.regs 4=s.regs 4-(112#32) at sp
    change (OriginalPathCell.called false prior.core (OriginalPathCell.gateFlags false prior.core)).core.regs 4=_
    calc
      _ = prior.core.regs 4-4 := args.2.2.2.1
      _ = _ := by rw [sp]; simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  · change load32 (OriginalPathCell.called false prior.core (OriginalPathCell.gateFlags false prior.core)).core.memory
      ((OriginalPathCell.called false prior.core (OriginalPathCell.gateFlags false prior.core)).core.regs 4)=_
    rw [args.2.2.2.1]
    exact args.2.2.2.2.1
end Firing
end Doom.Proofs.E1M1ThingGate
