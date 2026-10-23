import Doom.Proofs.E1M1ThingCoordinates
import Doom.Proofs.OriginalThingEntry
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1ThingEntry
open Verification X86 X86Memory X86Control BlockSummary
open E1M1ScanMemory (firstScan)
open E1M1ScanGeometry (path)
open E1M1ScanContracts (LineData)
open OriginalLineMixedInvariant (Initial ArraySafe)

def program : X86Routine.Program := fun pc =>
  match OriginalLineMixedInvariant.program pc with
  | some op => some op
  | none => OriginalThingEntry.program pc

theorem contains_prior (pc : Nat) (h : OriginalLineMixedInvariant.program pc≠none) :
    program pc=OriginalLineMixedInvariant.program pc := by
  unfold program
  cases eq : OriginalLineMixedInvariant.program pc <;> simp_all

theorem contains_thing (pc : Nat) (h : OriginalThingEntry.program pc≠none) :
    program pc=OriginalThingEntry.program pc := by
  have inside : 0x2c5a0≤pc ∧ pc<0x2c5eb := by
    by_cases hn : 0x2c5a0≤pc ∧ pc<0x2c5eb
    · exact hn
    have hn := hn
    have a : ¬(0x2c5a0≤pc ∧ pc<0x2c5c0) := by omega
    have b : ¬(0x2c5c0≤pc ∧ pc<0x2c5d2) := by omega
    have c : ¬(0x2c5e2≤pc ∧ pc<0x2c5eb) := by omega
    simp [OriginalThingEntry.program,OriginalThingEntry.bytesProgram,a,b,c] at h
  have absent : ∀ i : Fin 75, OriginalLineMixedInvariant.program (0x2c5a0+i.val)=none := by decide
  have eq : 0x2c5a0+(pc-0x2c5a0)=pc := by omega
  have empty : OriginalLineMixedInvariant.program pc=none := by
    simpa only [eq] using absent ⟨pc-0x2c5a0,by omega⟩
  simp [program,empty]

/-- Read separation at the common firing entry, including scan writes and the
two subsequent stores (CALL return word and thing callback slot). -/
structure ReadSafe (gun : Fire.Gun) (s : X86Memory.State) (lines a : Word) : Prop where
  before : E1M1PathMapFiring.Safe gun s a
  scan : E1M1ScanContracts.Protected (s.regs 4) lines a
  array : ArraySafe 0x2ba20 a
  call : Apart a (s.regs 4-(116#32))
  entry : Apart a (s.regs 4-(120#32))

/-- The sole iterator prologue store cannot damage the existing intercepts. -/
theorem collection (s : X86Memory.State) (base : Word) (resolve : Collision.Intercept → Word)
    (hits : Array Collision.Intercept) (reserve : Nat) (tracked : OriginalLineCollection.Tracks s base resolve hits reserve)
    (safe : ArraySafe base (s.regs 4-(4#32))) :
    OriginalLineCollection.Tracks (OriginalThingEntry.result s).core base resolve hits reserve := by
  have record (i : Nat) (hi : i<hits.size) (off : Word) (ho : off∈[(0#32),4,8]) :
      Apart (OriginalLineCollection.slot base i off) (s.regs 4-(4#32)) :=
    FloorCaller.apart_symm (safe.1 i (by have room:=tracked.room; omega) off ho)
  refine ⟨?_,?_,tracked.room⟩
  · intro i hi
    have old := tracked.encoded i hi
    unfold OriginalLineFinish.RecordAt at old ⊢
    refine ⟨?_,?_,?_⟩
    · exact (OriginalThingEntry.frame s _ (by
        simpa only [OriginalLineCollection.slot,BitVec.add_zero] using record i hi (0#32) (by simp))).trans old.1
    · exact (OriginalThingEntry.frame s _ (record i hi (4#32) (by simp))).trans old.2.1
    · exact (OriginalThingEntry.frame s _ (record i hi (8#32) (by simp))).trans old.2.2
  · exact (OriginalThingEntry.frame s _ (FloorCaller.apart_symm safe.2)).trans tracked.cursor

section Firing
variable (gun : Fire.Gun) (s : X86Memory.State) (weapon : Weapon.Context)
    (actor : Word) (thing : Collision.SolidThing) (angle : Angle) (ox oy : Fixed)
    (xout yout : Int32 × Fixed × Fixed) (base lines : Word) (words : Array Nat)
    (c : E1M1PathMap.Cell) (w h : Nat) (data : Nat → LineData)
    (input : E1M1FiringScan.Inputs gun s weapon actor thing angle ox oy xout yout base lines words c w h data)
include input

def extended (a : Word) (safe : ReadSafe gun s lines a) :
    Initial (firstScan gun s).core c.ids.length 0x2ba20 (E1M1PathMap.resolve lines) := by
  let original := E1M1FiringScan.initial gun s weapon actor thing angle ox oy xout yout base lines words c w h data input
  apply E1M1ScanReturn.protect _ _ _ _ original [a]
  · have run := E1M1FiringGeometry.first_scan_execution gun s none weapon input.firing actor thing angle ox oy input.geometry
      xout yout input.okX input.okY base lines words c w h input.map input.cursorSafe input.inside input.valid input.selected
    have sp := E1M1ScanGeometry.firing_stack gun s actor thing angle ox oy input.geometry xout yout input.okX input.okY
      base lines words w h input.map input.inside
    intro i hi b hb
    have eq : b=a := by simpa using hb
    subst b
    exact E1M1ScanContracts.protection _ (s.regs 4) lines sp i _ (input.valid.2.2.2.1 ⟨i,hi⟩).1
      (run.2.1.pointers ⟨i,hi⟩ (Fixed.ofInt 0)) a safe.scan
  · intro b hb
    have eq : b=a := by simpa using hb
    subst b
    exact safe.array

set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] Collision.SolidThing.attackEndpoint

theorem scan_read (a : Word) (safe : ReadSafe gun s lines a) :
    load32 (E1M1ScanReturn.finished gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).1.core.memory a=
      load32 s.memory a := by
  let contract := extended gun s weapon actor thing angle ox oy xout yout base lines words c w h data input a safe
  have run := E1M1FiringGeometry.first_scan_execution gun s none weapon input.firing actor thing angle ox oy input.geometry
    xout yout input.okX input.okY base lines words c w h input.map input.cursorSafe input.inside input.valid input.selected
  have keeps : ∀ i<c.ids.length, (contract.candidates i).crosses=true → (contract.candidates i).Continues := by
    intro i _ _
    dsimp only [contract,extended,E1M1ScanReturn.protect,E1M1FiringScan.initial,E1M1ScanContracts.initial]
    exact E1M1ScanContracts.candidate_continues (path thing angle ox oy).trace lines c.ids[i]! (data i)
  have ret := OriginalLineMixedInvariant.through_sentinel (firstScan gun s).core c.ids.length 0x2ba20
    (E1M1PathMap.resolve lines) contract {trace:=(path thing angle ox oy).trace} (firstScan gun s).flags
    run.2.2 keeps run.2.1.sentinel
  exact (ret.2.2.2 a (List.mem_append_right _ (by simp))).trans
    (E1M1ScanMemory.firing_frame gun s actor thing angle ox oy input.geometry a safe.before)

def result := OriginalThingEntry.result
  (E1M1ThingGate.called gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).core

variable (returns : E1M1ScanReturn.ReturnSafe (s.regs 4) lines) (flag : E1M1ThingGate.FlagSafe (s.regs 4) lines)
include returns

theorem call_read (a : Word) (safe : ReadSafe gun s lines a) :
    load32 (E1M1ThingGate.called gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).core.memory a=
      load32 s.memory a := by
  have sp := (E1M1ScanReturn.parent_return gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns).2.1
  apply (OriginalPathCell.call_frame false _ _ a ?_).trans
    (scan_read gun s weapon actor thing angle ox oy xout yout base lines words c w h data input a safe)
  change Apart a ((E1M1ScanReturn.finished gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).1.core.regs 4-(4#32))
  rw [sp]
  simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe.call

theorem call_stack :
    (E1M1ThingGate.called gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).core.regs 4=s.regs 4-(116#32) := by
  have sp := (E1M1ScanReturn.parent_return gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns).2.1
  change (E1M1ScanReturn.finished gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).1.core.regs 4-(4#32)=_
  rw [sp]
  simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]

include flag in
theorem firing_execution (f : Option Flags) :
    (∃ steps≤403+281*c.ids.length, X86CodeMemory.Prefix FloorCaller.cm program [] steps
      ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ (result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input)) ∧
    OriginalLineCollection.Tracks (result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).core
      0x2ba20 (E1M1PathMap.resolve lines)
      (E1M1ScanReturn.finished gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).2.collected 0 := by
  let called := E1M1ThingGate.called gun s weapon actor thing angle ox oy xout yout base lines words c w h data input
  obtain ⟨⟨n,hn,prior⟩,pc,sp,_,_,_,_,tracks⟩ :=
    E1M1ThingCoordinates.firing_call gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag f
  obtain ⟨m,hm,tail⟩ := OriginalThingEntry.execution called.core called.flags
  have prior := prior.transfer program [] contains_prior (by simp)
  rw [OriginalPathXStep.at_pc _ _ pc] at tail
  refine ⟨⟨n+m,by omega,E1M1PspriteStep.prefix_trans prior
    (X86CodeMemory.lift_success (tail.transfer program [] contains_thing (by simp)) FloorCaller.cm)⟩,?_⟩
  apply collection called.core _ _ _ 0 tracks
  rw [sp]
  simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using returns.array (s.regs 4-(120#32)) (by simp [E1M1ScanReturn.returnWords])

/-- The dynamic object-table reads are specified at firing entry; preservation
through every earlier stage is proved from byte separation. -/
def reads (links : Word) : List Word := [(0x2c0fc#32),0x2c110,0x2c0f8,
  links+(BitVec.ofNat 32 (Collision.pathCellIndex (path thing angle ox oy).startBlockX (path thing angle ox oy).startBlockY w) <<< 2)]

theorem bounds_inputs (links : Word) (safe : ∀ a∈reads thing angle ox oy w links, ReadSafe gun s lines a) :
    OriginalThingEntry.Inputs
      (E1M1ThingGate.called gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).core
      (path thing angle ox oy).startBlockX (path thing angle ox oy).startBlockY w h := by
  have coords := E1M1ThingCoordinates.call_coordinates gun s weapon actor thing angle ox oy xout yout base lines words c w h data input
  have sp := (OriginalPathCell.call_inputs false
    (E1M1ThingGate.gate gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).core none).2.2.2.1
  have oldsp := (E1M1ScanReturn.parent_return gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns).2.1
  refine ⟨coords.1,coords.2,?_,?_,input.map.widthBound,input.map.heightBound,?_⟩
  · exact (call_read gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns _ (safe _ (by simp [reads]))).trans input.map.width
  · exact (call_read gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns _ (safe _ (by simp [reads]))).trans input.map.height
  · intro a ha
    change Apart a ((E1M1ThingGate.gate gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).core.regs 4-(4#32)-(4#32))
    change Apart a ((E1M1ScanReturn.finished gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).1.core.regs 4-(4#32)-(4#32))
    rw [oldsp]
    have member : a∈reads thing angle ox oy w links := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl <;> simp [reads]
    simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using (safe a member).entry


theorem first_head (links object : Word)
    (safe : ∀ a∈reads thing angle ox oy w links, ReadSafe gun s lines a)
    (global : load32 s.memory (0x2c0f8#32)=links)
    (selected : load32 s.memory (links+(BitVec.ofNat 32 (Collision.pathCellIndex
      (path thing angle ox oy).startBlockX (path thing angle ox oy).startBlockY w) <<< 2))=object) :
    let called := E1M1ThingGate.called gun s weapon actor thing angle ox oy xout yout base lines words c w h data input
    OriginalThingEntry.head (OriginalThingEntry.guarded (OriginalThingEntry.entry called.core)).core=object := by
  have enc := bounds_inputs gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns links safe
  apply OriginalThingEntry.live_head _ _ _ w h enc input.inside links object
  · exact (call_read gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns _ (safe _ (by simp [reads]))).trans global
  · exact (call_read gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns _ (safe _ (by simp [reads]))).trans selected
  · rw [call_stack gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns]
    simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using (safe _ (by simp [reads])).entry
  · rw [call_stack gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns]
    simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using (safe _ (by simp [reads])).entry

include flag in
theorem firing_lookup (links object : Word)
    (safe : ∀ a∈reads thing angle ox oy w links, ReadSafe gun s lines a)
    (global : load32 s.memory (0x2c0f8#32)=links)
    (selected : load32 s.memory (links+(BitVec.ofNat 32 (Collision.pathCellIndex
      (path thing angle ox oy).startBlockX (path thing angle ox oy).startBlockY w) <<< 2))=object)
    (f : Option Flags) :
    let out := result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input
    (∃ steps≤403+281*c.ids.length, X86CodeMemory.Prefix FloorCaller.cm program [] steps
      ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ out) ∧
    out.pc=(if object=(0#32) then 0x2cab1 else 0x2c5d2) ∧
    out.core.regs 4=(if object=(0#32) then s.regs 4-(112#32) else s.regs 4-(120#32)) ∧
    (object=(0#32) → out.core.regs 0=(1#32)) ∧
    (object≠(0#32) → out.core.regs 2=object ∧ load32 out.core.memory (out.core.regs 4)=(0x2c720#32)) ∧
    OriginalLineCollection.Tracks out.core 0x2ba20 (E1M1PathMap.resolve lines)
      (E1M1ScanReturn.finished gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).2.collected 0 := by
  let called := E1M1ThingGate.called gun s weapon actor thing angle ox oy xout yout base lines words c w h data input
  have enc := bounds_inputs gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns links safe
  have inside := (OriginalThingEntry.live_bounds _ _ _ w h enc).mpr input.inside
  have head := first_head gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns links object safe global selected
  have start := E1M1ThingCoordinates.firing_call gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag f
  obtain ⟨execution,tracked⟩ := firing_execution gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag f
  have sp := call_stack gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns
  refine ⟨execution,?_,?_,?_,?_,tracked⟩
  · by_cases empty : object=(0#32)
    · have obs := OriginalThingEntry.empty_return called.core inside (head.trans empty)
      rw [if_pos empty]
      exact obs.2.2.trans (congrArg BitVec.toNat start.2.2.2.2.2.2.1)
    · exact (OriginalThingEntry.nonempty called.core inside (by rw [head]; exact empty)).1.trans (by simp [empty])
  · by_cases empty : object=(0#32)
    · have obs := OriginalThingEntry.empty_return called.core inside (head.trans empty)
      rw [if_pos empty]
      exact obs.2.1.trans (by rw [sp]; simp [BitVec.sub_eq_add_neg,BitVec.add_assoc])
    · have obs := OriginalThingEntry.nonempty called.core inside (by rw [head]; exact empty)
      rw [if_neg empty]
      exact obs.2.2.1.trans (by rw [sp]; simp [BitVec.sub_eq_add_neg,BitVec.add_assoc])
  · intro empty
    exact (OriginalThingEntry.empty_return called.core inside (head.trans empty)).1
  · intro present
    have obs := OriginalThingEntry.nonempty called.core inside (by rw [head]; exact present)
    exact ⟨obs.2.1.trans head,obs.2.2.2.trans start.2.2.2.2.2.1⟩
end Firing
end Doom.Proofs.E1M1ThingEntry
