import Doom.Proofs.E1M1ThingFirstSide
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1ThingGeometry
open Verification X86 X86Memory X86Control BlockSummary
open E1M1ScanMemory (firstScan)
open E1M1ScanGeometry (path)
open E1M1ScanContracts (LineData)
open OriginalLineMixedInvariant (Initial ArraySafe)

structure ScanSafe (sp lines a : Word) : Prop where
  scan : E1M1ScanContracts.Protected sp lines a
  array : ArraySafe 0x2ba20 a

structure EntrySafe (sp a : Word) : Prop where
  call : Apart a (sp-(116#32))
  entry : Apart a (sp-(120#32))
  callback : ∀ off∈[(4#32),8,12,16,20,24,28], Apart a (sp-(120#32)-off)

def SideSafe (sp a : Word) : Prop :=
  Apart a (sp+(20#32)) ∧ ∀ off∈[(4#32),8,12,16,20], Apart a (sp-off)
def traceReads : List Word := [0x2ba10,0x2ba14,0x2ba18,0x2ba1c]
def objectReads (object : Word) : List Word := [object+12,object+16,object+64]

/-- Values and separation at firing entry; the initialized trace is derived,
not assumed to equal pre-initialization globals. -/
structure Data (gun : Fire.Gun) (s : X86Memory.State) (lines object : Word)
    (target : Collision.SolidThing) : Prop where
  objectX : load32 s.memory (object+(12#32))=target.x.raw.toBitVec
  objectY : load32 s.memory (object+(16#32))=target.y.raw.toBitVec
  radius : load32 s.memory (object+(64#32))=target.radius.raw.toBitVec
  objectSafe : ∀ a∈objectReads object, E1M1ThingEntry.ReadSafe gun s lines a
  objectCallback : ∀ a∈objectReads object, ∀ off∈[(4#32),8,12,16,20,24,28], Apart a (s.regs 4-(120#32)-off)
  traceSetup : ∀ a∈traceReads, E1M1PathMapSetup.StackSafe (s.regs 4-(112#32)) a
  traceScan : ∀ a∈traceReads, ScanSafe (s.regs 4) lines a
  traceEntry : ∀ a∈traceReads, EntrySafe (s.regs 4) a
  traceSide : ∀ a∈traceReads, SideSafe (s.regs 4-(172#32)) a

section Firing
variable (gun : Fire.Gun) (s : X86Memory.State) (weapon : Weapon.Context)
    (actor : Word) (thing : Collision.SolidThing) (angle : Angle) (ox oy : Fixed)
    (xout yout : Int32 × Fixed × Fixed) (base lines : Word) (words : Array Nat)
    (c : E1M1PathMap.Cell) (w h : Nat) (data : Nat → LineData)
    (input : E1M1FiringScan.Inputs gun s weapon actor thing angle ox oy xout yout base lines words c w h data)
include input

def extended (a : Word) (safe : ScanSafe (s.regs 4) lines a) :
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
theorem scan_read (a : Word) (safe : ScanSafe (s.regs 4) lines a) :
    load32 (E1M1ScanReturn.finished gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).1.core.memory a=
      load32 (firstScan gun s).core.memory a := by
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
  exact ret.2.2.2 a (List.mem_append_right _ (by simp))

variable (returns : E1M1ScanReturn.ReturnSafe (s.regs 4) lines)
    (flag : E1M1ThingGate.FlagSafe (s.regs 4) lines)
    (links object : Word)
    (lookupSafe : ∀ a∈E1M1ThingEntry.reads thing angle ox oy w links, E1M1ThingEntry.ReadSafe gun s lines a)
    (global : load32 s.memory (0x2c0f8#32)=links)
    (selected : load32 s.memory (links+(BitVec.ofNat 32 (Collision.pathCellIndex
      (path thing angle ox oy).startBlockX (path thing angle ox oy).startBlockY w) <<< 2))=object)
    (present : object≠(0#32))
    (stack : E1M1ThingCallback.StackSafe (s.regs 4-(120#32)) 0x2ba20)
include returns flag lookupSafe global selected present stack

/-- The object iterator and callback entry preserve a protected word. -/
theorem entry_frame (a : Word) (safe : EntrySafe (s.regs 4) a) :
    load32 (E1M1ThingCallback.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).core.memory a=
      load32 (E1M1ThingGate.called gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).core.memory a := by
  have start := E1M1ThingEntry.firing_lookup gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links object lookupSafe global selected none
  have sp : (E1M1ThingEntry.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).core.regs 4=s.regs 4-(120#32) := by
    simpa only [if_neg present] using start.2.2.1
  apply (OriginalThingCallback.enter_frame _ _ a ?_).trans (OriginalThingEntry.frame _ a ?_)
  · change ∀ off∈[(4#32),8,12,16,20,24,28], Apart a ((E1M1ThingEntry.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).core.regs 4-off)
    rw [sp]
    exact safe.callback
  · rw [E1M1ThingEntry.call_stack gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns]
    simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe.entry

theorem object_read (a : Word) (safe : E1M1ThingEntry.ReadSafe gun s lines a)
    (callback : ∀ off∈[(4#32),8,12,16,20,24,28], Apart a (s.regs 4-(120#32)-off)) :
    load32 (E1M1ThingCallback.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).core.memory a=load32 s.memory a := by
  exact (entry_frame gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links object lookupSafe global selected present stack a
    ⟨safe.call,safe.entry,callback⟩).trans
    (E1M1ThingEntry.call_read gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns a safe)

theorem trace_read (a : Word) (scan : ScanSafe (s.regs 4) lines a) (entry : EntrySafe (s.regs 4) a) :
    load32 (E1M1ThingCallback.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).core.memory a=load32 (firstScan gun s).core.memory a := by
  apply (entry_frame gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links object lookupSafe global selected present stack a entry).trans
  have sp := (E1M1ScanReturn.parent_return gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns).2.1
  apply (OriginalPathCell.call_frame false _ _ a ?_).trans (scan_read gun s weapon actor thing angle ox oy xout yout base lines words c w h data input a scan)
  change Apart a ((E1M1ScanReturn.finished gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).1.core.regs 4-(4#32))
  rw [sp]
  simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using entry.call

theorem callback_inputs (target : Collision.SolidThing) (d : Data gun s lines object target) :
    OriginalThingFirstSide.Inputs (E1M1ThingCallback.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).core
      (path thing angle ox oy).trace target object := by
  have entered := E1M1ThingCallback.firing_enter gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links object lookupSafe global selected present stack none
  have trace := E1M1ScanMemory.firing_trace gun s actor thing angle ox oy input.geometry d.traceSetup
  have keep (a : Word) (ha : a∈traceReads) := trace_read gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links object lookupSafe global selected present stack a
    (d.traceScan a ha) (d.traceEntry a ha)
  have tx := congrArg (fun v => v.1) trace
  have ty := congrArg (fun v => v.2.1) trace
  have dx := congrArg (fun v => v.2.2.1) trace
  have dy := congrArg (fun v => v.2.2.2) trace
  refine ⟨⟨entered.2.2.1,?_,?_,?_,?_,?_⟩,?_,?_,?_⟩
  · exact (keep _ (by simp [traceReads])).trans dx
  · exact (keep _ (by simp [traceReads])).trans dy
  · exact (object_read gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links object lookupSafe global selected present stack _
      (d.objectSafe _ (by simp [objectReads])) (d.objectCallback _ (by simp [objectReads]))).trans d.objectX
  · exact (object_read gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links object lookupSafe global selected present stack _
      (d.objectSafe _ (by simp [objectReads])) (d.objectCallback _ (by simp [objectReads]))).trans d.objectY
  · exact (object_read gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links object lookupSafe global selected present stack _
      (d.objectSafe _ (by simp [objectReads])) (d.objectCallback _ (by simp [objectReads]))).trans d.radius
  · exact (keep _ (by simp [traceReads])).trans tx
  · exact (keep _ (by simp [traceReads])).trans ty
  · intro a ha
    change SideSafe ((E1M1ThingCallback.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).core.regs 4) a
    rw [entered.2.2.2.2.1]
    exact d.traceSide a ha

theorem firing_live (target : Collision.SolidThing) (d : Data gun s lines object target)
    (sideStack : E1M1ThingFirstSide.StackSafe (s.regs 4-(172#32)) 0x2ba20) (f : Option Flags) :
    let out := E1M1ThingFirstSide.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input
    (∃ steps≤480+281*c.ids.length, X86CodeMemory.Prefix FloorCaller.cm E1M1ThingFirstSide.program [] steps
      ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ out) ∧
    out.core.regs 0=OriginalDivlineSide.bit ((path thing angle ox oy).trace.pointSide
      (OriginalThingDiagonal.points (path thing angle ox oy).trace target).1
      (OriginalThingDiagonal.points (path thing angle ox oy).trace target).2.1) ∧
    out.pc=0x2c78d ∧
    OriginalLineCollection.Tracks out.core 0x2ba20 (E1M1PathMap.resolve lines)
      (E1M1ScanReturn.finished gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).2.collected 0 := by
  have run := E1M1ThingFirstSide.firing_first_side gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links object lookupSafe global selected present stack sideStack f
  have live := OriginalThingFirstSide.live _ (path thing angle ox oy).trace target object
    (callback_inputs gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links object lookupSafe global selected present stack target d)
  exact ⟨run.1,live.1,run.2.1,run.2.2.2.2⟩
end Firing
end Doom.Proofs.E1M1ThingGeometry
