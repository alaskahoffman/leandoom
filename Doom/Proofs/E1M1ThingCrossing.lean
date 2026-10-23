import Doom.Proofs.E1M1ThingGeometry
import Doom.Proofs.OriginalThingSecondSide
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1ThingCrossing
open Verification X86 X86Memory X86Control BlockSummary
open E1M1ScanGeometry (path)
open E1M1ScanContracts (LineData)
open OriginalLineMixedInvariant (ArraySafe)

def program : X86Routine.Program := fun pc =>
  match E1M1ThingFirstSide.program pc with
  | some op => some op
  | none => OriginalThingSecondSide.localProgram pc

theorem contains_prior (pc : Nat) (h : E1M1ThingFirstSide.program pc≠none) :
    program pc=E1M1ThingFirstSide.program pc := by
  unfold program
  cases eq : E1M1ThingFirstSide.program pc <;> simp_all

theorem contains_local (pc : Nat) (h : OriginalThingSecondSide.localProgram pc≠none) :
    program pc=OriginalThingSecondSide.localProgram pc := by
  have range : 0x2c78d≤pc ∧ pc<0x2c7ae := by
    by_cases r : 0x2c78d≤pc ∧ pc<0x2c7ae
    · exact r
    · simp [OriginalThingSecondSide.localProgram,OriginalThingSecondSide.bytesProgram,r] at h
  have all : ∀ i : Fin 33, program (0x2c78d+i.val)=OriginalThingSecondSide.localProgram (0x2c78d+i.val) := by decide
  have eq : 0x2c78d+(pc-0x2c78d)=pc := by omega
  simpa only [eq] using all ⟨pc-0x2c78d,by omega⟩

theorem contains_second (pc : Nat) (h : OriginalThingSecondSide.program pc≠none) :
    program pc=OriginalThingSecondSide.program pc := by
  cases old : OriginalThingFirstSide.program pc with
  | none =>
    have fresh : OriginalThingSecondSide.localProgram pc≠none := by simpa [OriginalThingSecondSide.program,old] using h
    simpa [OriginalThingSecondSide.program,old] using contains_local pc fresh
  | some op =>
    have first := E1M1ThingFirstSide.contains_first_side pc (by simp [old])
    have keep := contains_prior pc (by rw [first,old]; simp)
    simpa [OriginalThingSecondSide.program,old] using keep.trans first

def StackSafe (sp base : Word) : Prop :=
  ArraySafe base (sp+(16#32)) ∧ ∀ off∈[(4#32),8,12,16,20], ArraySafe base (sp-off)

theorem collection (s : X86Memory.State) (base : Word)
    (resolve : Collision.Intercept → Word) (hits : Array Collision.Intercept) (reserve : Nat)
    (tracked : OriginalLineCollection.Tracks s base resolve hits reserve)
    (safe : StackSafe (s.regs 4) base) :
    OriginalLineCollection.Tracks (OriginalThingSecondSide.result s).core base resolve hits reserve := by
  have record (i : Nat) (hi : i<hits.size) (off : Word) (ho : off∈[(0#32),4,8]) :
      OriginalThingSecondSide.Safe (s.regs 4) (OriginalLineCollection.slot base i off) := by
    have room : i<128 := by have room:=tracked.room; omega
    exact ⟨FloorCaller.apart_symm (safe.1.1 i room off ho),
      fun delta hd => FloorCaller.apart_symm ((safe.2 delta hd).1 i room off ho)⟩
  refine ⟨?_,?_,tracked.room⟩
  · intro i hi
    have old := tracked.encoded i hi
    unfold OriginalLineFinish.RecordAt at old ⊢
    refine ⟨?_,?_,?_⟩
    · exact (OriginalThingSecondSide.frame s _ (by
        simpa only [OriginalLineCollection.slot,BitVec.add_zero] using record i hi (0#32) (by simp))).trans old.1
    · exact (OriginalThingSecondSide.frame s _ (record i hi (4#32) (by simp))).trans old.2.1
    · exact (OriginalThingSecondSide.frame s _ (record i hi (8#32) (by simp))).trans old.2.2
  · exact (OriginalThingSecondSide.frame s _ ⟨FloorCaller.apart_symm safe.1.2,
      fun delta hd => FloorCaller.apart_symm (safe.2 delta hd).2⟩).trans tracked.cursor

set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] Collision.SolidThing.attackEndpoint
section Firing
variable (gun : Fire.Gun) (s : X86Memory.State) (weapon : Weapon.Context)
    (actor : Word) (thing : Collision.SolidThing) (angle : Angle) (ox oy : Fixed)
    (xout yout : Int32 × Fixed × Fixed) (base lines : Word) (words : Array Nat)
    (c : E1M1PathMap.Cell) (w h : Nat) (data : Nat → LineData)
    (input : E1M1FiringScan.Inputs gun s weapon actor thing angle ox oy xout yout base lines words c w h data)
include input

def result := OriginalThingSecondSide.result (E1M1ThingFirstSide.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).core

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


/-- Both side results and the original skip/crossing PC follow from firing-entry
encodings. Reached registers/trace globals are not extra input hypotheses. -/
theorem firing_crossing (target : Collision.SolidThing) (d : E1M1ThingGeometry.Data gun s lines object target)
    (sideStack : E1M1ThingFirstSide.StackSafe (s.regs 4-(172#32)) 0x2ba20)
    (secondStack : StackSafe (s.regs 4-(172#32)) 0x2ba20)
    (traceScratch : ∀ a∈E1M1ThingGeometry.traceReads, Apart a (s.regs 4-(172#32)+(16#32)))
    (f : Option Flags) :
    let out := result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input
    let trace := (path thing angle ox oy).trace
    (∃ steps≤533+281*c.ids.length, X86CodeMemory.Prefix FloorCaller.cm program [] steps
      ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ out) ∧
    out.pc=(if OriginalThingSecondSide.firstSide trace target=OriginalThingSecondSide.lastSide trace target
      then 0x2c805 else 0x2c7ae) ∧
    (OriginalThingSecondSide.firstSide trace target=OriginalThingSecondSide.lastSide trace target →
      out.core.regs 0=(1#32) ∧ Collision.thingIntercept trace target=.ok none) ∧
    OriginalLineCollection.Tracks out.core 0x2ba20 (E1M1PathMap.resolve lines)
      (E1M1ScanReturn.finished gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).2.collected 0 := by
  let entry := E1M1ThingCallback.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input
  let first := E1M1ThingFirstSide.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input
  have started := E1M1ThingCallback.firing_enter gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links object lookupSafe global selected present stack f
  obtain ⟨⟨n,hn,prior⟩,pc,sp,obj,tracked⟩ :=
    E1M1ThingFirstSide.firing_first_side gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links object lookupSafe global selected present stack sideStack f
  obtain ⟨m,hm,tail⟩ := OriginalThingSecondSide.execution first.core first.flags
  rw [OriginalPathXStep.at_pc _ _ pc] at tail
  have geometry := E1M1ThingGeometry.callback_inputs gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links object lookupSafe global selected present stack target d
  have live := OriginalThingSecondSide.live entry.core (path thing angle ox oy).trace target object geometry (by
    rw [started.2.2.2.2.1]
    exact traceScratch)
  refine ⟨⟨n+m,by omega,E1M1PspriteStep.prefix_trans (prior.transfer program [] contains_prior (by simp))
    (X86CodeMemory.lift_success (tail.transfer program [] contains_second (by simp)) FloorCaller.cm)⟩,
    live.1,live.2,?_⟩
  exact collection first.core 0x2ba20 (E1M1PathMap.resolve lines) _ 0 tracked (by rw [sp]; exact secondStack)
end Firing
end Doom.Proofs.E1M1ThingCrossing
