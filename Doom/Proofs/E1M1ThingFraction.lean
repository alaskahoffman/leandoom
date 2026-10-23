import Doom.Proofs.E1M1ThingCrossing
import Doom.Proofs.OriginalThingFractionInputs
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1ThingFraction
open Verification X86 X86Memory X86Control BlockSummary
open E1M1ScanGeometry (path)
open E1M1ScanContracts (LineData)
open OriginalLineMixedInvariant (ArraySafe)
open OriginalThingSecondSide (firstSide lastSide)

def program : X86Routine.Program := fun pc =>
  match E1M1ThingCrossing.program pc with
  | some op => some op
  | none => OriginalThingFraction.program pc

theorem contains_prior (pc : Nat) (h : E1M1ThingCrossing.program pc≠none) :
    program pc=E1M1ThingCrossing.program pc := by
  unfold program
  cases eq : E1M1ThingCrossing.program pc <;> simp_all

theorem contains_fraction (pc : Nat) (h : OriginalThingFraction.program pc≠none) :
    program pc=OriginalThingFraction.program pc := by
  by_cases r2c7ae : 0x2c7ae≤pc ∧ pc<0x2c7da
  · have all : ∀ i : Fin 44, program (0x2c7ae+i.val)=OriginalThingFraction.program (0x2c7ae+i.val) := by decide
    have eq : 0x2c7ae+(pc-0x2c7ae)=pc := by omega
    simpa only [eq] using all ⟨pc-0x2c7ae,by omega⟩
  by_cases r2c2d0 : 0x2c2d0≤pc ∧ pc<0x2c334
  · have all : ∀ i : Fin 100, program (0x2c2d0+i.val)=OriginalThingFraction.program (0x2c2d0+i.val) := by decide
    have eq : 0x2c2d0+(pc-0x2c2d0)=pc := by omega
    simpa only [eq] using all ⟨pc-0x2c2d0,by omega⟩
  by_cases r1d180 : 0x1d180≤pc ∧ pc<0x1d1c1
  · have all : ∀ i : Fin 65, program (0x1d180+i.val)=OriginalThingFraction.program (0x1d180+i.val) := by decide
    have eq : 0x1d180+(pc-0x1d180)=pc := by omega
    simpa only [eq] using all ⟨pc-0x1d180,by omega⟩
  simp [OriginalThingFraction.program,OriginalThingFraction.bytesProgram,OriginalInterceptVector.program,
    OriginalInterceptVector.bytesProgram,OriginalDivMemory.program,OriginalDivMemory.bytesProgram,r2c7ae,r2c2d0,r1d180] at h

def continueFraction (s : X86Control.State) :=
  if s.pc=0x2c7ae then OriginalThingFraction.result s.core else s

/-- At the two rejection boundaries EAX is 1; at insertion it is the exact fraction.
This does not execute the record writes or the callback epilogue. -/
def Outcome (s : X86Control.State) (trace : Collision.Divline) (target : Collision.SolidThing) : Prop :=
  ∃ hit : Option Fixed, Collision.thingIntercept trace target=.ok hit ∧
    s.pc=(match hit with
      | some _ => 0x2c7e4
      | none => if firstSide trace target=lastSide trace target then 0x2c805 else 0x2c7da) ∧
    s.core.regs 0=(match hit with | some frac => frac.raw.toBitVec | none => (1#32))

theorem continue_live (s : X86Control.State) (trace : Collision.Divline) (target : Collision.SolidThing)
    (pc : s.pc=if firstSide trace target=lastSide trace target then 0x2c805 else 0x2c7ae)
    (skip : firstSide trace target=lastSide trace target → s.core.regs 0=(1#32) ∧ Collision.thingIntercept trace target=.ok none)
    (h : OriginalThingFraction.Inputs s.core trace target)
    (computed : firstSide trace target≠lastSide trace target →
      ∃ frac, Collision.interceptVector trace (OriginalThingFraction.diagonal trace target)=.ok frac) :
    (∃ n≤80, X86Routine.Prefix program [] n s (continueFraction s)) ∧
    Outcome (continueFraction s) trace target := by
  by_cases same : firstSide trace target=lastSide trace target
  · have atSkip : s.pc=0x2c805 := by simpa only [if_pos same] using pc
    have absent : s.pc≠0x2c7ae := by omega
    simp only [continueFraction,if_neg absent]
    exact ⟨⟨0,by omega,.nil _⟩,none,(skip same).2,by simpa only [if_pos same] using atSkip,(skip same).1⟩
  · have atCall : s.pc=0x2c7ae := by simpa only [if_neg same] using pc
    obtain ⟨frac,ok⟩ := computed same
    have safe := OriginalInterceptVector.safe_of_success (OriginalThingFraction.setup s.core) trace
      (OriginalThingFraction.diagonal trace target) 0x2ba10 (s.core.regs 4)
      (OriginalThingFraction.encoded s.core trace target h) (by rw [ok]; rfl)
    obtain ⟨n,hn,run⟩ := OriginalThingFraction.execution s.core s.flags safe
    rw [OriginalPathXStep.at_pc _ _ atCall] at run
    simp only [continueFraction,if_pos atCall]
    refine ⟨⟨n,hn,run.transfer program [] contains_fraction (by simp)⟩,?_⟩
    have branch := OriginalThingFraction.decision_live s.core trace target h frac ok
    have value := OriginalThingFraction.production trace target frac same ok
    refine ⟨if frac.raw<0 then none else some frac,value,?_,?_⟩
    · by_cases neg : frac.raw<0 <;> simpa [neg,same] using branch.1
    · by_cases neg : frac.raw<0 <;> simpa [neg] using branch.2.1

def StackSafe (sp base : Word) : Prop :=
  ∀ off∈[(0#32),4,8,12,-4,-8,-12,-16,-20,-24,-28,-32,-36,-40], ArraySafe base (sp+off)

theorem collection (s : X86Control.State) (base : Word)
    (resolve : Collision.Intercept → Word) (hits : Array Collision.Intercept) (reserve : Nat)
    (tracked : OriginalLineCollection.Tracks s.core base resolve hits reserve)
    (safe : StackSafe (s.core.regs 4) base) :
    OriginalLineCollection.Tracks (continueFraction s).core base resolve hits reserve := by
  unfold continueFraction
  split
  · have record (i : Nat) (hi : i<hits.size) (off : Word) (ho : off∈[(0#32),4,8]) :
        OriginalThingFraction.Safe (s.core.regs 4) (OriginalLineCollection.slot base i off) := by
      have room : i<128 := by have room:=tracked.room; omega
      exact fun delta hd => FloorCaller.apart_symm ((safe delta hd).1 i room off ho)
    refine ⟨?_,?_,tracked.room⟩
    · intro i hi
      have old := tracked.encoded i hi
      unfold OriginalLineFinish.RecordAt at old ⊢
      refine ⟨?_,?_,?_⟩
      · exact (OriginalThingFraction.frame s.core _ (by
          simpa only [OriginalLineCollection.slot,BitVec.add_zero] using record i hi (0#32) (by simp))).trans old.1
      · exact (OriginalThingFraction.frame s.core _ (record i hi (4#32) (by simp))).trans old.2.1
      · exact (OriginalThingFraction.frame s.core _ (record i hi (8#32) (by simp))).trans old.2.2
    · exact (OriginalThingFraction.frame s.core _ (fun delta hd => FloorCaller.apart_symm (safe delta hd).2)).trans tracked.cursor
  · exact tracked

set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] Collision.SolidThing.attackEndpoint
section Firing
variable (gun : Fire.Gun) (s : X86Memory.State) (weapon : Weapon.Context)
    (actor : Word) (thing : Collision.SolidThing) (angle : Angle) (ox oy : Fixed)
    (xout yout : Int32 × Fixed × Fixed) (base lines : Word) (words : Array Nat)
    (c : E1M1PathMap.Cell) (w h : Nat) (data : Nat → LineData)
    (input : E1M1FiringScan.Inputs gun s weapon actor thing angle ox oy xout yout base lines words c w h data)
include input

def result := continueFraction (E1M1ThingCrossing.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input)

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


theorem firing_fraction (target : Collision.SolidThing) (d : E1M1ThingGeometry.Data gun s lines object target)
    (sideStack : E1M1ThingFirstSide.StackSafe (s.regs 4-(172#32)) 0x2ba20)
    (secondStack : E1M1ThingCrossing.StackSafe (s.regs 4-(172#32)) 0x2ba20)
    (traceScratch : ∀ a∈E1M1ThingGeometry.traceReads, Apart a (s.regs 4-(172#32)+(16#32)))
    (fractionStack : StackSafe (s.regs 4-(172#32)) 0x2ba20)
    (traceSafe : ∀ a∈OriginalThingFraction.traceReads, OriginalThingFraction.Safe (s.regs 4-(172#32)) a)
    (computed : firstSide (path thing angle ox oy).trace target≠lastSide (path thing angle ox oy).trace target →
      ∃ frac, Collision.interceptVector (path thing angle ox oy).trace (OriginalThingFraction.diagonal (path thing angle ox oy).trace target)=.ok frac)
    (f : Option Flags) :
    let out := result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input
    (∃ steps≤613+281*c.ids.length, X86CodeMemory.Prefix FloorCaller.cm program [] steps
      ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ out) ∧
    Outcome out (path thing angle ox oy).trace target ∧
    OriginalLineCollection.Tracks out.core 0x2ba20 (E1M1PathMap.resolve lines)
      (E1M1ScanReturn.finished gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).2.collected 0 := by
  let entry := E1M1ThingCallback.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input
  let crossed := E1M1ThingCrossing.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input
  have started := E1M1ThingCallback.firing_enter gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links object lookupSafe global selected present stack f
  have entrySP : entry.core.regs 4=s.regs 4-(172#32) := started.2.2.2.2.1
  have sp : crossed.core.regs 4=s.regs 4-(172#32) := (OriginalThingFractionInputs.crossing_regs entry.core).1.trans entrySP
  obtain ⟨⟨n,hn,prior⟩,pc,skip,tracked⟩ :=
    E1M1ThingCrossing.firing_crossing gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links object lookupSafe global selected present stack target d sideStack secondStack traceScratch f
  have geometry := E1M1ThingGeometry.callback_inputs gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links object lookupSafe global selected present stack target d
  have localInputs := OriginalThingFractionInputs.inputs entry.core (path thing angle ox oy).trace target object geometry
    (by rw [entrySP]; exact traceScratch) (by rw [entrySP]; exact traceSafe)
  obtain ⟨⟨m,hm,tail⟩,value⟩ := continue_live crossed (path thing angle ox oy).trace target pc skip localInputs computed
  exact ⟨⟨n+m,by omega,E1M1PspriteStep.prefix_trans (prior.transfer program [] contains_prior (by simp))
    (X86CodeMemory.lift_success tail FloorCaller.cm)⟩,value,
    collection crossed 0x2ba20 (E1M1PathMap.resolve lines) _ 0 tracked (by rw [sp]; exact fractionStack)⟩
end Firing
end Doom.Proofs.E1M1ThingFraction
