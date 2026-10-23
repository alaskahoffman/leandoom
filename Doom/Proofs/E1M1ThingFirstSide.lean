import Doom.Proofs.E1M1ThingCallback
import Doom.Proofs.OriginalThingFirstSide
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1ThingFirstSide
open Verification X86 X86Memory X86Control BlockSummary
open E1M1ScanGeometry (path)
open E1M1ScanContracts (LineData)
open OriginalLineMixedInvariant (ArraySafe)

def program : X86Routine.Program := fun pc =>
  match E1M1ThingCallback.program pc with
  | some op => some op
  | none => OriginalThingDiagonal.program pc

theorem contains_prior (pc : Nat) (h : E1M1ThingCallback.program pc≠none) :
    program pc=E1M1ThingCallback.program pc := by
  unfold program
  cases eq : E1M1ThingCallback.program pc <;> simp_all

theorem contains_first_side (pc : Nat) (h : OriginalThingFirstSide.program pc≠none) :
    program pc=OriginalThingFirstSide.program pc := by
  have range : (0x2c72b≤pc ∧ pc<0x2c78d) ∨ (0x2c1e0≤pc ∧ pc<0x2c2a7) := by
    by_cases a : 0x2c72b≤pc ∧ pc<0x2c78d
    · exact Or.inl a
    by_cases b : 0x2c1e0≤pc ∧ pc<0x2c2a7
    · exact Or.inr b
    simp [OriginalThingFirstSide.program,OriginalThingDiagonal.program,OriginalThingDiagonal.bytesProgram,
      OriginalDivlineSide.program,OriginalDivlineSide.bytesProgram,a,b] at h
  rcases range with a|b
  · have all : ∀ i : Fin 98, program (0x2c72b+i.val)=OriginalThingFirstSide.program (0x2c72b+i.val) := by decide
    have eq : 0x2c72b+(pc-0x2c72b)=pc := by omega
    simpa only [eq] using all ⟨pc-0x2c72b,by omega⟩
  · have all : ∀ i : Fin 199, program (0x2c1e0+i.val)=OriginalThingFirstSide.program (0x2c1e0+i.val) := by decide
    have eq : 0x2c1e0+(pc-0x2c1e0)=pc := by omega
    simpa only [eq] using all ⟨pc-0x2c1e0,by omega⟩

def StackSafe (sp base : Word) : Prop :=
  ArraySafe base (sp+(20#32)) ∧ ∀ off∈[(4#32),8,12,16,20], ArraySafe base (sp-off)

theorem collection (s : X86Memory.State) (base : Word)
    (resolve : Collision.Intercept → Word) (hits : Array Collision.Intercept) (reserve : Nat)
    (tracked : OriginalLineCollection.Tracks s base resolve hits reserve)
    (safe : StackSafe (s.regs 4) base) :
    OriginalLineCollection.Tracks (OriginalThingFirstSide.result s).core base resolve hits reserve := by
  have record (i : Nat) (hi : i<hits.size) (off : Word) (ho : off∈[(0#32),4,8]) :
      OriginalThingFirstSide.Safe s (OriginalLineCollection.slot base i off) := by
    have room : i<128 := by have room:=tracked.room; omega
    exact ⟨FloorCaller.apart_symm (safe.1.1 i room off ho),
      fun delta hd => FloorCaller.apart_symm ((safe.2 delta hd).1 i room off ho)⟩
  refine ⟨?_,?_,tracked.room⟩
  · intro i hi
    have old := tracked.encoded i hi
    unfold OriginalLineFinish.RecordAt at old ⊢
    refine ⟨?_,?_,?_⟩
    · exact (OriginalThingFirstSide.frame s _ (by
        simpa only [OriginalLineCollection.slot,BitVec.add_zero] using record i hi (0#32) (by simp))).trans old.1
    · exact (OriginalThingFirstSide.frame s _ (record i hi (4#32) (by simp))).trans old.2.1
    · exact (OriginalThingFirstSide.frame s _ (record i hi (8#32) (by simp))).trans old.2.2
  · exact (OriginalThingFirstSide.frame s _ ⟨FloorCaller.apart_symm safe.1.2,
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

def result := OriginalThingFirstSide.result (E1M1ThingCallback.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).core

variable (returns : E1M1ScanReturn.ReturnSafe (s.regs 4) lines)
    (flag : E1M1ThingGate.FlagSafe (s.regs 4) lines)
include returns flag

/-- Continuous execution and collection preservation. The live geometry theorem
is separate until object/trace representation is transported from firing entry. -/
theorem firing_first_side (links object : Word)
    (safe : ∀ a∈E1M1ThingEntry.reads thing angle ox oy w links, E1M1ThingEntry.ReadSafe gun s lines a)
    (global : load32 s.memory (0x2c0f8#32)=links)
    (selected : load32 s.memory (links+(BitVec.ofNat 32 (Collision.pathCellIndex
      (path thing angle ox oy).startBlockX (path thing angle ox oy).startBlockY w) <<< 2))=object)
    (present : object≠(0#32))
    (stack : E1M1ThingCallback.StackSafe (s.regs 4-(120#32)) 0x2ba20)
    (sideStack : StackSafe (s.regs 4-(172#32)) 0x2ba20)
    (f : Option Flags) :
    let out := result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input
    (∃ steps≤480+281*c.ids.length, X86CodeMemory.Prefix FloorCaller.cm program [] steps
      ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ out) ∧
    out.pc=0x2c78d ∧ out.core.regs 4=s.regs 4-(172#32) ∧ out.core.regs 1=object ∧
    OriginalLineCollection.Tracks out.core 0x2ba20 (E1M1PathMap.resolve lines)
      (E1M1ScanReturn.finished gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).2.collected 0 := by
  let entry := E1M1ThingCallback.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input
  obtain ⟨⟨n,hn,prior⟩,pc,obj,_,sp,_,_,tracked⟩ :=
    E1M1ThingCallback.firing_enter gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links object safe global selected present stack f
  obtain ⟨m,hm,tail⟩ := OriginalThingFirstSide.execution entry.core entry.flags
  rw [OriginalPathXStep.at_pc _ _ pc] at tail
  have ret := OriginalThingFirstSide.returned entry.core
  refine ⟨⟨n+m,by omega,E1M1PspriteStep.prefix_trans (prior.transfer program [] contains_prior (by simp))
    (X86CodeMemory.lift_success (tail.transfer program [] contains_first_side (by simp)) FloorCaller.cm)⟩,
    ret.1,ret.2.1.trans sp,ret.2.2.trans obj,?_⟩
  exact collection entry.core 0x2ba20 (E1M1PathMap.resolve lines) _ 0 tracked (by rw [sp]; exact sideStack)
end Firing
end Doom.Proofs.E1M1ThingFirstSide
