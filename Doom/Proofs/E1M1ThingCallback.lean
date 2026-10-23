import Doom.Proofs.E1M1ThingEntry
import Doom.Proofs.OriginalThingCallback
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1ThingCallback
open Verification X86 X86Memory X86Control BlockSummary
open E1M1ScanGeometry (path)
open E1M1ScanContracts (LineData)
open OriginalLineMixedInvariant (ArraySafe)

def program : X86Routine.Program := fun pc =>
  match E1M1ThingEntry.program pc with
  | some op => some op
  | none => OriginalThingCallback.program pc

theorem contains_prior (pc : Nat) (h : E1M1ThingEntry.program pc≠none) :
    program pc=E1M1ThingEntry.program pc := by
  unfold program
  cases eq : E1M1ThingEntry.program pc <;> simp_all

theorem contains_callback (pc : Nat) (h : OriginalThingCallback.program pc≠none) :
    program pc=OriginalThingCallback.program pc := by
  have inside : (0x2c5d2≤pc ∧ pc<0x2c5e2) ∨ (0x2c720≤pc ∧ pc<0x2c72b) := by
    by_cases a : 0x2c5d2≤pc ∧ pc<0x2c5e2
    · exact Or.inl a
    by_cases b : 0x2c720≤pc ∧ pc<0x2c72b
    · exact Or.inr b
    simp [OriginalThingCallback.program,OriginalThingCallback.bytesProgram,a,b] at h
  have absent : E1M1ThingEntry.program pc=none := by
    rcases inside with a|b
    · have all : ∀ i : Fin 16, E1M1ThingEntry.program (0x2c5d2+i.val)=none := by decide
      have eq : 0x2c5d2+(pc-0x2c5d2)=pc := by omega
      simpa only [eq] using all ⟨pc-0x2c5d2,by omega⟩
    · have all : ∀ i : Fin 11, E1M1ThingEntry.program (0x2c720+i.val)=none := by decide
      have eq : 0x2c720+(pc-0x2c720)=pc := by omega
      simpa only [eq] using all ⟨pc-0x2c720,by omega⟩
  simp [program,absent]

/-- Every CALL/prologue store is separated from the intercept array and cursor. -/
def StackSafe (sp base : Word) : Prop :=
  ∀ off∈[(4#32),8,12,16,20,24,28], ArraySafe base (sp-off)

theorem collection (s : X86Memory.State) (f : Option Flags) (base : Word)
    (resolve : Collision.Intercept → Word) (hits : Array Collision.Intercept) (reserve : Nat)
    (tracked : OriginalLineCollection.Tracks s base resolve hits reserve)
    (safe : StackSafe (s.regs 4) base) :
    OriginalLineCollection.Tracks (OriginalThingCallback.entered s f).core base resolve hits reserve := by
  have record (i : Nat) (hi : i<hits.size) (off : Word) (ho : off∈[(0#32),4,8]) :
      ∀ delta∈[(4#32),8,12,16,20,24,28],
        Apart (OriginalLineCollection.slot base i off) (s.regs 4-delta) := by
    intro delta hd
    exact FloorCaller.apart_symm ((safe delta hd).1 i (by have room:=tracked.room; omega) off ho)
  refine ⟨?_,?_,tracked.room⟩
  · intro i hi
    have old := tracked.encoded i hi
    unfold OriginalLineFinish.RecordAt at old ⊢
    refine ⟨?_,?_,?_⟩
    · exact (OriginalThingCallback.enter_frame s f _ (by
        simpa only [OriginalLineCollection.slot,BitVec.add_zero] using record i hi (0#32) (by simp))).trans old.1
    · exact (OriginalThingCallback.enter_frame s f _ (record i hi (4#32) (by simp))).trans old.2.1
    · exact (OriginalThingCallback.enter_frame s f _ (record i hi (8#32) (by simp))).trans old.2.2
  · exact (OriginalThingCallback.enter_frame s f _ (fun delta hd => FloorCaller.apart_symm (safe delta hd).2)).trans tracked.cursor

set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] Collision.SolidThing.attackEndpoint
section Firing
variable (gun : Fire.Gun) (s : X86Memory.State) (weapon : Weapon.Context)
    (actor : Word) (thing : Collision.SolidThing) (angle : Angle) (ox oy : Fixed)
    (xout yout : Int32 × Fixed × Fixed) (base lines : Word) (words : Array Nat)
    (c : E1M1PathMap.Cell) (w h : Nat) (data : Nat → LineData)
    (input : E1M1FiringScan.Inputs gun s weapon actor thing angle ox oy xout yout base lines words c w h data)
include input

def result : X86Control.State :=
  let out := E1M1ThingEntry.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input
  OriginalThingCallback.entered out.core out.flags

variable (returns : E1M1ScanReturn.ReturnSafe (s.regs 4) lines)
    (flag : E1M1ThingGate.FlagSafe (s.regs 4) lines)
include returns flag

/-- A continuous prefix reaches the actual object-intersection body. The body
itself is the next obligation, as are reachability of the initial contracts. -/
theorem firing_enter (links object : Word)
    (safe : ∀ a∈E1M1ThingEntry.reads thing angle ox oy w links, E1M1ThingEntry.ReadSafe gun s lines a)
    (global : load32 s.memory (0x2c0f8#32)=links)
    (selected : load32 s.memory (links+(BitVec.ofNat 32 (Collision.pathCellIndex
      (path thing angle ox oy).startBlockX (path thing angle ox oy).startBlockY w) <<< 2))=object)
    (present : object≠(0#32))
    (stack : StackSafe (s.regs 4-(120#32)) 0x2ba20)
    (f : Option Flags) :
    let out := result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input
    (∃ steps≤413+281*c.ids.length, X86CodeMemory.Prefix FloorCaller.cm program [] steps
      ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ out) ∧
    out.pc=0x2c72b ∧ out.core.regs 1=object ∧ out.core.regs 2=object ∧
    out.core.regs 4=s.regs 4-(172#32) ∧
    load32 out.core.memory (s.regs 4-(136#32))=object ∧
    load32 out.core.memory (s.regs 4-(124#32))=(0x2c5d7#32) ∧
    OriginalLineCollection.Tracks out.core 0x2ba20 (E1M1PathMap.resolve lines)
      (E1M1ScanReturn.finished gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).2.collected 0 := by
  let entry := E1M1ThingEntry.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input
  obtain ⟨⟨n,hn,prior⟩,pc,sp,_,dispatch,tracked⟩ :=
    E1M1ThingEntry.firing_lookup gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links object safe global selected f
  simp only [if_neg present] at pc sp
  obtain ⟨objectArg,target⟩ := dispatch present
  have tail := OriginalThingCallback.enter_execution entry.core entry.flags target
  rw [OriginalPathXStep.at_pc _ _ pc] at tail
  have observations := OriginalThingCallback.enter_observe entry.core entry.flags
  have collection := collection entry.core entry.flags 0x2ba20 (E1M1PathMap.resolve lines) _ 0 tracked (by rw [sp]; exact stack)
  refine ⟨⟨n+10,by omega,E1M1PspriteStep.prefix_trans
    (prior.transfer program [] contains_prior (by simp))
    (X86CodeMemory.lift_success (tail.transfer program [] contains_callback (by simp)) FloorCaller.cm)⟩,
    rfl,observations.1.trans objectArg,observations.2.1.trans objectArg,?_,?_,?_,collection⟩
  · apply observations.2.2.1.trans
    rw [sp]
    simp only [BitVec.sub_sub]
    rfl
  · have addr : entry.core.regs 4-(16#32)=s.regs 4-(136#32) := by
      rw [sp]
      simp only [BitVec.sub_sub]
      rfl
    have saved := observations.2.2.2.1
    rw [addr] at saved
    exact saved.trans objectArg
  · have addr : entry.core.regs 4-(4#32)=s.regs 4-(124#32) := by
      rw [sp]
      simp only [BitVec.sub_sub]
      rfl
    have saved := observations.2.2.2.2
    rw [addr] at saved
    exact saved
end Firing
end Doom.Proofs.E1M1ThingCallback
