import Doom.Proofs.E1M1NextCoordinates
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1NextThingLookup
open Verification X86 X86Memory X86Control BlockSummary
open OriginalLineVisits (Represents stamp)
attribute [local irreducible] load32

/-- Reuse the authenticated iterator bytes within the continuous firing program. -/
theorem contains_entry (pc : Nat) (h : OriginalThingEntry.program pc≠none) :
    E1M1FiringAdvance.program pc=OriginalThingEntry.program pc := by
  have a := E1M1ThingEntry.contains_thing pc h
  have b := E1M1FiringThings.contains_entry pc (by rw [a]; exact h)
  exact (E1M1FiringAdvance.contains_prior pc (by
    change E1M1FiringThings.program pc≠none
    rw [b,a]; exact h)).trans (b.trans a)

/-- Bounds and table lookup either select the actual first object or return
success for an empty cell. Both branches retain mixed hits and visit history. -/
theorem execution (s : X86Control.State) (sp lines epoch : Word) (objects : Nat → Word)
    (hits : Array Collision.Intercept) (seen : Array Bool)
    (x y : Int32) (w h : Nat) (links object : Word)
    (pc : s.pc=0x2c5a0) (stack : s.core.regs 4=sp-(116#32))
    (callback : s.core.regs 3=(0x2c720#32))
    (returnWord : load32 s.core.memory (s.core.regs 4)=(0x2cab1#32))
    (encoding : OriginalThingEntry.Inputs s.core x y w h)
    (inMap : Collision.pathCellInside x y w h=true)
    (global : load32 s.core.memory (0x2c0f8#32)=links)
    (selected : load32 s.core.memory (links+(BitVec.ofNat 32 (Collision.pathCellIndex x y w) <<< 2))=object)
    (globalSafe : Apart (0x2c0f8#32) (sp-(120#32)))
    (headSafe : Apart (links+(BitVec.ofNat 32 (Collision.pathCellIndex x y w) <<< 2)) (sp-(120#32)))
    (tracked : OriginalLineCollection.Tracks s.core 0x2ba20 (E1M1ThingFinish.resolve lines objects) hits 0)
    (represented : Represents s.core.memory lines epoch seen)
    (array : OriginalLineMixedInvariant.ArraySafe 0x2ba20 (sp-(120#32)))
    (epochSafe : Apart (0x13580#32) (sp-(120#32)))
    (stampSafe : ∀ j<seen.size, Apart (stamp lines j) (sp-(120#32))) :
    let out := OriginalThingEntry.result s.core
    (∃ n≤20, X86CodeMemory.Prefix FloorCaller.cm E1M1FiringAdvance.program [] n s out) ∧
    OriginalThingEntry.head (OriginalThingEntry.guarded (OriginalThingEntry.entry s.core)).core=object ∧
    (object=0 → out.core.regs 0=(1#32) ∧ out.core.regs 4=sp-(112#32) ∧ out.pc=0x2cab1) ∧
    (object≠0 → out.pc=0x2c5d2 ∧ out.core.regs 2=object ∧ out.core.regs 4=sp-(120#32) ∧
      load32 out.core.memory (out.core.regs 4)=(0x2c720#32)) ∧
    OriginalLineCollection.Tracks out.core 0x2ba20 (E1M1ThingFinish.resolve lines objects) hits 0 ∧
    Represents out.core.memory lines epoch seen := by
  have address : s.core.regs 4-(4#32)=sp-(120#32) := by
    rw [stack]; simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  have inside := (OriginalThingEntry.live_bounds _ x y w h encoding).mpr inMap
  have head := OriginalThingEntry.live_head _ x y w h encoding inMap links object global selected
    (by rw [address]; exact globalSafe) (by rw [address]; exact headSafe)
  obtain ⟨n,hn,path⟩ := OriginalThingEntry.execution s.core s.flags
  rw [OriginalPathXStep.at_pc _ _ pc] at path
  have kept := E1M1ThingEntry.collection s.core 0x2ba20 (E1M1ThingFinish.resolve lines objects) hits 0 tracked
    (by rw [address]; exact array)
  have frame (a : Word) (safe : Apart a (sp-(120#32))) :=
    OriginalThingEntry.frame s.core a (by rw [address]; exact safe)
  refine ⟨⟨n,hn,X86CodeMemory.lift_success (path.transfer _ [] contains_entry (by simp)) FloorCaller.cm⟩,
    head,?_,?_,kept,⟨(frame _ epochSafe).trans represented.1,fun j hj => ?_⟩⟩
  · intro empty
    have ret := OriginalThingEntry.empty_return s.core inside (head.trans empty)
    rw [returnWord,stack] at ret
    simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using ret
  · intro present
    have ret := OriginalThingEntry.nonempty s.core inside (by rw [head]; exact present)
    rw [head,address,callback] at ret
    exact ret
  · rw [frame _ (stampSafe j hj)]; exact represented.2 j hj
end Doom.Proofs.E1M1NextThingLookup
