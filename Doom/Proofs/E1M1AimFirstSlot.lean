import Doom.Proofs.E1M1AimFirstSelection
import Doom.Proofs.E1M1AimStackShape
import Doom.Proofs.E1M1FirstIntercept
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimFirstSlot
open Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1MinimumScan (address)
open E1M1InterceptMinimum (minimum)
open E1M1InterceptSetup (result)
open E1M1FirstIntercept (program)
attribute [local irreducible] load32 store32

open E1M1AimFirstSelection (Protected Outcome)

/-- Collection exit through the actual traversal CALL, setup, minimum scan and
first callback CALL. The entry stack shape, first saved return and preserved
words are conclusions of execution, not assumptions about a future state.
This strengthened result also retains the callback slot created by setup. -/
theorem execution (s : X86Memory.State) (f : Option Flags)
    (hits : Array Intercept) (resolve : Intercept → Word)
    (bounded : hits.size≤128)
    (limit : load32 s.memory 0x2c028=address hits.size)
    (encoded : OriginalLineFinish.Encodes s.memory 0x2ba20 resolve hits)
    (protect : Protected (s.regs 4) hits)
    (callback : OriginalInterceptSetup.callback s=0x2b760) :
    ∃ n≤32+7*hits.size, ∃ out,
      X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2cafd⟩ out ∧
      Outcome hits resolve (s.regs 4-24) out ∧
      E1M1AimStackShape.Shape (s.regs 4-24) out ∧
      load32 out.core.memory ((s.regs 4-24)+20)=0x2cb0b ∧
      load32 out.core.memory (s.regs 4-24)=0x2b760 ∧
      (∀ a, E1M1AimEntryFrame.SafeWord (s.regs 4) a →
        load32 out.core.memory a=load32 s.memory a) := by
  have setup := (E1M1InterceptSetup.execution s f hits.size bounded limit protect.cursor).transfer
    program [] (by
      intro pc h
      have same := E1M1TraversalEntry.contains_setup pc h
      exact (E1M1FirstIntercept.contains_entry pc (by rw [same]; exact h)).trans same) (by simp)
  obtain ⟨stack,count,max,countdown,slot,pc⟩ := E1M1InterceptSetup.fields s hits.size protect.cursor
  have pushed : (result s hits.size).core.regs 4-4=s.regs 4-28 := by
    rw [stack]; simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  have records := E1M1InterceptSetup.records s hits.size hits resolve encoded protect.records
  obtain ⟨n,hn,out,run,done,frame,counter,maximum,position⟩ := E1M1ScanInterface.dispatch
    program E1M1FirstIntercept.contains_selection E1M1FirstIntercept.contains_call
    (result s hits.size) hits resolve bounded (count.trans limit) records max pc
    (by rw [stack]; exact protect.target) (by rw [pushed]; exact protect.callCursor)
    (by intro i hi off ho; rw [pushed]; exact protect.callRecords i hi off ho)
  rw [slot,callback,stack] at done position
  refine ⟨23+n,by omega,out,E1M1PspriteStep.prefix_trans setup run,?_,
    E1M1AimStackShape.scan _ _ position,?_,?_,?_⟩
  · rcases done with empty|far|ready
    · refine Or.inl ⟨empty.1,empty.2,?_⟩
      rw [counter,countdown,empty.1]; rfl
    · exact Or.inr (Or.inl far)
    · obtain ⟨best,j,chosen,within,index,inside,arg⟩ := ready.selected
      have pair : best=(best.1,some j) := Prod.ext rfl index
      have budget : BitVec.ofNat 32 hits.size-1=BitVec.ofNat 32 (hits.size-1) :=
        BitVec.ofNat_sub_ofNat_of_le _ 1 (by decide) (by omega)
      exact Or.inr (Or.inr ⟨best.1,j,ready,chosen.trans (congrArg Except.ok pair),
        within,inside,by simp,rfl,arg,by simpa using counter.trans (countdown.trans budget),maximum⟩)
  · have saved := frame (s.regs 4-4) protect.returnCursor (by
      rw [pushed]; exact E1M1AimEntryFrame.return_safe (s.regs 4))
    have address : s.regs 4-24+20=s.regs 4-4 := by
      simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rw [address,saved]; exact E1M1AimEntryFrame.return_word s hits.size
  · have adjacent : Apart ((result s hits.size).core.regs 4)
        ((result s hits.size).core.regs 4-4) := by
      have small : Apart (0#32) (-(4#32)) := by unfold Apart; decide
      simpa [BitVec.sub_eq_add_neg] using OriginalPathXStep.apart_translate
        ((result s hits.size).core.regs 4) (0#32) (-(4#32)) small
    have kept := frame ((result s hits.size).core.regs 4) (by rw [stack]; exact protect.target) adjacent
    rw [slot,callback] at kept
    simpa only [stack] using kept
  · intro a safe
    exact E1M1AimEntryFrame.preserved s hits.size out frame a safe stack
end Doom.Proofs.E1M1AimFirstSlot
