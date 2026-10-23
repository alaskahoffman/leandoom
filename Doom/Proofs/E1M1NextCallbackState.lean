import Doom.Proofs.E1M1SelectionRegisters
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1NextCallbackState
open Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1MinimumScan (address)
open E1M1InterceptMinimum (Best minimum)
open OriginalInterceptGate (saved called gate)
open E1M1AimRepeatProgram (program ReadFrame contains_selection contains_call)
open E1M1CallbackEntry (control records)
attribute [local irreducible] load32 store32

/-- The original CALL supplies both aliases of the chosen record and saves the
end cursor. The buffer still contains the selected record's original fraction. -/
structure Ready (hits : Array Intercept) (resolve : Intercept → Word)
    (target sp : Word) (out : X86Control.State) : Prop extends
    E1M1CallbackEntry.Ready hits resolve target sp out where
  pointer : out.core.regs 3=out.core.regs 0
  cursor : load32 out.core.memory 0x2c028=address hits.size

def Outcome (hits : Array Intercept) (resolve : Intercept → Word)
    (target sp : Word) (out : X86Control.State) : Prop :=
  (hits.size=0 ∧ out.pc=0x2c887) ∨
  (∃ best, minimum hits=.ok best ∧ best.1>65536 ∧ out.pc=0x2c887) ∨
  Ready hits resolve target sp out

/-- Preserve the counter through every scan branch and the authentic indirect
CALL, including the full buffer and exact EAX/EBX argument relationship. -/
theorem dispatch (s : X86Control.State) (hits : Array Collision.Intercept)
    (resolve : Collision.Intercept → Word) (bounded : hits.size≤128)
    (limit : s.core.regs 1=address hits.size)
    (encoded : OriginalLineFinish.Encodes s.core.memory 0x2ba20 resolve hits)
    (maximum : s.core.regs 7=65536)
    (pc : s.pc=(if hits.size=0 then 0x2c887 else 0x2c841))
    (targetSafe : Apart (s.core.regs 4) 0x2c028)
    (cursorSafe : Apart 0x2c028 (s.core.regs 4-4))
    (recordSafe : ∀ i<hits.size, ∀ off∈[(0#32),4,8],
      Apart (OriginalLineCollection.slot 0x2ba20 i off) (s.core.regs 4-4)) :
    ∃ n≤9+7*hits.size, ∃ out,
      X86CodeMemory.Prefix FloorCaller.cm program [] n s out ∧
      Outcome hits resolve (load32 s.core.memory (s.core.regs 4)) (s.core.regs 4) out ∧ ReadFrame s.core out ∧
      out.core.regs 6=s.core.regs 6 ∧ out.core.regs 7=65536 := by
  by_cases empty : hits.size=0
  · exact ⟨0,by omega,s,.nil _,Or.inl ⟨empty,by simpa only [empty,ite_true] using pc⟩,(by intro a hc hs; rfl),rfl,maximum⟩
  · have start : s.pc=0x2c841 := by simpa only [if_neg empty] using pc
    obtain ⟨n,hn,selected,best,run,choice,state,exit,mem,maxOut,sp,counter⟩ :=
      E1M1SelectionRegisters.execution s.core s.flags hits bounded limit
        (E1M1MinimumScan.fractions _ _ _ encoded) maximum
    have run := run.transfer program [] contains_selection (by simp)
    rw [OriginalPathXStep.at_pc _ _ start] at run
    by_cases far : best.1>65536
    · refine ⟨n,by omega,gate selected.core,run,Or.inr (Or.inl ⟨best,choice,far,by simpa only [if_pos far] using exit⟩),?_,counter,maxOut⟩
      intro a hc hs
      change load32 (store32 selected.core.memory 0x2c028 (selected.core.regs 1)) a=_
      rw [load_store_apart _ _ _ _ hc,mem]
    · have atCall : (gate selected.core).pc=0x2c868 := by simpa only [if_neg far] using exit
      obtain ⟨j,chosen,inside⟩ := E1M1InterceptGate.admitted hits best choice far
      have callRun := (X86CodeMemory.lift_success
        (OriginalInterceptGate.call_execution (saved selected.core) (gate selected.core).flags) FloorCaller.cm).transfer
        program [] contains_call (by simp)
      change X86CodeMemory.Prefix FloorCaller.cm program [] 2
        ⟨(gate selected.core).core,(gate selected.core).flags,0x2c868⟩ _ at callRun
      rw [OriginalPathXStep.at_pc _ _ atCall] at callRun
      have fields := control selected.core (gate selected.core).flags (by rw [sp]; exact targetSafe)
      refine ⟨n+2,by omega,called (saved selected.core) (gate selected.core).flags,
        E1M1PspriteStep.prefix_trans run callRun,Or.inr (Or.inr ⟨⟨?_,?_,fields.2.2,?_,?_⟩,?_,?_⟩),?_,?_,?_⟩
      · exact fields.1.trans (by rw [mem,sp])
      · exact fields.2.1.trans (by rw [sp])
      · exact records _ _ hits resolve bounded (by rw [mem]; exact encoded) (by rw [sp]; exact recordSafe)
      · refine ⟨best,j,choice,far,chosen,inside,?_⟩
        simpa [called,saved,X86Routine.pushWord,put,write] using state.choice j chosen
      · simp [called,saved,X86Routine.pushWord,put,write]
      · change load32 (store32 (store32 selected.core.memory 0x2c028 (selected.core.regs 1))
          (selected.core.regs 4-4) 0x2c86d) 0x2c028=address hits.size
        rw [load_store_apart _ _ _ _ (by rw [sp]; exact cursorSafe),load_store]
        exact state.limit
      · intro a hc hs
        exact (E1M1CallbackEntry.frame selected.core (gate selected.core).flags a hc (by rw [sp]; exact hs)).trans (by rw [mem])
      · simpa [called,saved,X86Routine.pushWord,put,write] using counter
      · simpa [called,saved,X86Routine.pushWord,put,write] using maxOut

/-- The callback function slot survives CALL even when the stack wraps. -/
theorem callback_slot (s : X86Memory.State) (out : X86Control.State)
    (frame : ReadFrame s out) (safe : Apart (s.regs 4) 0x2c028) :
    load32 out.core.memory (s.regs 4)=load32 s.memory (s.regs 4) := by
  apply frame _ safe
  have small : Apart (0#32) (-4) := by unfold Apart; decide
  simpa only [BitVec.add_zero,BitVec.sub_eq_add_neg] using
    OriginalPathXStep.apart_translate (s.regs 4) (0#32) (-4) small

end Doom.Proofs.E1M1NextCallbackState
