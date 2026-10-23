import Doom.Proofs.E1M1AimScanStack
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1ScanInterface
open Verification X86 X86Memory X86Control BlockSummary Collision E1M1SelectionHistory
open E1M1MinimumScan (address)
open E1M1InterceptMinimum (Best minimum)
open OriginalInterceptGate (saved called gate)
open E1M1AimRepeatProgram (ReadFrame)
open E1M1AimScanStack (Position)
open E1M1CallbackEntry (control records)
open E1M1AimNextSelection (head)
attribute [local irreducible] load32 store32

/-- The proved scan can be linked into any program that retains its decoded
selection and CALL instructions. No callback implementation is needed here. -/
theorem dispatch (program : X86Routine.Program)
    (contains_selection : ∀ pc, E1M1InterceptGate.program pc≠none →
      program pc=E1M1InterceptGate.program pc)
    (contains_call : ∀ pc, OriginalInterceptGate.program pc≠none →
      program pc=OriginalInterceptGate.program pc)
    (s : X86Control.State) (hits : Array Collision.Intercept)
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
      E1M1NextCallbackState.Outcome hits resolve (load32 s.core.memory (s.core.regs 4)) (s.core.regs 4) out ∧ ReadFrame s.core out ∧
      out.core.regs 6=s.core.regs 6 ∧ out.core.regs 7=65536 ∧
      Position (load32 s.core.memory (s.core.regs 4)) (s.core.regs 4) out := by
  by_cases empty : hits.size=0
  · exact ⟨0,by omega,s,.nil _,Or.inl ⟨empty,by simpa only [empty,ite_true] using pc⟩,(by intro a hc hs; rfl),rfl,maximum,Or.inl ⟨by simpa only [empty,ite_true] using pc,rfl⟩⟩
  · have start : s.pc=0x2c841 := by simpa only [if_neg empty] using pc
    obtain ⟨n,hn,selected,best,run,choice,state,exit,mem,maxOut,sp,counter⟩ :=
      E1M1SelectionRegisters.execution s.core s.flags hits bounded limit
        (E1M1MinimumScan.fractions _ _ _ encoded) maximum
    have run := run.transfer program [] contains_selection (by simp)
    rw [OriginalPathXStep.at_pc _ _ start] at run
    by_cases far : best.1>65536
    · refine ⟨n,by omega,gate selected.core,run,Or.inr (Or.inl ⟨best,choice,far,by simpa only [if_pos far] using exit⟩),?_,counter,maxOut,Or.inl ⟨by simpa only [if_pos far] using exit,by simpa [gate,saved] using sp⟩⟩
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
        E1M1PspriteStep.prefix_trans run callRun,Or.inr (Or.inr ⟨⟨?_,?_,fields.2.2,?_,?_⟩,?_,?_⟩),?_,?_,?_,?_⟩
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

      · exact Or.inr ⟨fields.1.trans (by rw [mem,sp]),fields.2.1.trans (by rw [sp])⟩

end Doom.Proofs.E1M1ScanInterface
