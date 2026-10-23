import Doom.Proofs.E1M1AimNextSelection
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1AimRepeatProgram
open Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1MinimumScan (address)
attribute [local irreducible] load32 store32

/-- One byte-decoded program for the callback, its parent and repeated selection. -/
def program : X86Routine.Program := fun pc =>
  match E1M1AimResume.program pc with
  | some op => some op
  | none => match OriginalInterceptSetup.program pc with
    | some op => some op
    | none => OriginalInterceptMinimum.program pc

theorem contains_resume (pc : Nat) (h : E1M1AimResume.program pc≠none) :
    program pc=E1M1AimResume.program pc := by
  unfold program; cases eq : E1M1AimResume.program pc <;> simp_all

theorem contains_setup (pc : Nat) (h : OriginalInterceptSetup.program pc≠none) :
    program pc=OriginalInterceptSetup.program pc := by
  have range : (0x2c810≤pc ∧ pc<0x2c841) ∨ (0x2cafd≤pc ∧ pc<0x2cb0b) := by
    by_cases a : 0x2c810≤pc ∧ pc<0x2c841
    · exact Or.inl a
    · by_cases b : 0x2cafd≤pc ∧ pc<0x2cb0b
      · exact Or.inr b
      · simp [OriginalInterceptSetup.program,OriginalInterceptSetup.bytesProgram,a,b] at h
  rcases range with a|b
  · have all : ∀ i : Fin 49, program (0x2c810+i.val)=OriginalInterceptSetup.program (0x2c810+i.val) := by decide
    have eq : 0x2c810+(pc-0x2c810)=pc := by omega
    simpa only [eq] using all ⟨pc-0x2c810,by omega⟩
  · have all : ∀ i : Fin 14, program (0x2cafd+i.val)=OriginalInterceptSetup.program (0x2cafd+i.val) := by decide
    have eq : 0x2cafd+(pc-0x2cafd)=pc := by omega
    simpa only [eq] using all ⟨pc-0x2cafd,by omega⟩

theorem contains_selection (pc : Nat) (h : E1M1InterceptGate.program pc≠none) :
    program pc=E1M1InterceptGate.program pc := by
  have range : 0x2c841≤pc ∧ pc<0x2c887 := by
    by_cases a : pc<0x2c85e
    · have good : 0x2c841≤pc ∧ pc<0x2c85e := by
        by_cases good : 0x2c841≤pc ∧ pc<0x2c85e
        · exact good
        · simp [E1M1InterceptGate.program,a,OriginalInterceptMinimum.program,
            OriginalInterceptMinimum.bytesProgram] at h
          omega
      omega
    · have good : 0x2c85e≤pc ∧ pc<0x2c887 := by
        by_cases good : 0x2c85e≤pc ∧ pc<0x2c887
        · exact good
        · simp [E1M1InterceptGate.program,a,OriginalInterceptGate.program,
            OriginalInterceptGate.bytesProgram,good] at h
      omega
  have all : ∀ i : Fin 70, program (0x2c841+i.val)=E1M1InterceptGate.program (0x2c841+i.val) := by decide
  have eq : 0x2c841+(pc-0x2c841)=pc := by omega
  simpa only [eq] using all ⟨pc-0x2c841,by omega⟩

theorem contains_call (pc : Nat) (h : OriginalInterceptGate.program pc≠none) :
    program pc=OriginalInterceptGate.program pc := by
  have eq := E1M1InterceptGate.contains_gate pc h
  exact (contains_selection pc (by rw [eq]; exact h)).trans eq

open E1M1AimNextSelection (head)
theorem head_execution (s : X86Memory.State) (f : Option Flags) :
    X86CodeMemory.Prefix FloorCaller.cm program [] 4 ⟨s,f,0x2c83a⟩ (head s) := by
  have run : X86Routine.Prefix OriginalInterceptSetup.listed [] 4 ⟨s,f,0x2c83a⟩ (head s) := by
    apply X86Routine.Prefix.step (middle := ⟨put s 0 (s.regs 6),f,0x2c83c⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,put,write,blockPreservesFlags])
    apply X86Routine.Prefix.step (middle := ⟨(head s).core,none,0x2c83d⟩) (by simp) (by rfl) (by
      simp [head,X86Routine.execute,put,write,BitVec.sub_eq_add_neg])
    apply X86Routine.Prefix.step (middle := ⟨(head s).core,(head s).flags,0x2c83f⟩) (by simp) (by rfl) (by
      simp [head,X86Routine.execute,X86Control.execute,put,write])
    apply X86Routine.Prefix.step (middle := head s) (by simp) (by rfl) (by
      by_cases zero : s.regs 6=(0#32) <;>
        simp [head,X86Routine.execute,X86Control.execute,logical32,zero,put,write])
    exact .nil _
  have run := run.transfer OriginalInterceptSetup.program [] OriginalInterceptSetup.decoded (by simp)
  exact (X86CodeMemory.lift_success run FloorCaller.cm).transfer program [] contains_setup (by simp)

open E1M1CallbackEntry (Outcome control records)
open E1M1InterceptMinimum (Best minimum)
open OriginalInterceptGate (saved called gate)
/-- Words outside the two traversal stores survive selection and CALL. -/
def ReadFrame (s : X86Memory.State) (out : X86Control.State) : Prop :=
  ∀ a, Apart a 0x2c028 → Apart a (s.regs 4-4) →
    load32 out.core.memory a=load32 s.memory a

theorem dispatch (s : X86Control.State) (hits : Array Collision.Intercept)
    (resolve : Collision.Intercept → Word) (bounded : hits.size≤128)
    (limit : s.core.regs 1=address hits.size)
    (encoded : OriginalLineFinish.Encodes s.core.memory 0x2ba20 resolve hits)
    (maximum : s.core.regs 7=65536)
    (pc : s.pc=(if hits.size=0 then 0x2c887 else 0x2c841))
    (targetSafe : Apart (s.core.regs 4) 0x2c028)
    (recordSafe : ∀ i<hits.size, ∀ off∈[(0#32),4,8],
      Apart (OriginalLineCollection.slot 0x2ba20 i off) (s.core.regs 4-4)) :
    ∃ n≤9+7*hits.size, ∃ out,
      X86CodeMemory.Prefix FloorCaller.cm program [] n s out ∧
      Outcome hits resolve (load32 s.core.memory (s.core.regs 4)) (s.core.regs 4) out ∧ ReadFrame s.core out := by
  by_cases empty : hits.size=0
  · exact ⟨0,by omega,s,.nil _,Or.inl ⟨empty,by simpa only [empty,ite_true] using pc⟩,by intro a hc hs; rfl⟩
  · have start : s.pc=0x2c841 := by simpa only [if_neg empty] using pc
    obtain ⟨n,hn,selected,best,run,choice,state,exit,mem,maxOut,sp⟩ :=
      E1M1SelectionFrame.execution s.core s.flags hits bounded limit
        (E1M1MinimumScan.fractions _ _ _ encoded) maximum
    have run := run.transfer program [] contains_selection (by simp)
    rw [OriginalPathXStep.at_pc _ _ start] at run
    by_cases far : best.1>65536
    · refine ⟨n,by omega,gate selected.core,run,Or.inr (Or.inl ⟨best,choice,far,by simpa only [if_pos far] using exit⟩),?_⟩
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
        E1M1PspriteStep.prefix_trans run callRun,Or.inr (Or.inr ⟨?_,?_,fields.2.2,?_,?_⟩),?_⟩
      · exact fields.1.trans (by rw [mem,sp])
      · exact fields.2.1.trans (by rw [sp])
      · exact records _ _ hits resolve bounded (by rw [mem]; exact encoded) (by rw [sp]; exact recordSafe)
      · refine ⟨best,j,choice,far,chosen,inside,?_⟩
        simpa [called,saved,X86Routine.pushWord,put,write] using state.choice j chosen
      · intro a hc hs
        exact (E1M1CallbackEntry.frame selected.core (gate selected.core).flags a hc (by rw [sp]; exact hs)).trans (by rw [mem])

theorem repeat_selection (s : X86Memory.State) (f : Option Flags) (hits : Array Intercept)
    (resolve : Intercept → Word) (bounded : hits.size≤128) (nonempty : hits.size≠0)
    (limit : s.regs 1=address hits.size)
    (encoded : OriginalLineFinish.Encodes s.memory 0x2ba20 resolve hits)
    (maximum : s.regs 7=65536) (targetSafe : Apart (s.regs 4) 0x2c028)
    (recordSafe : ∀ i<hits.size, ∀ off∈[(0#32),4,8],
      Apart (OriginalLineCollection.slot 0x2ba20 i off) (s.regs 4-4)) :
    ∃ n≤13+7*hits.size, ∃ out,
      X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2c83a⟩ out ∧
      E1M1AimNextSelection.Outcome s hits resolve out ∧ ReadFrame s out := by
  have run := head_execution s f
  by_cases zero : s.regs 6=(0#32)
  · exact ⟨4,by omega,head s,run,Or.inl ⟨zero,rfl⟩,by intro a hc hs; rfl⟩
  · obtain ⟨n,hn,out,tail,done,frame⟩ := dispatch (head s) hits resolve bounded
      (by simpa [head,put,write] using limit) encoded
      (by simpa [head,put,write] using maximum)
      (by simp [head,zero,nonempty]) targetSafe recordSafe
    exact ⟨4+n,by omega,out,E1M1PspriteStep.prefix_trans run tail,Or.inr ⟨zero,done⟩,frame⟩

end Doom.Proofs.E1M1AimRepeatProgram
