import Doom.Proofs.E1M1SelectionFrame
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1CallbackEntry
open Verification X86 X86Memory X86Control BlockSummary
open E1M1MinimumScan (address)
open E1M1InterceptMinimum (Best minimum)
open OriginalInterceptGate (saved called gate)
open E1M1FirstIntercept (program)
attribute [local irreducible] load32 store32

/-- Every record word in the vanilla buffer is disjoint from the cursor global. -/
theorem cursor_apart (i : Nat) (bound : i<128) (off : Word) (member : off∈[(0#32),4,8]) :
    Apart (OriginalLineCollection.slot 0x2ba20 i off) 0x2c028 := by
  have all : ∀ j : Fin 128,
      Apart (OriginalLineCollection.slot 0x2ba20 j.val 0) 0x2c028 ∧
      Apart (OriginalLineCollection.slot 0x2ba20 j.val 4) 0x2c028 ∧
      Apart (OriginalLineCollection.slot 0x2ba20 j.val 8) 0x2c028 := by unfold Apart; decide
  have h := all ⟨i,bound⟩
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl
  · exact h.1
  · exact h.2.1
  · exact h.2.2

/-- The range gate writes the cursor, then CALL pushes its real return address. -/
theorem memory (s : X86Memory.State) (f : Option Flags) :
    (called (saved s) f).core.memory=
      store32 (store32 s.memory 0x2c028 (s.regs 1)) (s.regs 4-4) 0x2c86d := rfl

theorem frame (s : X86Memory.State) (f : Option Flags) (a : Word)
    (cursor : Apart a 0x2c028) (stack : Apart a (s.regs 4-4)) :
    load32 (called (saved s) f).core.memory a=load32 s.memory a := by
  rw [memory,load_store_apart _ _ _ _ stack,load_store_apart _ _ _ _ cursor]

/-- Derive the actual indirect destination and the return word, without running
or assuming anything about the callee. -/
theorem control (s : X86Memory.State) (f : Option Flags) (safe : Apart (s.regs 4) 0x2c028) :
    (called (saved s) f).pc=(load32 s.memory (s.regs 4)).toNat ∧
    (called (saved s) f).core.regs 4=s.regs 4-4 ∧
    load32 (called (saved s) f).core.memory ((called (saved s) f).core.regs 4)=0x2c86d := by
  refine ⟨?_,?_,?_⟩
  · change (load32 (store32 s.memory 0x2c028 (s.regs 1)) (s.regs 4)).toNat=_
    rw [load_store_apart _ _ _ _ safe]
  · simp [called,saved,X86Routine.pushWord,put,write]
  · change load32 (store32 (store32 s.memory 0x2c028 (s.regs 1)) (s.regs 4-4) 0x2c86d) (s.regs 4-4)=_
    exact load_store _ _ _

/-- Fractions, line/thing tags, and object pointers all survive both stores. -/
theorem records (s : X86Memory.State) (f : Option Flags) (hits : Array Collision.Intercept)
    (resolve : Collision.Intercept → Word) (bound : hits.size≤128)
    (encoded : OriginalLineFinish.Encodes s.memory 0x2ba20 resolve hits)
    (stack : ∀ i<hits.size, ∀ off∈[(0#32),4,8],
      Apart (OriginalLineCollection.slot 0x2ba20 i off) (s.regs 4-4)) :
    OriginalLineFinish.Encodes (called (saved s) f).core.memory 0x2ba20 resolve hits := by
  intro i hi
  rcases encoded i hi with ⟨frac,kind,pointer⟩
  refine ⟨?_,?_,?_⟩
  · exact (frame s f _ (by simpa [OriginalLineCollection.slot] using cursor_apart i (by omega) 0 (by simp))
      (by simpa [OriginalLineCollection.slot] using stack i hi 0 (by simp))).trans frac
  · exact (frame s f _ (cursor_apart i (by omega) 4 (by simp)) (stack i hi 4 (by simp))).trans kind
  · exact (frame s f _ (cursor_apart i (by omega) 8 (by simp)) (stack i hi 8 (by simp))).trans pointer

/-- Data available to a callback proof at the reached machine state. -/
structure Ready (hits : Array Collision.Intercept) (resolve : Collision.Intercept → Word)
    (target sp : Word) (out : X86Control.State) : Prop where
  pc : out.pc=target.toNat
  stack : out.core.regs 4=sp-4
  returnWord : load32 out.core.memory (out.core.regs 4)=0x2c86d
  records : OriginalLineFinish.Encodes out.core.memory 0x2ba20 resolve hits
  selected : ∃ best j, minimum hits=.ok best ∧ ¬best.1>65536 ∧
    best.2=some j ∧ j<hits.size ∧ out.core.regs 0=address j

def Outcome (hits : Array Collision.Intercept) (resolve : Collision.Intercept → Word)
    (target sp : Word) (out : X86Control.State) : Prop :=
  (hits.size=0 ∧ out.pc=0x2c887) ∨
  (∃ best, minimum hits=.ok best ∧ best.1>65536 ∧ out.pc=0x2c887) ∨
  Ready hits resolve target sp out

/-- Selection through the real CALL, retaining the callback slot, stack, return
word and full record image from the start of selection. -/
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
      Outcome hits resolve (load32 s.core.memory (s.core.regs 4)) (s.core.regs 4) out := by
  by_cases empty : hits.size=0
  · exact ⟨0,by omega,s,.nil _,Or.inl ⟨empty,by simpa only [empty,ite_true] using pc⟩⟩
  · have start : s.pc=0x2c841 := by simpa only [if_neg empty] using pc
    obtain ⟨n,hn,selected,best,run,choice,state,exit,mem,maxOut,sp⟩ :=
      E1M1SelectionFrame.execution s.core s.flags hits bounded limit
        (E1M1MinimumScan.fractions _ _ _ encoded) maximum
    have run := run.transfer program [] E1M1FirstIntercept.contains_selection (by simp)
    rw [OriginalPathXStep.at_pc _ _ start] at run
    by_cases far : best.1>65536
    · exact ⟨n,by omega,gate selected.core,run,Or.inr (Or.inl ⟨best,choice,far,by simpa only [if_pos far] using exit⟩)⟩
    · have atCall : (gate selected.core).pc=0x2c868 := by simpa only [if_neg far] using exit
      obtain ⟨j,chosen,inside⟩ := E1M1InterceptGate.admitted hits best choice far
      have callRun := (X86CodeMemory.lift_success
        (OriginalInterceptGate.call_execution (saved selected.core) (gate selected.core).flags) FloorCaller.cm).transfer
        program [] E1M1FirstIntercept.contains_call (by simp)
      change X86CodeMemory.Prefix FloorCaller.cm program [] 2
        ⟨(gate selected.core).core,(gate selected.core).flags,0x2c868⟩ _ at callRun
      rw [OriginalPathXStep.at_pc _ _ atCall] at callRun
      have fields := control selected.core (gate selected.core).flags (by rw [sp]; exact targetSafe)
      refine ⟨n+2,by omega,called (saved selected.core) (gate selected.core).flags,
        E1M1PspriteStep.prefix_trans run callRun,Or.inr (Or.inr ⟨?_,?_,fields.2.2,?_,?_⟩)⟩
      · exact fields.1.trans (by rw [mem,sp])
      · exact fields.2.1.trans (by rw [sp])
      · exact records _ _ hits resolve bounded (by rw [mem]; exact encoded) (by rw [sp]; exact recordSafe)
      · refine ⟨best,j,choice,far,chosen,inside,?_⟩
        simpa [called,saved,X86Routine.pushWord,put,write] using state.choice j chosen

/-- The pointer passed in EAX reads the exact source hit, including its tag and
resolved line/thing pointer, in the callback's current memory. -/
theorem selected_record (hits : Array Collision.Intercept) (resolve : Collision.Intercept → Word)
    (target sp : Word) (out : X86Control.State) (ready : Ready hits resolve target sp out) :
    ∃ j, ∃ hi : j<hits.size,
      OriginalLineFinish.RecordAt out.core.memory (out.core.regs 0) hits[j] (resolve hits[j]) := by
  obtain ⟨best,j,_,_,_,hi,arg⟩ := ready.selected
  refine ⟨j,hi,?_⟩
  rw [arg]
  simpa [E1M1MinimumScan.address,BitVec.ofNat_add] using ready.records j hi
end Doom.Proofs.E1M1CallbackEntry
