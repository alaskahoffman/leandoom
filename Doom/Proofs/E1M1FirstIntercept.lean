import Doom.Proofs.E1M1TraversalEntry
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1FirstIntercept
open Verification X86 X86Memory X86Control BlockSummary
open E1M1InterceptMinimum (Best minimum)
open E1M1MinimumScan (address Fractions Represents)
open OriginalInterceptGate (gate saved called)
attribute [local irreducible] load32 store32

/-- Collection/setup and ordered selection use one authenticated program. -/
def program : X86Routine.Program := fun pc =>
  match E1M1TraversalEntry.program pc with
  | some op => some op
  | none => E1M1InterceptGate.program pc

theorem contains_entry (pc : Nat) (h : E1M1TraversalEntry.program pc≠none) :
    program pc=E1M1TraversalEntry.program pc := by
  unfold program
  cases eq : E1M1TraversalEntry.program pc <;> simp_all

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

/-- Exhaustive first-pass outcomes. The callback case carries the live minimum,
its in-bounds index and the exact machine state at the real indirect-call target.
It does not assert that the callback body has executed or identify its target. -/
def Boundary (hits : Array Collision.Intercept) (out : X86Control.State) : Prop :=
  (hits.size=0 ∧ out.pc=0x2c887) ∨
  ∃ best, minimum hits=.ok best ∧
    ((best.1>65536 ∧ out.pc=0x2c887) ∨
      (¬best.1>65536 ∧ ∃ j, best.2=some j ∧ j<hits.size ∧ out.core.regs 0=address j ∧
        ∃ selected : X86Memory.State, Represents selected hits hits.size best ∧
          out=called (saved selected) (gate selected).flags))

/-- From the actual setup exit, either bypass the scan, reject its minimum, or
run the original indirect CALL with the source-selected record pointer. -/
theorem dispatch (s : X86Control.State) (hits : Array Collision.Intercept)
    (bounded : hits.size≤128) (limit : s.core.regs 1=address hits.size)
    (encoded : Fractions s.core.memory hits) (maximum : s.core.regs 7=65536)
    (pc : s.pc=(if hits.size=0 then 0x2c887 else 0x2c841)) :
    ∃ n≤9+7*hits.size, ∃ out,
      X86CodeMemory.Prefix FloorCaller.cm program [] n s out ∧ Boundary hits out := by
  by_cases empty : hits.size=0
  · exact ⟨0,by omega,s,.nil _,Or.inl ⟨empty,by simpa only [empty,ite_true] using pc⟩⟩
  · have start : s.pc=0x2c841 := by simpa only [if_neg empty] using pc
    obtain ⟨n,hn,selected,best,run,choice,state,exit,_,_⟩ :=
      E1M1InterceptGate.execution s.core s.flags hits bounded limit encoded maximum
    have run := run.transfer program [] contains_selection (by simp)
    rw [OriginalPathXStep.at_pc _ _ start] at run
    by_cases far : best.1>65536
    · exact ⟨n,by omega,gate selected.core,run,Or.inr ⟨best,choice,Or.inl ⟨far,by simpa only [if_pos far] using exit⟩⟩⟩
    · have atCall : (gate selected.core).pc=0x2c868 := by simpa only [if_neg far] using exit
      obtain ⟨j,chosen,inside⟩ := E1M1InterceptGate.admitted hits best choice far
      have callRun := (X86CodeMemory.lift_success
        (OriginalInterceptGate.call_execution (saved selected.core) (gate selected.core).flags) FloorCaller.cm).transfer
        program [] contains_call (by simp)
      change X86CodeMemory.Prefix FloorCaller.cm program [] 2
        ⟨(gate selected.core).core,(gate selected.core).flags,0x2c868⟩ _ at callRun
      rw [OriginalPathXStep.at_pc _ _ atCall] at callRun
      refine ⟨n+2,by omega,called (saved selected.core) (gate selected.core).flags,
        E1M1PspriteStep.prefix_trans run callRun,Or.inr ⟨best,choice,Or.inr ⟨far,j,chosen,inside,?_,selected.core,state,rfl⟩⟩⟩
      simpa [called,saved,X86Routine.pushWord,put,write] using state.choice j chosen

/-- The live ordered tail does no work for an empty collection, matching the
machine's immediate bypass rather than an artificial empty minimum scan. -/
theorem empty_tail (r : Collision.PathResult) (visit : Collision.Intercept → Nat → Bool)
    (empty : r.collected.size=0) : E1M1QuerySource.visitHits r visit=.ok r := by
  rw [E1M1InterceptMinimum.live]
  simp [E1M1InterceptMinimum.withMinimum,empty,Std.Legacy.Range.forIn_eq_forIn_range']
  rfl

/-- If the first minimum is beyond range, the exact live tail returns without
visiting a hit, for any callback function. -/
theorem rejected_tail (r : Collision.PathResult) (visit : Collision.Intercept → Nat → Bool)
    (best : Best) (selected : minimum r.collected=.ok best) (far : best.1>65536) :
    E1M1QuerySource.visitHits r visit=.ok r := by
  rw [E1M1InterceptMinimum.live]
  cases size : r.collected.size with
  | zero =>
    simp [E1M1InterceptMinimum.withMinimum,size,Std.Legacy.Range.forIn_eq_forIn_range']
    rfl
  | succ n =>
    simp [E1M1InterceptMinimum.withMinimum,Std.Legacy.Range.forIn_eq_forIn_range',
      Std.Legacy.Range.size,size,List.range'_succ,List.forIn_cons,selected]
    simp only [show Except.ok best=(pure best : Except String Best) from rfl,pure_bind,if_pos far]
    rfl
end Doom.Proofs.E1M1FirstIntercept
