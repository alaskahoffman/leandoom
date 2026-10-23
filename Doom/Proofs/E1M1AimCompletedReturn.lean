import Doom.Proofs.OriginalPathReturn
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1AimCompletedReturn
open Verification X86 X86Memory X86Control BlockSummary Collision
attribute [local irreducible] load32 store32 E1M1AimTraversalReturn.result

def legacy : X86Routine.Program := fun pc =>
  match OriginalAimQuery.program pc with
  | some op => some op
  | none => E1M1AimTraversalReturn.program pc
def program : X86ReturnCleanup.Program := fun pc =>
  match OriginalPathReturn.program pc with
  | some op => some op
  | none => X86ReturnCleanup.embed legacy pc

theorem contains_aim (pc : Nat) (h : OriginalAimQuery.program pc≠none) :
    legacy pc=OriginalAimQuery.program pc := by
  unfold legacy; cases eq : OriginalAimQuery.program pc <;> simp_all

theorem contains_traversal (pc : Nat) (h : E1M1AimTraversalReturn.program pc≠none) :
    legacy pc=E1M1AimTraversalReturn.program pc := by
  have absent : OriginalAimQuery.program pc=none := by
    by_cases first : 0x2bb80≤pc ∧ pc<0x2bba0
    · have all : ∀ i : Fin 32, E1M1AimTraversalReturn.program (0x2bb80+i.val)=none := by decide
      have eq : 0x2bb80+(pc-0x2bb80)=pc := by omega
      exact False.elim (h (by simpa only [eq] using all ⟨pc-0x2bb80,by omega⟩))
    · by_cases second : 0x2bbff≤pc ∧ pc<0x2bc19
      · have all : ∀ i : Fin 26, E1M1AimTraversalReturn.program (0x2bbff+i.val)=none := by decide
        have eq : 0x2bbff+(pc-0x2bbff)=pc := by omega
        exact False.elim (h (by simpa only [eq] using all ⟨pc-0x2bbff,by omega⟩))
      · simp [OriginalAimQuery.program,OriginalAimQuery.bytesProgram,first,second]
  simp [legacy,absent]

theorem contains_ret8 (pc : Nat) (h : OriginalPathReturn.program pc≠none) :
    program pc=OriginalPathReturn.program pc := by
  unfold program; cases eq : OriginalPathReturn.program pc <;> simp_all

theorem contains_legacy (pc : Nat) (h : X86ReturnCleanup.embed legacy pc≠none) :
    program pc=X86ReturnCleanup.embed legacy pc := by
  have absent : OriginalPathReturn.program pc=none := by
    by_cases inside : 0x2cb11≤pc ∧ pc<0x2cb14
    · have all : ∀ i : Fin 3, X86ReturnCleanup.embed legacy (0x2cb11+i.val)=none := by decide
      have eq : 0x2cb11+(pc-0x2cb11)=pc := by omega
      exact False.elim (h (by simpa only [eq] using all ⟨pc-0x2cb11,by omega⟩))
    · simp [OriginalPathReturn.program,OriginalPathReturn.bytesProgram,inside]
  simp [program,absent]

def parent (s : X86Control.State) :=
  OriginalPathReturn.result (E1M1AimTraversalReturn.result s).core (E1M1AimTraversalReturn.result s).flags
def result (s : X86Control.State) := OriginalAimQuery.returned (parent s).core

/-- The real RET 8 lands at the original aim-return test, preserving all memory.
These are endpoint stack premises, not yet derived from the full hit loop. -/
theorem parent_layout (s : X86Control.State)
    (safe : Apart (s.core.regs 4+84) 0x2c028)
    (address : load32 s.core.memory (s.core.regs 4+84)=0x2bbff) :
    (parent s).pc=0x2bbff ∧ (parent s).core.regs 4=s.core.regs 4+96 ∧
    (parent s).core.memory=(E1M1AimTraversalReturn.result s).core.memory := by
  have addr := E1M1AimTraversalReturn.caller_address s safe address
  have parts := OriginalPathReturn.layout (E1M1AimTraversalReturn.result s).core (E1M1AimTraversalReturn.result s).flags
  refine ⟨?_,?_,parts.2.2.1⟩
  · change (OriginalPathReturn.result _ _).pc=_
    rw [parts.1,addr]; rfl
  · change (OriginalPathReturn.result _ _).core.regs 4=_
    rw [parts.2.1,(E1M1AimTraversalReturn.layout s).2.1,BitVec.add_assoc]; rfl

/-- Continuous execution through both actual returns and the final aim epilogue,
including the source result in EAX. The saved return addresses remain explicit. -/
theorem execution (s : X86Control.State)
    (exit : s.pc=0x2c887 ∨ s.pc=0x2c88c)
    (safe20 : Apart (s.core.regs 4+20) 0x2c028)
    (address20 : load32 s.core.memory (s.core.regs 4+20)=0x2cb0b)
    (safe84 : Apart (s.core.regs 4+84) 0x2c028)
    (address84 : load32 s.core.memory (s.core.regs 4+84)=0x2bbff) :
    ∃ n≤21, X86ReturnCleanup.Prefix FloorCaller.cm program [] n s (result s) := by
  obtain ⟨n,bound,head⟩ := E1M1AimTraversalReturn.execution s exit safe20 address20
  have head := (X86ReturnCleanup.lift (head.transfer legacy [] contains_traversal (by simp))).transfer program contains_legacy
  have mid := (OriginalPathReturn.execution FloorCaller.cm (E1M1AimTraversalReturn.result s).core
    (E1M1AimTraversalReturn.result s).flags).transfer program contains_ret8
  have same : E1M1AimTraversalReturn.result s=
      ⟨(E1M1AimTraversalReturn.result s).core,(E1M1AimTraversalReturn.result s).flags,0x2cb11⟩ := by
    rw [← (E1M1AimTraversalReturn.layout s).1]
  rw [← same] at mid
  have tail := (X86CodeMemory.lift_success
    (OriginalAimQuery.return_execution (parent s).core (parent s).flags) FloorCaller.cm).transfer legacy [] contains_aim (by simp)
  have tail := (X86ReturnCleanup.lift tail).transfer program contains_legacy
  have landing := (parent_layout s safe84 address84).1
  have sameParent : parent s=⟨(parent s).core,(parent s).flags,0x2bbff⟩ := by rw [← landing]
  rw [← sameParent] at tail
  exact ⟨n+1+8,by omega,(head.trans mid).trans tail⟩

theorem memory (s : X86Control.State) :
    (result s).core.memory=store32 s.core.memory 0x2c028 (s.core.regs 1) := by
  rw [result,OriginalAimQuery.return_memory]
  change (E1M1AimTraversalReturn.result s).core.memory=_
  exact E1M1AimTraversalReturn.memory s

/-- This is the actual final EAX, including a null target with stale slope and
an admitted non-null target whose selected slope is zero. -/
theorem value (initial : Array Intercept) (resolve : Intercept → Word)
    (s : X86Control.State) (answer : AimResult)
    (exit : E1M1AimHitMemory.Exit initial resolve s answer)
    (nonnull : ∀ j<initial.size, resolve initial[j]!≠0) :
    (result s).core.regs 0=answer.slope.raw.toBitVec := by
  rw [result,OriginalAimQuery.return_value]
  exact E1M1AimTraversalReturn.chosen initial resolve s answer exit nonnull

theorem layout (s : X86Control.State) :
    (result s).core.regs 4=s.core.regs 4+116 ∧
    (result s).pc=(load32 (result s).core.memory (s.core.regs 4+112)).toNat ∧
    (result s).core.regs 5=load32 (result s).core.memory (s.core.regs 4+96) ∧
    (result s).core.regs 7=load32 (result s).core.memory (s.core.regs 4+100) ∧
    (result s).core.regs 6=load32 (result s).core.memory (s.core.regs 4+104) ∧
    (result s).core.regs 1=load32 (result s).core.memory (s.core.regs 4+108) := by
  have stack : (parent s).core.regs 4=s.core.regs 4+96 := by
    have h := (OriginalPathReturn.layout (E1M1AimTraversalReturn.result s).core (E1M1AimTraversalReturn.result s).flags).2.1
    change (parent s).core.regs 4=_ at h
    rw [h,(E1M1AimTraversalReturn.layout s).2.1,BitVec.add_assoc]; rfl
  simp [result,OriginalAimQuery.returned,OriginalAimQuery.pop,put,write,stack,BitVec.add_assoc]

/-- Restore the aim caller's saved values from pre-return memory. The old stack
frame must be disjoint from the final traversal-cursor store. -/
theorem saved_caller (s : X86Control.State)
    (safe : ∀ off∈[(96#32),100,104,108,112], Apart (s.core.regs 4+off) 0x2c028) :
    (result s).pc=(load32 s.core.memory (s.core.regs 4+112)).toNat ∧
    (result s).core.regs 5=load32 s.core.memory (s.core.regs 4+96) ∧
    (result s).core.regs 7=load32 s.core.memory (s.core.regs 4+100) ∧
    (result s).core.regs 6=load32 s.core.memory (s.core.regs 4+104) ∧
    (result s).core.regs 1=load32 s.core.memory (s.core.regs 4+108) := by
  have keep (off : Word) (member : off∈[(96#32),100,104,108,112]) :
      load32 (result s).core.memory (s.core.regs 4+off)=load32 s.core.memory (s.core.regs 4+off) := by
    rw [memory]; exact load_store_apart _ _ _ _ (safe off member)
  obtain ⟨sp,pc,bp,di,si,cx⟩ := layout s
  exact ⟨pc.trans (congrArg BitVec.toNat (keep _ (by simp))),
    bp.trans (keep _ (by simp)),di.trans (keep _ (by simp)),si.trans (keep _ (by simp)),cx.trans (keep _ (by simp))⟩

/-- Append the entire return chain to any established ordered-loop execution.
Stack validity is still required at that prefix's endpoint. -/
theorem append (start finish : X86Control.State) (steps : Nat)
    (run : X86CodeMemory.Prefix FloorCaller.cm E1M1AimActorSelect.program [] steps start finish)
    (exit : finish.pc=0x2c887 ∨ finish.pc=0x2c88c)
    (safe20 : Apart (finish.core.regs 4+20) 0x2c028)
    (address20 : load32 finish.core.memory (finish.core.regs 4+20)=0x2cb0b)
    (safe84 : Apart (finish.core.regs 4+84) 0x2c028)
    (address84 : load32 finish.core.memory (finish.core.regs 4+84)=0x2bbff) :
    ∃ n≤steps+21, X86ReturnCleanup.Prefix FloorCaller.cm program [] n start (result finish) := by
  obtain ⟨n,bound,tail⟩ := execution finish exit safe20 address20 safe84 address84
  have old := (run.transfer E1M1AimTraversalReturn.program [] E1M1AimTraversalReturn.contains_loop (by simp)).transfer
    legacy [] contains_traversal (by simp)
  exact ⟨steps+n,by omega,((X86ReturnCleanup.lift old).transfer program contains_legacy).trans tail⟩
end Doom.Proofs.E1M1AimCompletedReturn
