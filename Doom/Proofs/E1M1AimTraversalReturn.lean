import Doom.Proofs.OriginalTraversalReturn
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1AimTraversalReturn
open Verification X86 X86Memory X86Control BlockSummary Collision
open OriginalTraversalReturn (returned cleaned stored)
attribute [local irreducible] load32 store32

def program : X86Routine.Program := fun pc =>
  match OriginalTraversalReturn.program pc with
  | some op => some op
  | none => E1M1AimActorSelect.program pc

theorem contains_return (pc : Nat) (h : OriginalTraversalReturn.program pc≠none) :
    program pc=OriginalTraversalReturn.program pc := by
  unfold program; cases eq : OriginalTraversalReturn.program pc <;> simp_all

theorem contains_loop (pc : Nat) (h : E1M1AimActorSelect.program pc≠none) :
    program pc=E1M1AimActorSelect.program pc := by
  have absent : OriginalTraversalReturn.program pc=none := by
    by_cases first : 0x2c887≤pc ∧ pc<0x2c89a
    · have all : ∀ i : Fin 19, E1M1AimActorSelect.program (0x2c887+i.val)=none := by decide
      have eq : 0x2c887+(pc-0x2c887)=pc := by omega
      exact False.elim (h (by simpa only [eq] using all ⟨pc-0x2c887,by omega⟩))
    · by_cases second : 0x2cb0b≤pc ∧ pc<0x2cb11
      · have all : ∀ i : Fin 6, E1M1AimActorSelect.program (0x2cb0b+i.val)=none := by decide
        have eq : 0x2cb0b+(pc-0x2cb0b)=pc := by omega
        exact False.elim (h (by simpa only [eq] using all ⟨pc-0x2cb0b,by omega⟩))
      · simp [OriginalTraversalReturn.program,OriginalTraversalReturn.bytesProgram,first,second]
  simp [program,absent]

def input (s : X86Control.State) : X86Memory.State :=
  if s.pc=0x2c887 then put s.core 0 1 else s.core
def result (s : X86Control.State) := cleaned (returned (input s)).core

/-- The final cursor store is the only memory write in this return segment. -/
theorem memory (s : X86Control.State) :
    (result s).core.memory=store32 s.core.memory 0x2c028 (s.core.regs 1) := by
  simp [result,cleaned,returned,OriginalTraversalReturn.restored,stored,input,
    OriginalAimQuery.pop,put,write]; split <;> simp [put,write]

theorem word (s : X86Control.State) (a : Word) (safe : Apart a 0x2c028) :
    load32 (result s).core.memory a=load32 s.core.memory a := by
  rw [memory]; exact load_store_apart _ _ _ _ safe

/-- The caller's actual return-address word is needed. This is an explicit
stack-layout premise at loop exit, not yet an invariant derived from entry. -/
theorem execution (s : X86Control.State)
    (exit : s.pc=0x2c887 ∨ s.pc=0x2c88c)
    (safe : Apart (s.core.regs 4+20) 0x2c028)
    (address : load32 s.core.memory (s.core.regs 4+20)=0x2cb0b) :
    ∃ n≤12, X86CodeMemory.Prefix FloorCaller.cm program [] n s (result s) := by
  have frame : load32 (stored (input s)).memory ((input s).regs 4+20)=0x2cb0b := by
    have sp : (input s).regs 4=s.core.regs 4 := by simp [input,put,write]; split <;> rfl
    have mem : (input s).memory=s.core.memory := by simp [input,put]; split <;> rfl
    change load32 (store32 (input s).memory 0x2c028 ((input s).regs 1)) ((input s).regs 4+20)=_
    rw [sp,load_store_apart _ _ _ _ safe,mem,address]
  have pc : (returned (input s)).pc=0x2cb0b := by
    rw [(OriginalTraversalReturn.return_layout (input s)).2.2.2.1,frame]; rfl
  have tail := (X86CodeMemory.lift_success
    (OriginalTraversalReturn.cleanup_execution (returned (input s)).core (returned (input s)).flags)
    FloorCaller.cm).transfer program [] contains_return (by simp)
  have same : (returned (input s))=⟨(returned (input s)).core,(returned (input s)).flags,0x2cb0b⟩ := by
    rw [← pc]
  rw [← same] at tail
  rcases exit with exhausted|stopped
  · have head := (X86CodeMemory.lift_success
      (OriginalTraversalReturn.exhausted_execution s.core s.flags) FloorCaller.cm).transfer program [] contains_return (by simp)
    have sameS : s=⟨s.core,s.flags,0x2c887⟩ := by rw [← exhausted]
    have inp : input s=put s.core 0 1 := by simp [input,exhausted]
    rw [← inp,← sameS] at head
    exact ⟨12,by omega,E1M1PspriteStep.prefix_trans head tail⟩
  · have head := (X86CodeMemory.lift_success
      (OriginalTraversalReturn.stop_execution s.core s.flags) FloorCaller.cm).transfer program [] contains_return (by simp)
    have sameS : s=⟨s.core,s.flags,0x2c88c⟩ := by rw [← stopped]
    have inp : input s=s.core := by simp [input,stopped]
    rw [← inp] at head
    -- Rewrite only the start state: input is the same core on this branch.
    have head' : X86CodeMemory.Prefix FloorCaller.cm program [] 7 s (returned (input s)) := by
      simpa only [inp,← sameS] using head
    exact ⟨11,by omega,E1M1PspriteStep.prefix_trans head' tail⟩

/-- Preserve the ordered loop's exact aim-value selection through the cursor
write, real traversal RET, and parent cleanup. EAX still holds the traversal
boolean here; the aim-return expression is not confused with that boolean. -/
theorem chosen (initial : Array Intercept) (resolve : Intercept → Word)
    (s : X86Control.State) (answer : AimResult)
    (exit : E1M1AimHitMemory.Exit initial resolve s answer)
    (nonnull : ∀ j<initial.size, resolve initial[j]!≠0) :
    OriginalAimQuery.chosen (result s).core=answer.slope.raw.toBitVec := by
  have target := word s (0x2b9f8#32) (by unfold Apart; decide)
  have slope := word s (0x2b9b4#32) (by unfold Apart; decide)
  have prior := E1M1AimHitMemory.return_value initial resolve s answer exit nonnull
  change (if load32 (result s).core.memory (0x2b9f8#32)=0 then (0#32)
    else load32 (result s).core.memory (0x2b9b4#32))=_
  rw [target,slope]; exact prior

theorem layout (s : X86Control.State) :
    (result s).pc=0x2cb11 ∧ (result s).core.regs 4=s.core.regs 4+84 ∧
    (result s).core.regs 0=(if s.pc=0x2c887 then 1 else s.core.regs 0) ∧
    (result s).core.regs 5=load32 (result s).core.memory (s.core.regs 4+72) ∧
    (result s).core.regs 7=load32 (result s).core.memory (s.core.regs 4+76) ∧
    (result s).core.regs 6=load32 (result s).core.memory (s.core.regs 4+80) := by
  simp [result,cleaned,returned,OriginalTraversalReturn.restored,stored,input,
    OriginalAimQuery.pop,put,write,BitVec.add_assoc]
  split <;> simp [put,write,BitVec.add_assoc]

/-- The saved caller registers survive the final cursor write under explicit
byte-range separation, including unaligned or wrapping stack addresses. -/
theorem saved_registers (s : X86Control.State)
    (safe : ∀ off∈[(16#32),72,76,80], Apart (s.core.regs 4+off) 0x2c028) :
    (result s).core.regs 3=load32 s.core.memory (s.core.regs 4+16) ∧
    (result s).core.regs 5=load32 s.core.memory (s.core.regs 4+72) ∧
    (result s).core.regs 7=load32 s.core.memory (s.core.regs 4+76) ∧
    (result s).core.regs 6=load32 s.core.memory (s.core.regs 4+80) := by
  have ebx : (result s).core.regs 3=load32 (result s).core.memory (s.core.regs 4+16) := by
    simp [result,cleaned,returned,OriginalTraversalReturn.restored,stored,input,
      OriginalAimQuery.pop,put,write,BitVec.add_assoc]
    split <;> simp [put,write,BitVec.add_assoc]
  exact ⟨ebx.trans (word s _ (safe _ (by simp))),
    (layout s).2.2.2.1.trans (word s _ (safe _ (by simp))),
    (layout s).2.2.2.2.1.trans (word s _ (safe _ (by simp))),
    (layout s).2.2.2.2.2.trans (word s _ (safe _ (by simp)))⟩

/-- Establish the next RET 8's return-address load without pretending that the
current instruction interpreter supports RET 8 itself. -/
theorem caller_address (s : X86Control.State)
    (safe : Apart (s.core.regs 4+84) 0x2c028)
    (address : load32 s.core.memory (s.core.regs 4+84)=0x2bbff) :
    load32 (result s).core.memory ((result s).core.regs 4)=0x2bbff := by
  rw [(layout s).2.1,word s _ safe,address]

/-- Composition with an already proved loop prefix. Saved-stack validity is
required at its endpoint; this theorem does not discharge that obligation. -/
theorem append (start finish : X86Control.State) (steps : Nat)
    (run : X86CodeMemory.Prefix FloorCaller.cm E1M1AimActorSelect.program [] steps start finish)
    (exit : finish.pc=0x2c887 ∨ finish.pc=0x2c88c)
    (safe : Apart (finish.core.regs 4+20) 0x2c028)
    (address : load32 finish.core.memory (finish.core.regs 4+20)=0x2cb0b) :
    ∃ n≤steps+12, X86CodeMemory.Prefix FloorCaller.cm program [] n start (result finish) := by
  obtain ⟨n,bound,tail⟩ := execution finish exit safe address
  exact ⟨steps+n,by omega,E1M1PspriteStep.prefix_trans
    (run.transfer program [] contains_loop (by simp)) tail⟩
end Doom.Proofs.E1M1AimTraversalReturn
