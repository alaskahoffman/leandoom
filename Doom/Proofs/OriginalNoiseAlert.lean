import Doom.Proofs.OriginalNoiseEntry
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.NoiseAlert
open Verification X86 X86Memory X86Control BlockSummary
private theorem prefix_trans {p stops n m s t u}
    (a : X86Routine.Prefix p stops n s t) (b : X86Routine.Prefix p stops m t u) :
    X86Routine.Prefix p stops (n+m) s u := by
  induction a with
  | nil => simpa using b
  | @step n s middle last op len active decoded executed rest ih =>
    simpa only [Nat.succ_add] using X86Routine.Prefix.step active decoded executed (ih b)

def saveThree (s : X86Memory.State) :=
  X86Routine.pushWord (X86Routine.pushWord (X86Routine.pushWord s (s.regs 3)) (s.regs 1)) (s.regs 6)
def saveTwo (s : X86Memory.State) :=
  X86Routine.pushWord (X86Routine.pushWord s (s.regs 7)) (s.regs 5)
def saved (s : X86Memory.State) := saveTwo (saveThree s)
def prepareTail (s : X86Memory.State) :=
  put (put (put (put (saveTwo s) 4 ((saveTwo s).regs 4-(4#32))) 3 (s.regs 0)) 1 (s.regs 2))
    2 (load32 (saveTwo s).memory 0x13580)
def prepared (s : X86Memory.State) := prepareTail (saveThree s)

private theorem save_three (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix listed [] 3 ⟨s,f,0x26f60⟩ ⟨saveThree s,f,0x26f63⟩ := by
  let a := X86Routine.pushWord s (s.regs 3)
  let b := X86Routine.pushWord a (s.regs 1)
  apply X86Routine.Prefix.step (middle := ⟨a,f,0x26f61⟩) (by simp) rfl rfl
  apply X86Routine.Prefix.step (middle := ⟨b,f,0x26f62⟩) (by simp) rfl rfl
  apply X86Routine.Prefix.step (middle := ⟨saveThree s,f,0x26f63⟩) (by simp) rfl rfl
  exact X86Routine.Prefix.nil _

private theorem prepare_tail (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix listed [] 6 ⟨s,f,0x26f63⟩ ⟨prepareTail s,none,0x26f72⟩ := by
  let a := X86Routine.pushWord s (s.regs 7)
  let b := saveTwo s
  let c := put b 4 (b.regs 4-(4#32))
  let d := put c 3 (s.regs 0)
  let e := put d 1 (s.regs 2)
  apply X86Routine.Prefix.step (middle := ⟨a,f,0x26f64⟩) (by simp) rfl rfl
  apply X86Routine.Prefix.step (middle := ⟨b,f,0x26f65⟩) (by simp) rfl rfl
  apply X86Routine.Prefix.step (middle := ⟨c,none,0x26f68⟩) (by simp) rfl (by
    simp [X86Routine.execute,c,BitVec.sub_eq_add_neg])
  apply X86Routine.Prefix.step (middle := ⟨d,none,0x26f6a⟩) (by simp) rfl rfl
  apply X86Routine.Prefix.step (middle := ⟨e,none,0x26f6c⟩) (by simp) rfl rfl
  apply X86Routine.Prefix.step (middle := ⟨prepareTail s,none,0x26f72⟩) (by simp) rfl rfl
  exact X86Routine.Prefix.nil _

theorem prepare_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 9 ⟨s,f,0x26f60⟩ ⟨prepared s,none,0x26f72⟩ :=
  (prefix_trans (save_three s f) (prepare_tail (saveThree s) f)).transfer program [] decoded (by simp)

def seen (s : X86Memory.State) := load32 s.memory (s.regs 0+(66#32))
def previousCost (s : X86Memory.State) := load32 s.memory (s.regs 3+(18#32))
def nextCost (s : X86Memory.State) := s.regs 1+(1#32)
def gate (s : X86Memory.State) : X86Control.State :=
  if s.regs 2≠seen s then ⟨s,some (compare32 (s.regs 2) (seen s)),0x26f83⟩
  else ⟨put s 0 (nextCost s),some (compare32 (nextCost s) (previousCost s)),
    if (previousCost s).toInt≤(nextCost s).toInt then 0x27011 else 0x26f83⟩

/-- Revisit pruning uses a signed comparison of the wrapping blocks+1 value. -/
@[local simp] private theorem step_26f72 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x26f83,0x27011] (n+1) ⟨s,f,0x26f72⟩ =
      (X86Routine.execute (.control (.cmpMemory 2 ⟨some 0,none,0,66⟩)) ⟨s,f,0x26f75⟩).bind (X86Routine.run listed [0x26f83,0x27011] n) := by rfl
@[local simp] private theorem step_26f75 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x26f83,0x27011] (n+1) ⟨s,f,0x26f75⟩ =
      (X86Routine.execute (.control (.jumpZero false 12)) ⟨s,f,0x26f77⟩).bind (X86Routine.run listed [0x26f83,0x27011] n) := by rfl
@[local simp] private theorem step_26f77 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x26f83,0x27011] (n+1) ⟨s,f,0x26f77⟩ =
      (X86Routine.execute (.control (.block (.legacy (.lea 0 1 1)))) ⟨s,f,0x26f7a⟩).bind (X86Routine.run listed [0x26f83,0x27011] n) := by rfl
@[local simp] private theorem step_26f7a (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x26f83,0x27011] (n+1) ⟨s,f,0x26f7a⟩ =
      (X86Routine.execute (.control (.cmpMemory 0 ⟨some 3,none,0,18⟩)) ⟨s,f,0x26f7d⟩).bind (X86Routine.run listed [0x26f83,0x27011] n) := by rfl
@[local simp] private theorem step_26f7d (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x26f83,0x27011] (n+1) ⟨s,f,0x26f7d⟩ =
      (X86Routine.execute (.jumpSigned 0 142) ⟨s,f,0x26f83⟩).bind (X86Routine.run listed [0x26f83,0x27011] n) := by rfl
@[local simp] private theorem stop_gate_execution_26f83 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x26f83,0x27011] n ⟨s,f,0x26f83⟩=some ⟨s,f,0x26f83⟩ := by cases n <;> rfl
@[local simp] private theorem stop_gate_execution_27011 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x26f83,0x27011] n ⟨s,f,0x27011⟩=some ⟨s,f,0x27011⟩ := by cases n <;> rfl

theorem gate_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x26f83,0x27011] 5 ⟨s,f,0x26f72⟩=some (gate s) := by
  have run : X86Routine.run listed [0x26f83,0x27011] 5 ⟨s,f,0x26f72⟩=some (gate s) := by
    by_cases old : s.regs 2=seen s
    all_goals
      by_cases cheaper : (previousCost s).toInt≤(nextCost s).toInt
      all_goals
        simp only [seen,nextCost,previousCost] at old cheaper
        simp [X86Routine.execute,X86Control.execute,
        X86Block.execute,X86Memory.execute,X86Block.Address.eval,blockPreservesFlags,
        gate,seen,nextCost,previousCost,cmp32_zero,PlayerHeight.cmp_ge_prop,put,write,old,cheaper,-BitVec.toInt_add]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

def markedMemory (s : X86Memory.State) :=
  store32 s.memory (s.regs 3+(66#32)) (load32 s.memory (0x13580#32))
def lines (s : X86Memory.State) := load32 (markedMemory s) (s.regs 3+(78#32))
def costMemory (s : X86Memory.State) := store32 (markedMemory s) (s.regs 3+(18#32)) (nextCost s)
def soundTarget (s : X86Memory.State) := load32 (costMemory s) (0x2b958#32)
def updated (s : X86Memory.State) : X86Control.State :=
  ⟨⟨write (write (write (write (write s.regs 0 (load32 s.memory (0x13580#32))) 0 (nextCost s)) 7 (lines s)) 0 (soundTarget s)) 6 (0#32),
    store32 (costMemory s) (s.regs 3+(22#32)) (soundTarget s)⟩,
    some (logical32 (lines s)),if (lines s).toInt≤0 then 0x27011 else 0x26fa6⟩

/-- The three actual sector writes and signed line-count branch. Stops before
line traversal or the return epilogue, rather than assuming either callee. -/
@[local simp] private theorem step_26f83 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x26fa6,0x27011] (n+1) ⟨s,f,0x26f83⟩ =
      (X86Routine.execute (.control (.block (.load 0 ⟨none,none,0,0x13580⟩))) ⟨s,f,0x26f88⟩).bind (X86Routine.run listed [0x26fa6,0x27011] n) := by rfl
@[local simp] private theorem step_26f88 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x26fa6,0x27011] (n+1) ⟨s,f,0x26f88⟩ =
      (X86Routine.execute (.control (.block (.store ⟨some 3,none,0,66⟩ 0))) ⟨s,f,0x26f8b⟩).bind (X86Routine.run listed [0x26fa6,0x27011] n) := by rfl
@[local simp] private theorem step_26f8b (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x26fa6,0x27011] (n+1) ⟨s,f,0x26f8b⟩ =
      (X86Routine.execute (.control (.block (.legacy (.lea 0 1 1)))) ⟨s,f,0x26f8e⟩).bind (X86Routine.run listed [0x26fa6,0x27011] n) := by rfl
@[local simp] private theorem step_26f8e (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x26fa6,0x27011] (n+1) ⟨s,f,0x26f8e⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 7 3 78)))) ⟨s,f,0x26f91⟩).bind (X86Routine.run listed [0x26fa6,0x27011] n) := by rfl
@[local simp] private theorem step_26f91 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x26fa6,0x27011] (n+1) ⟨s,f,0x26f91⟩ =
      (X86Routine.execute (.control (.block (.store ⟨some 3,none,0,18⟩ 0))) ⟨s,f,0x26f94⟩).bind (X86Routine.run listed [0x26fa6,0x27011] n) := by rfl
@[local simp] private theorem step_26f94 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x26fa6,0x27011] (n+1) ⟨s,f,0x26f94⟩ =
      (X86Routine.execute (.control (.block (.load 0 ⟨none,none,0,0x2b958⟩))) ⟨s,f,0x26f99⟩).bind (X86Routine.run listed [0x26fa6,0x27011] n) := by rfl
@[local simp] private theorem step_26f99 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x26fa6,0x27011] (n+1) ⟨s,f,0x26f99⟩ =
      (X86Routine.execute (.xorRegister 6 6) ⟨s,f,0x26f9b⟩).bind (X86Routine.run listed [0x26fa6,0x27011] n) := by rfl
@[local simp] private theorem step_26f9b (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x26fa6,0x27011] (n+1) ⟨s,f,0x26f9b⟩ =
      (X86Routine.execute (.control (.block (.store ⟨some 3,none,0,22⟩ 0))) ⟨s,f,0x26f9e⟩).bind (X86Routine.run listed [0x26fa6,0x27011] n) := by rfl
@[local simp] private theorem step_26f9e (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x26fa6,0x27011] (n+1) ⟨s,f,0x26f9e⟩ =
      (X86Routine.execute (.control (.testWord 7 7)) ⟨s,f,0x26fa0⟩).bind (X86Routine.run listed [0x26fa6,0x27011] n) := by rfl
@[local simp] private theorem step_26fa0 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x26fa6,0x27011] (n+1) ⟨s,f,0x26fa0⟩ =
      (X86Routine.execute (.jumpSigned 1 107) ⟨s,f,0x26fa6⟩).bind (X86Routine.run listed [0x26fa6,0x27011] n) := by rfl
@[local simp] private theorem stop_update_execution_26fa6 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x26fa6,0x27011] n ⟨s,f,0x26fa6⟩=some ⟨s,f,0x26fa6⟩ := by cases n <;> rfl
@[local simp] private theorem stop_update_execution_27011 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x26fa6,0x27011] n ⟨s,f,0x27011⟩=some ⟨s,f,0x27011⟩ := by cases n <;> rfl

theorem update_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x26fa6,0x27011] 10 ⟨s,f,0x26f83⟩=some (updated s) := by
  have run : X86Routine.run listed [0x26fa6,0x27011] 10 ⟨s,f,0x26f83⟩=some (updated s) := by
    by_cases empty : (lines s).toInt≤0
    all_goals
      simp only [lines,markedMemory] at empty
      simp [X86Routine.execute,X86Control.execute,
      X86Block.execute,X86Memory.execute,X86Block.Address.eval,blockPreservesFlags,
      updated,lines,soundTarget,costMemory,markedMemory,nextCost,PlayerHeight.logical_le,
      put,write,empty,-BitVec.toInt_add]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

theorem update_frame (s : X86Memory.State) :
    PlayerHeight.Frame s.memory (updated s).core.memory
      [s.regs 3+(66#32),s.regs 3+(18#32),s.regs 3+(22#32)] := by
  intro a safe
  change load32 (store32 (costMemory s) (s.regs 3+(22#32)) (soundTarget s)) a=_
  rw [load_store_apart _ _ _ _ (safe _ (by simp))]
  unfold costMemory
  rw [load_store_apart _ _ _ _ (safe _ (by simp))]
  exact load_store_apart _ _ _ _ (safe _ (by simp))

private theorem apart_translate (p a b : Word) (h : Apart a b) : Apart (p+a) (p+b) := by
  intro i j eq
  rw [BitVec.add_assoc,BitVec.add_assoc] at eq
  exact h i j ((BitVec.add_right_inj p).mp eq)

theorem updated_target (s : X86Memory.State) :
    load32 (updated s).core.memory (s.regs 3+(22#32))=soundTarget s := load_store _ _ _
theorem updated_cost (s : X86Memory.State) :
    load32 (updated s).core.memory (s.regs 3+(18#32))=nextCost s := by
  change load32 (store32 (costMemory s) (s.regs 3+(22#32)) (soundTarget s)) _=_
  rw [load_store_apart _ _ _ _ (apart_translate _ _ _ (by unfold Apart; decide))]
  exact load_store _ _ _
theorem updated_stamp (s : X86Memory.State) :
    load32 (updated s).core.memory (s.regs 3+(66#32))=load32 s.memory (0x13580#32) := by
  change load32 (store32 (costMemory s) (s.regs 3+(22#32)) (soundTarget s)) _=_
  rw [load_store_apart _ _ _ _ (apart_translate _ _ _ (by unfold Apart; decide))]
  unfold costMemory
  rw [load_store_apart _ _ _ _ (apart_translate _ _ _ (by unfold Apart; decide))]
  exact load_store _ _ _
end Doom.Proofs.NoiseAlert
