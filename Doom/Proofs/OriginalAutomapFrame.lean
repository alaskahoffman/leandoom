import Doom.Proofs.OriginalAutomapStop
import Doom.Proofs.OriginalDeathChoice
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
namespace Doom.Proofs.AutomapStop
open Verification X86 X86Memory X86Control BlockSummary

theorem frame_append {a b c : Memory} {xs ys : List Word}
    (first : PlayerHeight.Frame a b xs) (last : PlayerHeight.Frame b c ys) :
    PlayerHeight.Frame a c (xs++ys) := by
  intro p safe
  rw [last p (fun q hq => safe q (List.mem_append.mpr (Or.inr hq)))]
  exact first p (fun q hq => safe q (List.mem_append.mpr (Or.inl hq)))

def iterationWrites (s : X86Memory.State) := [s.regs 4-(4#32),s.regs 4-(8#32),digit s-(16#32)]
theorem iteration_frame (s : X86Memory.State) :
    PlayerHeight.Frame s.memory (iteration s).memory (iterationWrites s) := by
  intro a safe
  change load32 (store32 (store32 (store32 s.memory (s.regs 4-4) 0x24e74)
    ((s.regs 4-4)-4) (s.regs 3+4)) (digit s-16) 101) a=load32 s.memory a
  rw [load_store_apart _ _ _ _ (safe _ (by simp [iterationWrites]))]
  rw [load_store_apart _ _ _ _ (safe _ (by simp [iterationWrites,BitVec.sub_sub]))]
  exact load_store_apart _ _ _ _ (safe _ (by simp [iterationWrites]))

def loopWrites (s : X86Memory.State) : Nat → List Word
  | 0 => []
  | n+1 => loopWrites s n ++ iterationWrites (loopState s n)
theorem loop_frame (s : X86Memory.State) (n : Nat) :
    PlayerHeight.Frame s.memory (loopState s n).memory (loopWrites s n) := by
  induction n with
  | zero => intro _ _; rfl
  | succ n ih => exact frame_append ih (iteration_frame (loopState s n))

def unloadWrites (s : X86Memory.State) := [s.regs 4-(4#32),s.regs 4-(8#32)] ++ loopWrites (unloadStart s) 10
theorem unload_frame (s : X86Memory.State) :
    PlayerHeight.Frame s.memory (unloadResult s).core.memory (unloadWrites s) := by
  apply frame_append (b := unloadSaved s) ?_ (loop_frame (unloadStart s) 10)
  intro a safe
  unfold unloadSaved
  rw [load_store_apart _ _ _ _ (safe _ (by simp))]
  exact load_store_apart _ _ _ _ (safe _ (by simp))

def responderWrites (s : X86Memory.State) :=
  [s.regs 4-(4#32),s.regs 4-(8#32),s.regs 4-(12#32),s.regs 4-(16#32),s.regs 4-(20#32),0x75434]
theorem responder_frame (s : X86Memory.State) :
    PlayerHeight.Frame s.memory (responderResult s).core.memory (responderWrites s) := by
  intro a safe
  change load32 (responderMemory s) a=load32 s.memory a
  unfold responderMemory responderSaved
  repeat rw [load_store_apart _ _ _ _ (safe _ (by simp [responderWrites]))]

/-- A conservative ordered list, including scratch writes and repeated slots. -/
def stopWrites (s : X86Memory.State) :=
  [s.regs 4-(4#32),s.regs 4-(8#32),s.regs 4-(12#32)] ++
  unloadWrites (stopUnload s) ++ [0x12c5c,s.regs 4-(12#32)] ++
  responderWrites (stopResponder s) ++ [0x12c94]

theorem stopUnload_frame (s : X86Memory.State) :
    PlayerHeight.Frame s.memory (stopUnload s).memory
      [s.regs 4-(4#32),s.regs 4-(8#32),s.regs 4-(12#32)] := by
  intro a safe
  change load32 (store32 (store32 (store32 s.memory (s.regs 4-4) (s.regs 3))
    ((s.regs 4-4)-4) (s.regs 2)) (((s.regs 4-4)-4)-4) 0x24f97) a=load32 s.memory a
  repeat rw [load_store_apart _ _ _ _ (safe _ (by simp [BitVec.sub_sub]))]

theorem stopResponder_sp (s : X86Memory.State) :
    (unloadResult (stopUnload s)).core.regs 4-(4#32)=s.regs 4-(12#32) := by
  simp [unloadResult,stopUnload,X86Routine.pushWord,write,BitVec.sub_eq_add_neg,BitVec.add_assoc]

theorem eventCall_frame (u : X86Memory.State) :
    PlayerHeight.Frame u.memory
      (X86Routine.pushWord ⟨write (write (write u.regs 0 0x12c98) 2 0) 3 1,
        store32 u.memory (0x12c5c#32) 0⟩ 0x24fae).memory [0x12c5c,u.regs 4-(4#32)] := by
  intro a safe
  change load32 (store32 (store32 u.memory (0x12c5c#32) 0) (u.regs 4-4) 0x24fae) a=load32 u.memory a
  rw [load_store_apart _ _ _ _ (safe _ (by simp))]
  exact load_store_apart _ _ _ _ (safe _ (by simp))

theorem stopResponder_frame (s : X86Memory.State) :
    PlayerHeight.Frame (unloadResult (stopUnload s)).core.memory (stopResponder s).memory
      [0x12c5c,s.regs 4-(12#32)] := by
  have h := eventCall_frame (unloadResult (stopUnload s)).core
  rw [stopResponder_sp] at h
  exact h

theorem stopLast_frame (s : X86Memory.State) :
    PlayerHeight.Frame (responderResult (stopResponder s)).core.memory (stopResult s).core.memory [0x12c94] := by
  intro a safe
  exact load_store_apart _ _ _ _ (safe _ (by simp))

theorem stop_frame (s : X86Memory.State) :
    PlayerHeight.Frame s.memory (stopResult s).core.memory (stopWrites s) :=
  frame_append (frame_append (frame_append (frame_append (stopUnload_frame s)
    (unload_frame (stopUnload s))) (stopResponder_frame s))
    (responder_frame (stopResponder s))) (stopLast_frame s)

theorem stop_registers (s : X86Memory.State) :
    (stopResult s).core.regs 3=s.regs 3 ∧ (stopResult s).core.regs 4=s.regs 4+4 := by
  simp [stopResult,write]

theorem stop_flags (s : X86Memory.State)
    (safe : ∀ a, a ∈ [(stopResponder s).regs 4-(4#32),(stopResponder s).regs 4-(8#32),
      (stopResponder s).regs 4-(12#32),(stopResponder s).regs 4-(16#32),
      (stopResponder s).regs 4-(20#32),(stopResponder s).regs 4] → Apart (0x12c5c#32) a) :
    load32 (stopResult s).core.memory (0x12c5c#32)=0 ∧
    load32 (stopResult s).core.memory (0x12c94#32)=1 ∧
    load32 (stopResult s).core.memory (0x75434#32)=1 := by
  have distinct (a b : Word) (h : (a,b) ∈ [(0x12c5c,0x12c94),(0x12c5c,0x75434),(0x75434,0x12c94)]) : Apart a b := by
    simp only [List.mem_cons,List.mem_singleton,Prod.mk.injEq,List.not_mem_nil,or_false] at h
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> unfold Apart <;> decide
  change load32 (stopMemory s) _=0 ∧ load32 (stopMemory s) _=1 ∧ load32 (stopMemory s) _=1
  refine ⟨?_,load_store _ _ _,?_⟩
  · unfold stopMemory responderMemory responderSaved
    rw [load_store_apart _ _ _ _ (distinct _ _ (by simp)),load_store_apart _ _ _ _ (distinct _ _ (by simp))]
    repeat rw [load_store_apart _ _ _ _ (safe _ (by simp))]
    change load32 (store32 (store32 (unloadResult (stopUnload s)).core.memory (0x12c5c#32) 0)
      ((stopResponder s).regs 4) 0x24fae) (0x12c5c#32)=0
    rw [load_store_apart _ _ _ _ (safe _ (by simp)),load_store]
  · unfold stopMemory
    rw [load_store_apart _ _ _ _ (distinct _ _ (by simp))]
    exact load_store _ _ _

end Doom.Proofs.AutomapStop
