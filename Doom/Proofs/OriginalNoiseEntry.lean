import Doom.Proofs.OriginalNoiseCode
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.NoiseAlert
open Verification X86 X86Memory X86Control BlockSummary
def targetMemory (s : X86Memory.State) := store32 s.memory 0x2b958 (s.regs 0)
def subsector (s : X86Memory.State) := load32 (targetMemory s) (s.regs 2+(52#32))
def sector (s : X86Memory.State) := load32 (targetMemory s) (subsector s)
def count (s : X86Memory.State) := load32 (targetMemory s) 0x13580+(1#32)
def entryHead (s : X86Memory.State) :=
  put (put {s with memory := targetMemory s} 0 (subsector s)) 2 (load32 (targetMemory s) 0x13580)
def entryTail (s : X86Memory.State) : X86Control.State :=
  ⟨put { (put (put s 2 (s.regs 2+(1#32))) 0 (load32 s.memory (s.regs 0))) with
      memory := store32 s.memory 0x13580 (s.regs 2+(1#32)) } 2 0,
    some (logical32 0),0x26f60⟩
def result (s : X86Memory.State) := entryTail (entryHead s)

private theorem head_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix listed [0x26f60] 3 ⟨s,f,0x27020⟩ ⟨entryHead s,f,0x2702e⟩ := by
  let a : X86Memory.State := {s with memory := targetMemory s}
  let b := put a 0 (subsector s)
  apply X86Routine.Prefix.step (middle := ⟨a,f,0x27025⟩) (by simp) rfl rfl
  apply X86Routine.Prefix.step (middle := ⟨b,f,0x27028⟩) (by simp) rfl rfl
  apply X86Routine.Prefix.step (middle := ⟨entryHead s,f,0x2702e⟩) (by simp) rfl rfl
  exact X86Routine.Prefix.nil _

private theorem tail_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run listed [0x26f60] 5 ⟨s,f,0x2702e⟩=some (entryTail s) := by
  simp [X86Routine.run,listed,X86Routine.execute,X86Control.execute,X86Block.execute,
    X86Memory.execute,X86Block.Address.eval,blockPreservesFlags,put,write,entryTail,logical32]

/-- Eight actual instructions, including the wrapping traversal counter and
real tail jump. All loads observe preceding stores, even with aliasing. -/
theorem entry_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x26f60] 8 ⟨s,f,0x27020⟩=some (result s) := by
  have run := (head_execution s f).finish (tail_execution (entryHead s) f) 8 (by decide)
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]
  rfl

theorem result_target (s : X86Memory.State) : load32 (result s).core.memory 0x2b958=s.regs 0 := by
  change load32 (store32 (targetMemory s) 0x13580 (count s)) 0x2b958=_
  rw [load_store_apart _ _ _ _ (by unfold Apart; decide)]
  exact load_store _ _ _
theorem result_count (s : X86Memory.State) :
    load32 (result s).core.memory 0x13580=load32 s.memory 0x13580+(1#32) := by
  change load32 (store32 (targetMemory s) 0x13580 (count s)) 0x13580=_
  rw [load_store]
  unfold count targetMemory
  rw [load_store_apart _ _ _ _ (by unfold Apart; decide)]
theorem result_frame (s : X86Memory.State) :
    PlayerHeight.Frame s.memory (result s).core.memory [0x2b958,0x13580] := by
  intro a safe
  change load32 (store32 (targetMemory s) 0x13580 (count s)) a=_
  rw [load_store_apart _ _ _ _ (safe _ (by simp))]
  exact load_store_apart _ _ _ _ (safe _ (by simp))

end Doom.Proofs.NoiseAlert
