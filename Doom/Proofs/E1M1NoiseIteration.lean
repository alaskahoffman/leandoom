import Doom.Proofs.E1M1NoiseOpening
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
namespace Doom.Proofs.E1M1NoiseIteration
open Verification X86 X86Memory X86Control
abbrev program := E1M1NoiseOpening.program

private theorem contains_traversal (pc : Nat) (h : NoiseTraversal.program pc≠none) : program pc=NoiseTraversal.program pc := by
  change E1M1NoiseOpening.program pc=NoiseTraversal.program pc
  have a := E1M1NoiseTraversal.contains_traversal pc h
  rw [E1M1NoiseOpening.contains_prior pc (by rw [a]; exact h),a]
private theorem path {stops n s t} (run : X86Routine.run NoiseTraversal.program stops n s=some t) :
    ∃ k, k≤n ∧ X86CodeMemory.Prefix FloorCaller.cm program [] k s t := by
  obtain ⟨k,hk,p,_⟩ := X86Routine.run_path run
  exact ⟨k,hk,(X86CodeMemory.lift_success p FloorCaller.cm).transfer program [] contains_traversal (by simp)⟩

theorem line_gate_pc (s : X86Memory.State) : (NoiseTraversal.lineGate s).pc=0x26fb4 ∨ (NoiseTraversal.lineGate s).pc=0x27006 := by
  simp only [NoiseTraversal.lineGate]; split <;> simp
private theorem opening_gate_pc (s : X86Memory.State) : (NoiseTraversal.openingGate s).pc=0x26fc4 ∨ (NoiseTraversal.openingGate s).pc=0x27006 := by
  simp only [NoiseTraversal.openingGate]; split <;> simp
private theorem neighbor_pc (s : X86Memory.State) : (E1M1NoiseOpening.neighbor s).pc=0x26fee := by
  simp only [E1M1NoiseOpening.neighbor]
  split <;> rfl
private theorem raw_block_pc (s : X86Memory.State) : (NoiseTraversal.blockResult s).pc=0x26f60 ∨ (NoiseTraversal.blockResult s).pc=0x27006 := by
  simp only [NoiseTraversal.blockResult]
  split
  · exact Or.inl rfl
  · split <;> simp [NoiseTraversal.recursiveCall]
private theorem line_result_pc (s : X86Memory.State) (f : Option Flags) :
    (E1M1NoiseOpening.lineResult s f).pc=0x26fee ∨ (E1M1NoiseOpening.lineResult s f).pc=0x27006 := by
  simp only [E1M1NoiseOpening.lineResult]
  split
  · exact Or.inl (neighbor_pc _)
  · rename_i h
    exact Or.inr ((opening_gate_pc _).resolve_left h)
theorem opening_block_pc (s : X86Memory.State) (f : Option Flags) :
    (E1M1NoiseOpening.blockResult s f).pc=0x26f60 ∨ (E1M1NoiseOpening.blockResult s f).pc=0x27006 := by
  simp only [E1M1NoiseOpening.blockResult]
  split
  · exact raw_block_pc _
  · rename_i h
    exact Or.inr ((line_result_pc s f).resolve_left h)

def dispatched (s : X86Memory.State) : X86Control.State :=
  let g := NoiseTraversal.lineGate s
  if g.pc=0x26fb4 then E1M1NoiseOpening.blockResult g.core g.flags else g

def resumed (s : X86Memory.State) : X86Control.State :=
  let d := dispatched s
  if d.pc=0x26f60 then E1M1NoiseTraversal.sectorReturn d.core else d

def result (s : X86Memory.State) := NoiseTraversal.advanced (resumed s).core

/-- These are conditions on computed results, not assumptions supplying callee
execution. Nonterminal recursive children are intentionally not covered yet. -/
structure Inputs (s : X86Memory.State) : Prop where
  opening : (NoiseTraversal.lineGate s).pc=0x26fb4 →
    (E1M1NoiseOpening.opened (NoiseTraversal.lineGate s).core (NoiseTraversal.lineGate s).flags).pc=0x26fbb
  terminal : (dispatched s).pc=0x26f60 → (E1M1NoiseAlert.sectorResult (dispatched s).core).pc=0x27011
  childReturn : (dispatched s).pc=0x26f60 → (E1M1NoiseTraversal.sectorReturn (dispatched s).core).pc=0x27006

theorem dispatched_pc (s : X86Memory.State) : (dispatched s).pc=0x26f60 ∨ (dispatched s).pc=0x27006 := by
  simp only [dispatched]
  split
  · exact opening_block_pc _ _
  · rename_i h
    exact Or.inr ((line_gate_pc s).resolve_left h)
theorem resumed_pc (s : X86Memory.State) (h : Inputs s) : (resumed s).pc=0x27006 := by
  simp only [resumed]
  split
  · rename_i call
    exact h.childReturn call
  · rename_i skip
    exact (dispatched_pc s).resolve_left skip
theorem result_pc (s : X86Memory.State) : (result s).pc=0x26fa8 ∨ (result s).pc=0x27011 := by
  simp only [result,NoiseTraversal.advanced]; split <;> simp

theorem dispatch_execution (s : X86Memory.State) (f : Option Flags) (h : Inputs s) :
    ∃ n, n≤59 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x26fa8⟩ (dispatched s) := by
  obtain ⟨n,hn,p⟩ := path (NoiseTraversal.line_execution s f)
  by_cases two : (NoiseTraversal.lineGate s).pc=0x26fb4
  · obtain ⟨m,hm,q⟩ := E1M1NoiseOpening.block_execution _ _ (h.opening two)
    have eq : NoiseTraversal.lineGate s=⟨(NoiseTraversal.lineGate s).core,(NoiseTraversal.lineGate s).flags,0x26fb4⟩ := by rw [←two]
    rw [←eq] at q
    exact ⟨n+m,by omega,by simpa only [dispatched,two,ite_true] using E1M1PspriteStep.prefix_trans p q⟩
  · exact ⟨n,by omega,by simpa only [dispatched,two,ite_false] using p⟩

theorem resume_execution (s : X86Memory.State) (h : Inputs s) :
    ∃ n, n≤31 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n (dispatched s) (resumed s) := by
  by_cases call : (dispatched s).pc=0x26f60
  · obtain ⟨n,hn,p⟩ := E1M1NoiseTraversal.terminal_sector_execution (dispatched s).core (dispatched s).flags (h.terminal call)
    have eq : dispatched s=⟨(dispatched s).core,(dispatched s).flags,0x26f60⟩ := by rw [←call]
    rw [←eq] at p
    exact ⟨n,hn,by simpa only [resumed,call,ite_true] using p.transfer program [] E1M1NoiseOpening.contains_prior (by simp)⟩
  · exact ⟨0,by omega,by simpa only [resumed,call,ite_false] using X86CodeMemory.Prefix.nil (cm := FloorCaller.cm) (program := program) (exits := []) (dispatched s)⟩

/-- One complete line iteration, including actual leaf/pruned child execution,
return and parent advancement. No recursive CALL is replaced by a stub. -/
theorem iteration_execution (s : X86Memory.State) (f : Option Flags) (h : Inputs s) :
    ∃ n, n≤95 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x26fa8⟩ (result s) := by
  obtain ⟨a,ha,p⟩ := dispatch_execution s f h
  obtain ⟨b,hb,q⟩ := resume_execution s h
  obtain ⟨c,hc,r⟩ := path (NoiseTraversal.advance_execution (resumed s).core (resumed s).flags)
  have eq : resumed s=⟨(resumed s).core,(resumed s).flags,0x27006⟩ := by rw [←resumed_pc s h]
  rw [←eq] at r
  exact ⟨a+b+c,by omega,E1M1PspriteStep.prefix_trans (E1M1PspriteStep.prefix_trans p q) r⟩

/-- Bounded repetition stops as soon as the original loop reaches its epilogue.
Fuel exhaustion is an observed prefix, not a claim that traversal finished. -/
def loop : Nat → X86Control.State → X86Control.State
  | 0,s => s
  | k+1,s => let t := result s.core; if t.pc=0x26fa8 then loop k t else t
def LoopInputs : Nat → X86Control.State → Prop
  | 0,_ => True
  | k+1,s => s.pc=0x26fa8 ∧ Inputs s.core ∧
    ((result s.core).pc=0x26fa8 → LoopInputs k (result s.core))

theorem loop_execution (k : Nat) (s : X86Control.State) (h : LoopInputs k s) :
    ∃ n, n≤95*k ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n s (loop k s) := by
  induction k generalizing s with
  | zero => exact ⟨0,by simp,X86CodeMemory.Prefix.nil _⟩
  | succ k ih =>
    obtain ⟨pc,inputs,rest⟩ := h
    obtain ⟨n,hn,p⟩ := iteration_execution s.core s.flags inputs
    have eq : s=⟨s.core,s.flags,0x26fa8⟩ := by rw [←pc]
    rw [←eq] at p
    by_cases more : (result s.core).pc=0x26fa8
    · obtain ⟨m,hm,q⟩ := ih (result s.core) (rest more)
      exact ⟨n+m,by omega,by simpa only [loop,more,ite_true] using E1M1PspriteStep.prefix_trans p q⟩
    · exact ⟨n,by omega,by simpa only [loop,more,ite_false] using p⟩

/-- Frame equality is explicit until separation/reachability discharges it.
This establishes the progress component of the eventual traversal invariant. -/
theorem progress (s : X86Memory.State)
    (index : (resumed s).core.regs 6=s.regs 6)
    (offset : (resumed s).core.regs 5=s.regs 5) :
    (result s).core.regs 6=s.regs 6+1 ∧ (result s).core.regs 5=s.regs 5+4 := by
  simp [result,NoiseTraversal.advanced,put,write,index,offset]

def finished (k : Nat) (s : X86Control.State) := NoiseTraversal.returned (loop k s).core

theorem loop_return_execution (k : Nat) (s : X86Control.State) (h : LoopInputs k s)
    (done : (loop k s).pc=0x27011) :
    ∃ n, n≤95*k+7 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n s (finished k s) := by
  obtain ⟨n,hn,p⟩ := loop_execution k s h
  have q := (X86CodeMemory.lift_success (NoiseTraversal.return_execution (loop k s).core (loop k s).flags) FloorCaller.cm).transfer program [] contains_traversal (by simp)
  have eq : loop k s=⟨(loop k s).core,(loop k s).flags,0x27011⟩ := by rw [←done]
  rw [←eq] at q
  exact ⟨n+7,by omega,E1M1PspriteStep.prefix_trans p q⟩

def started (s : X86Memory.State) := NoiseTraversal.initialized (E1M1NoiseAlert.sectorResult s).core
def sectorResult (k : Nat) (s : X86Memory.State) := finished k (started s)

/-- A nonempty sector's full call: prologue, stamp/cost updates, initialization,
checked finite line loop, stack restoration and actual RET. -/
theorem sector_execution (k : Nat) (s : X86Memory.State) (f : Option Flags)
    (nonempty : (E1M1NoiseAlert.sectorResult s).pc=0x26fa6)
    (inputs : LoopInputs k (started s)) (done : (loop k (started s)).pc=0x27011) :
    ∃ n, n≤95*k+32 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x26f60⟩ (sectorResult k s) := by
  obtain ⟨n,hn,p⟩ := E1M1NoiseAlert.sector_execution s f
  have p := (p.transfer E1M1NoiseTraversal.program [] E1M1NoiseTraversal.contains_prior (by simp)).transfer program [] E1M1NoiseOpening.contains_prior (by simp)
  have q := (X86CodeMemory.lift_success (NoiseTraversal.initialize_execution (E1M1NoiseAlert.sectorResult s).core (E1M1NoiseAlert.sectorResult s).flags) FloorCaller.cm).transfer program [] contains_traversal (by simp)
  have eq : E1M1NoiseAlert.sectorResult s=⟨(E1M1NoiseAlert.sectorResult s).core,(E1M1NoiseAlert.sectorResult s).flags,0x26fa6⟩ := by rw [←nonempty]
  rw [←eq] at q
  obtain ⟨m,hm,r⟩ := loop_return_execution k (started s) inputs done
  exact ⟨n+1+m,by omega,E1M1PspriteStep.prefix_trans (E1M1PspriteStep.prefix_trans p q) r⟩
end Doom.Proofs.E1M1NoiseIteration
