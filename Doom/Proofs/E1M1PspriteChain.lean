import Doom.Proofs.E1M1PspriteSetter
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace Doom.Proofs.E1M1PspriteChain
open Verification X86 X86Memory X86Control BlockSummary
abbrev program := E1M1PspriteSetter.program

private theorem lift {n s t} (p : X86Routine.Prefix PspriteSetter.program [] n s t) :
    X86CodeMemory.Prefix FloorCaller.cm program [] n s t :=
  (X86CodeMemory.lift_success p FloorCaller.cm).transfer program [] E1M1PspriteSetter.contains_setter (by simp)
private theorem path {stops n s t}
    (run : X86Routine.run PspriteSetter.program stops n s=some t) :
    ∃ k, k ≤ n ∧ X86CodeMemory.Prefix FloorCaller.cm program [] k s t := by
  obtain ⟨k,hk,p,_⟩ := X86Routine.run_path run
  exact ⟨k,hk,lift (p.transfer PspriteSetter.program [] (by intros; rfl) (by simp))⟩

/-- Check the callback word itself, not the dispatch PC: an arbitrary callback
could coincidentally point at the no-action continuation address. -/
def NoAction (s : X86Memory.State) : Prop :=
  let t := E1M1PspriteSetter.positioned s
  load32 t.core.memory (t.core.regs 1+(12#32))=(0#32)
instance (s : X86Memory.State) : Decidable (NoAction s) := inferInstanceAs (Decidable (_ = _))

def continued (s : X86Memory.State) : X86Control.State :=
  PspriteSetter.next (PspriteSetter.successor (E1M1PspriteSetter.dispatched s).core none).core

/-- One entire action-free installation and successor decision, without
resetting memory or assuming a positive timer. -/
theorem iteration_execution (s : X86Memory.State) (f : Option Flags) (quiet : NoAction s) :
    ∃ n, n ≤ 28 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2d05e⟩ (continued s) := by
  obtain ⟨n,hn,a⟩ := E1M1PspriteSetter.dispatch_execution s f
  let t := E1M1PspriteSetter.dispatched s
  have gate : t=⟨t.core,t.flags,0x2d09a⟩ := by
    change load32 (E1M1PspriteSetter.positioned s).core.memory ((E1M1PspriteSetter.positioned s).core.regs 1+(12#32))=(0#32) at quiet
    dsimp only [t,E1M1PspriteSetter.dispatched]
    rw [if_pos quiet]
    simp only [PspriteSetter.actionGate,BitVec.ofNat_eq_ofNat,quiet,↓reduceIte]
  have b := lift (PspriteSetter.successor_execution t.core t.flags)
  rw [←gate] at b
  let u := PspriteSetter.successor t.core t.flags
  obtain ⟨m,hm,c⟩ := path (PspriteSetter.next_execution u.core u.flags)
  have e : u=⟨u.core,u.flags,0x2d0a2⟩ := rfl
  rw [←e] at c
  exact ⟨n+3+m,by omega,E1M1PspriteStep.prefix_trans (E1M1PspriteStep.prefix_trans a b) c⟩

/-- Fuel counts state installations/terminal branches, not machine instructions.
Exhaustion, an unsupported PC, or any callback is a failure, never a return. -/
def chain : Nat → X86Control.State → Option X86Control.State
  | 0,_ => none
  | fuel+1,s =>
    if s.pc=0x2d055 then some (PspriteSetter.returned (PspriteSetter.cleared s.core) s.flags)
    else if s.pc=0x2d0ac then some (PspriteSetter.returned s.core s.flags)
    else if s.pc=0x2d05e ∧ NoAction s.core then chain fuel (continued s.core)
    else none

theorem chain_execution (fuel : Nat) (s t : X86Control.State) (ok : chain fuel s=some t) :
    ∃ n, n ≤ 28*fuel+4 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n s t := by
  induction fuel generalizing s with
  | zero => simp [chain] at ok
  | succ fuel ih =>
    simp only [chain] at ok
    split at ok
    · rename_i pc
      have e : s=⟨s.core,s.flags,0x2d055⟩ := by rw [←pc]
      have out := Option.some.inj ok
      rw [←out,e]
      exact ⟨4,by omega,lift (PspriteSetter.clear_execution _ _)⟩
    · split at ok
      · rename_i pc
        have e : s=⟨s.core,s.flags,0x2d0ac⟩ := by rw [←pc]
        have out := Option.some.inj ok
        rw [←out,e]
        exact ⟨3,by omega,lift (PspriteSetter.return_execution _ _)⟩
      · split at ok
        · rename_i proceed
          obtain ⟨n,hn,a⟩ := iteration_execution s.core s.flags proceed.2
          have e : s=⟨s.core,s.flags,0x2d05e⟩ := by rw [←proceed.1]
          rw [←e] at a
          obtain ⟨m,hm,b⟩ := ih (continued s.core) ok
          exact ⟨n+m,by omega,E1M1PspriteStep.prefix_trans a b⟩
        · cases ok

/-- Additional fuel preserves any successful result. No bound is asserted for
cycles or for chains whose next action has not been proved. -/
theorem chain_mono (fuel extra : Nat) (s t : X86Control.State) (ok : chain fuel s=some t) :
    chain (fuel+extra) s=some t := by
  induction fuel generalizing s with
  | zero => simp [chain] at ok
  | succ fuel ih =>
    rw [Nat.succ_add]
    simp only [chain] at ok ⊢
    split at ok <;> simp_all only [↓reduceIte]
    split at ok <;> simp_all only [↓reduceIte]
    split at ok
    · rename_i proceed
      rw [if_pos proceed]
      exact ih _ ok
    · rename_i stop
      simp [stop] at ok

def complete (fuel : Nat) (s : X86Memory.State) := chain fuel (PspriteSetter.entered s)

theorem complete_execution (fuel : Nat) (s : X86Memory.State) (f : Option Flags)
    (t : X86Control.State) (ok : complete fuel s=some t) :
    ∃ n, n ≤ 28*fuel+13 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2d040⟩ t := by
  obtain ⟨n,hn,a⟩ := path (PspriteSetter.entry_execution s f)
  obtain ⟨m,hm,b⟩ := chain_execution fuel (PspriteSetter.entered s) t ok
  exact ⟨n+m,by omega,E1M1PspriteStep.prefix_trans a b⟩

def slot (fuel : Nat) (s : X86Memory.State) : Option X86Control.State :=
  let t := PspriteStep.result s
  if t.pc=0x2d040 then complete fuel t.core else some t

theorem slot_execution (fuel : Nat) (s : X86Memory.State) (f : Option Flags)
    (t : X86Control.State) (ok : slot fuel s=some t) :
    ∃ n, n ≤ 28*fuel+28 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2dc6f⟩ t := by
  obtain ⟨n,hn,a,_⟩ := X86Routine.run_path (PspriteStep.slot_execution s f)
  have a := (X86CodeMemory.lift_success a FloorCaller.cm).transfer program [] E1M1PspriteLoop.contains_slot (by simp)
  simp only [slot] at ok
  split at ok
  · rename_i expires
    obtain ⟨m,hm,b⟩ := complete_execution fuel (PspriteStep.result s).core (PspriteStep.result s).flags t ok
    have e : PspriteStep.result s=⟨(PspriteStep.result s).core,(PspriteStep.result s).flags,0x2d040⟩ := by rw [←expires]
    rw [←e] at b
    exact ⟨n+m,by omega,E1M1PspriteStep.prefix_trans a b⟩
  · have e := Option.some.inj ok
    rw [←e]
    exact ⟨n,by omega,a⟩


private theorem loop_path {stops n s t}
    (run : X86Routine.run PspriteLoop.program stops n s=some t) :
    ∃ k, k ≤ n ∧ X86CodeMemory.Prefix FloorCaller.cm program [] k s t := by
  obtain ⟨k,hk,p,_⟩ := X86Routine.run_path run
  exact ⟨k,hk,(X86CodeMemory.lift_success p FloorCaller.cm).transfer program [] E1M1PspriteLoop.contains_tail (by simp)⟩

def finished (s : X86Control.State) :=
  let t := PspriteLoop.advanced s.core
  PspriteLoop.returned (PspriteLoop.copied t.core) t.flags

/-- After the flash slot actually completes, copy coordinates and return. -/
theorem finish_execution (s : X86Control.State) (pc : s.pc=0x2dc95)
    (flashIndex : s.core.regs 6=(1#32)) :
    ∃ n, n ≤ 14 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n s (finished s) := by
  obtain ⟨n,hn,a⟩ := loop_path (PspriteLoop.advance_execution s.core s.flags)
  have e : s=⟨s.core,s.flags,0x2dc95⟩ := by rw [←pc]
  rw [←e] at a
  let t := PspriteLoop.advanced s.core
  have e2 : t=⟨t.core,t.flags,0x2dc9e⟩ := by
    change PspriteLoop.advanced s.core=_
    have h : (PspriteLoop.advanced s.core).pc=0x2dc9e := by simp [PspriteLoop.advanced,flashIndex]
    rw [←h]
  obtain ⟨m,hm,b⟩ := loop_path (PspriteLoop.copy_execution t.core t.flags)
  rw [←e2] at b
  have c := (X86CodeMemory.lift_success (PspriteLoop.return_execution (PspriteLoop.copied t.core) t.flags) FloorCaller.cm).transfer
    program [] E1M1PspriteLoop.contains_tail (by simp)
  exact ⟨n+m+6,by omega,E1M1PspriteStep.prefix_trans (E1M1PspriteStep.prefix_trans a b) c⟩

/-- Includes action-free flash transitions, unlike the earlier suffix restricted
to non-expiring timers. The actual return PC and restored slot index are checked. -/
def suffix (fuel : Nat) (s : X86Control.State) : Option X86Control.State := do
  let t ← slot fuel (PspriteLoop.advanced s.core).core
  if t.pc=0x2dc95 ∧ t.core.regs 6=(1#32) then some (finished t) else none

theorem suffix_execution (fuel : Nat) (s t : X86Control.State)
    (pc : s.pc=0x2dc95) (weaponIndex : s.core.regs 6=(0#32))
    (ok : suffix fuel s=some t) :
    ∃ n, n ≤ 28*fuel+46 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n s t := by
  obtain ⟨n,hn,a⟩ := loop_path (PspriteLoop.advance_execution s.core s.flags)
  have e : s=⟨s.core,s.flags,0x2dc95⟩ := by rw [←pc]
  rw [←e] at a
  let u := PspriteLoop.advanced s.core
  have e2 : u=⟨u.core,u.flags,0x2dc6f⟩ := by
    change PspriteLoop.advanced s.core=_
    have h : (PspriteLoop.advanced s.core).pc=0x2dc6f := by simp [PspriteLoop.advanced,weaponIndex]
    rw [←h]
  cases result : slot fuel u.core with
  | none => simp [suffix,show slot fuel (PspriteLoop.advanced s.core).core=none from result] at ok
  | some v =>
    obtain ⟨m,hm,b⟩ := slot_execution fuel u.core u.flags v result
    rw [←e2] at b
    simp only [suffix,show slot fuel (PspriteLoop.advanced s.core).core=some v from result,Bind.bind,Option.bind] at ok
    split at ok
    · rename_i good
      obtain ⟨j,hj,c⟩ := finish_execution v good.1 good.2
      have out := Option.some.inj ok
      rw [out] at c
      exact ⟨n+m+j,by omega,E1M1PspriteStep.prefix_trans (E1M1PspriteStep.prefix_trans a b) c⟩
    · cases ok

end Doom.Proofs.E1M1PspriteChain
