import Doom.Proofs.E1M1NoiseIteration
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
namespace Doom.Proofs.E1M1NoiseRecursive
open Verification X86 X86Memory X86Control
abbrev program := E1M1NoiseOpening.program
abbrev Runs (budget : Nat) (s t : X86Control.State) :=
  ∃ n, n≤budget ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n s t
private theorem trans {a b s t u} (p : Runs a s t) (q : Runs b t u) : Runs (a+b) s u := by
  obtain ⟨n,hn,p⟩ := p
  obtain ⟨m,hm,q⟩ := q
  exact ⟨n+m,by omega,E1M1PspriteStep.prefix_trans p q⟩
private theorem weaken {a b s t} (p : Runs a s t) (h : a≤b) : Runs b s t := by
  obtain ⟨n,hn,p⟩ := p
  exact ⟨n,by omega,p⟩
private theorem identity (s : X86Control.State) : Runs 0 s s := ⟨0,by omega,X86CodeMemory.Prefix.nil _⟩
private theorem contains_traversal (pc : Nat) (h : NoiseTraversal.program pc≠none) : program pc=NoiseTraversal.program pc := by
  change E1M1NoiseOpening.program pc=NoiseTraversal.program pc
  have a := E1M1NoiseTraversal.contains_traversal pc h
  rw [E1M1NoiseOpening.contains_prior pc (by rw [a]; exact h),a]
private theorem path {stops n s t} (run : X86Routine.run NoiseTraversal.program stops n s=some t) : Runs n s t := by
  obtain ⟨k,hk,p,_⟩ := X86Routine.run_path run
  exact ⟨k,hk,(X86CodeMemory.lift_success p FloorCaller.cm).transfer program [] contains_traversal (by simp)⟩
private theorem at_pc (s : X86Control.State) (pc : Nat) (h : s.pc=pc) : s=⟨s.core,s.flags,pc⟩ := by rw [←h]

def OpeningReturns (s : X86Memory.State) : Prop :=
  (NoiseTraversal.lineGate s).pc=0x26fb4 →
    (E1M1NoiseOpening.opened (NoiseTraversal.lineGate s).core (NoiseTraversal.lineGate s).flags).pc=0x26fbb
instance (s : X86Memory.State) : Decidable (OpeningReturns s) := by unfold OpeningReturns; infer_instance

/-- Only the opening return is needed to reach the child entry; no terminal-child
condition is needed or assumed here. -/
theorem dispatch_execution (s : X86Control.State) (pc : s.pc=0x26fa8) (h : OpeningReturns s.core) :
    Runs 59 s (E1M1NoiseIteration.dispatched s.core) := by
  obtain ⟨n,hn,p⟩ := path (NoiseTraversal.line_execution s.core s.flags)
  rw [←at_pc s _ pc] at p
  by_cases two : (NoiseTraversal.lineGate s.core).pc=0x26fb4
  · obtain ⟨m,hm,q⟩ := E1M1NoiseOpening.block_execution _ _ (h two)
    rw [←at_pc (NoiseTraversal.lineGate s.core) _ two] at q
    exact ⟨n+m,by omega,by simpa only [E1M1NoiseIteration.dispatched,two,ite_true] using E1M1PspriteStep.prefix_trans p q⟩
  · exact ⟨n,by omega,by simpa only [E1M1NoiseIteration.dispatched,two,ite_false] using p⟩

private theorem sector_prefix (s : X86Control.State) (pc : s.pc=0x26f60) :
    Runs 24 s (E1M1NoiseAlert.sectorResult s.core) := by
  obtain ⟨n,hn,p⟩ := E1M1NoiseAlert.sector_execution s.core s.flags
  rw [←at_pc s _ pc] at p
  exact ⟨n,hn,(p.transfer E1M1NoiseTraversal.program [] E1M1NoiseTraversal.contains_prior (by simp)).transfer program [] E1M1NoiseOpening.contains_prior (by simp)⟩
private theorem init_lines (s : X86Control.State) (pc : s.pc=0x26fa6) : Runs 1 s (NoiseTraversal.initialized s.core) := by
  have p := (X86CodeMemory.lift_success (NoiseTraversal.initialize_execution s.core s.flags) FloorCaller.cm).transfer program [] contains_traversal (by simp)
  rw [←at_pc s _ pc] at p
  exact ⟨1,by omega,p⟩
private theorem advance (s : X86Control.State) (pc : s.pc=0x27006) : Runs 5 s (NoiseTraversal.advanced s.core) := by
  have p := path (NoiseTraversal.advance_execution s.core s.flags)
  rw [←at_pc s _ pc] at p
  exact p
private theorem finish (s : X86Control.State) (pc : s.pc=0x27011) : Runs 7 s (NoiseTraversal.returned s.core) := by
  have p := (X86CodeMemory.lift_success (NoiseTraversal.return_execution s.core s.flags) FloorCaller.cm).transfer program [] contains_traversal (by simp)
  rw [←at_pc s _ pc] at p
  exact ⟨7,by omega,p⟩

inductive Phase where | sector | lines deriving DecidableEq

def Phase.pc : Phase → Nat | .sector => 0x26f60 | .lines => 0x26fa8

/-- Recursive summary of the original machine, not the live Lean worklist.
None means exhausted structural fuel or a failed actual-return/endpoint check.
A successful result always includes the current sector's real RET. -/
def eval : Nat → Phase → X86Control.State → Option X86Control.State
  | 0,_,_ => none
  | k+1,.sector,s =>
    let p := E1M1NoiseAlert.sectorResult s.core
    if p.pc=0x27011 then some (NoiseTraversal.returned p.core)
    else if p.pc=0x26fa6 then eval k .lines (NoiseTraversal.initialized p.core)
    else none
  | k+1,.lines,s => do
    if ¬OpeningReturns s.core then none else do
      let d := E1M1NoiseIteration.dispatched s.core
      let t ← if d.pc=0x26f60 then do
          let t ← eval k .sector d
          if t.pc=0x27006 then some t else none
        else if d.pc=0x27006 then some d else none
      let a := NoiseTraversal.advanced t.core
      if a.pc=0x26fa8 then eval k .lines a
      else if a.pc=0x27011 then some (NoiseTraversal.returned a.core) else none

/-- A conservative tree-shaped instruction bound, not a map-size termination
bound. The child and remaining parent lines can both use the smaller budget. -/
def bound : Nat → Nat | 0 => 0 | k+1 => 2*bound k+71

private theorem tail_execution (k : Nat) (s t : X86Control.State)
    (ih : ∀ phase s t, s.pc=phase.pc → eval k phase s=some t → Runs (bound k) s t)
    (pc : s.pc=0x27006)
    (h : (let a := NoiseTraversal.advanced s.core
      if a.pc=0x26fa8 then eval k .lines a
      else if a.pc=0x27011 then some (NoiseTraversal.returned a.core) else none)=some t) :
    Runs (5+bound k+7) s t := by
  have p := advance s pc
  dsimp only at h
  split at h
  · rename_i more
    exact weaken (trans p (ih .lines _ _ more h)) (by omega)
  · split at h
    · rename_i done
      have eq : NoiseTraversal.returned (NoiseTraversal.advanced s.core).core=t := Option.some.inj h
      rw [←eq]
      exact weaken (trans p (finish _ done)) (by omega)
    · contradiction

/-- Successful bounded recursive evaluation is execution of the pinned original
instructions, for any nesting depth admitted by fuel. No child transition axiom. -/
theorem execution (k : Nat) (phase : Phase) (s t : X86Control.State)
    (pc : s.pc=phase.pc) (h : eval k phase s=some t) : Runs (bound k) s t := by
  induction k generalizing phase s t with
  | zero => simp [eval] at h
  | succ k ih =>
    cases phase with
    | sector =>
      have p := sector_prefix s pc
      simp only [eval] at h
      split at h
      · rename_i done
        have eq : NoiseTraversal.returned (E1M1NoiseAlert.sectorResult s.core).core=t := Option.some.inj h
        rw [←eq]
        exact weaken (trans p (finish _ done)) (by simp only [bound]; omega)
      · split at h
        · rename_i more
          have q := init_lines (E1M1NoiseAlert.sectorResult s.core) more
          have r := ih .lines _ _ rfl h
          exact weaken (trans (trans p q) r) (by simp only [bound]; omega)
        · contradiction
    | lines =>
      simp only [eval] at h
      split at h
      · contradiction
      · rename_i opening
        have opening : OpeningReturns s.core := Classical.not_not.mp opening
        have p := dispatch_execution s pc opening
        split at h
        · rename_i child
          simp only [Option.bind_eq_bind] at h
          cases childRun : eval k .sector (E1M1NoiseIteration.dispatched s.core) with
          | none => simp [childRun] at h
          | some u =>
            simp only [childRun,Option.bind_some] at h
            split at h
            · rename_i ret
              have q := ih .sector _ _ child childRun
              have r := tail_execution k u t ih ret h
              exact weaken (trans (trans p q) r) (by simp only [bound]; omega)
            · simp at h
        · split at h
          · rename_i skip
            exact weaken (trans p (tail_execution k _ _ ih skip h)) (by simp only [bound]; omega)
          · simp at h

/-- At zero fuel no traversal, even a pruned one, is certified as complete. -/
theorem zero_fuel (phase : Phase) (s : X86Control.State) : eval 0 phase s=none := rfl

private theorem contains_noise (pc : Nat) (h : NoiseAlert.program pc≠none) : program pc=NoiseAlert.program pc := by
  change E1M1NoiseOpening.program pc=NoiseAlert.program pc
  have a := E1M1NoiseAlert.contains_noise pc h
  have b := E1M1NoiseTraversal.contains_prior pc (by rw [a]; exact h)
  rw [E1M1NoiseOpening.contains_prior pc (by rw [b,a]; exact h),b,a]
private theorem contains_fire (pc : Nat) (h : WeaponFire.program pc≠none) : program pc=WeaponFire.program pc := by
  change E1M1NoiseOpening.program pc=WeaponFire.program pc
  have a := E1M1WeaponFire.contains_fire pc h
  have b := E1M1WeaponContinuation.contains_prior pc (by rw [a]; exact h)
  have c := E1M1NoiseAlert.contains_prior pc (by rw [b,a]; exact h)
  have d := E1M1NoiseTraversal.contains_prior pc (by rw [c,b,a]; exact h)
  rw [E1M1NoiseOpening.contains_prior pc (by rw [d,c,b,a]; exact h),d,c,b,a]

/-- Original P_NoiseAlert entry followed by arbitrary successful recursive
propagation, including the sector's actual return to the noise caller. -/
theorem alert_execution (k : Nat) (s t : X86Control.State) (pc : s.pc=0x27020)
    (h : eval k .sector (NoiseAlert.result s.core)=some t) : Runs (8+bound k) s t := by
  obtain ⟨n,hn,p,_⟩ := X86Routine.run_path (NoiseAlert.entry_execution s.core s.flags)
  have p := (X86CodeMemory.lift_success p FloorCaller.cm).transfer program [] contains_noise (by simp)
  rw [←at_pc s _ pc] at p
  exact trans ⟨n,hn,p⟩ (execution k .sector _ _ rfl h)

/-- Complete accepted firing through recursive noise and the final fire RET.
Successful evaluation and the actual noise return address remain explicit. -/
theorem fire_execution (k : Nat) (s : X86Memory.State) (f : Option Flags) (t : X86Control.State)
    (enough : E1M1WeaponFire.Enough s)
    (actor : DeathSetter.SetterInputs E1M1WeaponFire.entry (E1M1WeaponFire.poseCall s).core 0x2d42a)
    (attack : E1M1WeaponContinuation.AttackReturns s)
    (noise : eval k .sector (NoiseAlert.result (E1M1NoiseAlert.noiseCall s).core)=some t)
    (ret : t.pc=0x2d44f) :
    Runs (121+bound k) ⟨s,f,0x2d410⟩ (WeaponFire.returned t.core t.flags) := by
  obtain ⟨n,hn,p⟩ := E1M1WeaponContinuation.noise_execution s f enough actor attack
  have p := ((p.transfer E1M1NoiseAlert.program [] E1M1NoiseAlert.contains_prior (by simp)).transfer E1M1NoiseTraversal.program [] E1M1NoiseTraversal.contains_prior (by simp)).transfer program [] E1M1NoiseOpening.contains_prior (by simp)
  have q := alert_execution k (E1M1NoiseAlert.noiseCall s) t rfl noise
  have r := (X86CodeMemory.lift_success (WeaponFire.return_execution t.core t.flags) FloorCaller.cm).transfer program [] contains_fire (by simp)
  rw [←at_pc t _ ret] at r
  have p : Runs 109 ⟨s,f,0x2d410⟩ (E1M1NoiseAlert.noiseCall s) := ⟨n,hn,p⟩
  have r : Runs 4 t (WeaponFire.returned t.core t.flags) := ⟨4,by omega,r⟩
  exact weaken (trans (trans p q) r) (by omega)
end Doom.Proofs.E1M1NoiseRecursive
