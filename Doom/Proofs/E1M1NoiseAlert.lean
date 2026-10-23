import Doom.Proofs.OriginalNoiseAlert
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
namespace Doom.Proofs.E1M1NoiseAlert
open Verification X86 X86Memory X86Control BlockSummary

def program (pc : Nat) : Option (X86Routine.Op × Nat) :=
  if (0x27020≤pc ∧ pc<0x2703e) ∨ (0x26f60≤pc ∧ pc<0x26fa6) then NoiseAlert.program pc
  else E1M1WeaponContinuation.program pc

theorem contains_noise (pc : Nat) (h : NoiseAlert.program pc≠none) : program pc=NoiseAlert.program pc := by
  by_cases inside : (0x27020≤pc ∧ pc<0x2703e) ∨ (0x26f60≤pc ∧ pc<0x26fa6)
  · simp [program,inside]
  · exact False.elim (h (by simp [NoiseAlert.program,NoiseAlert.bytesProgram,not_or.mp inside |>.1,not_or.mp inside |>.2]))
theorem contains_prior (pc : Nat) (h : E1M1WeaponContinuation.program pc≠none) :
    program pc=E1M1WeaponContinuation.program pc := by
  by_cases inside : (0x27020≤pc ∧ pc<0x2703e) ∨ (0x26f60≤pc ∧ pc<0x26fa6)
  · rcases inside with a | b
    · have checked : ∀ i : Fin 30, E1M1WeaponContinuation.program (0x27020+i.val)=none := by decide
      have eq : 0x27020+(pc-0x27020)=pc := by omega
      exact False.elim (h (by simpa only [eq] using checked ⟨pc-0x27020,by omega⟩))
    · have checked : ∀ i : Fin 70, E1M1WeaponContinuation.program (0x26f60+i.val)=none := by decide
      have eq : 0x26f60+(pc-0x26f60)=pc := by omega
      exact False.elim (h (by simpa only [eq] using checked ⟨pc-0x26f60,by omega⟩))
  · simp [program,inside]

private theorem path {stops n s t} (run : X86Routine.run NoiseAlert.program stops n s=some t) :
    ∃ k, k≤n ∧ X86CodeMemory.Prefix FloorCaller.cm program [] k s t := by
  obtain ⟨k,hk,p,_⟩ := X86Routine.run_path run
  exact ⟨k,hk,(X86CodeMemory.lift_success p FloorCaller.cm).transfer program [] contains_noise (by simp)⟩

def sectorResult (s : X86Memory.State) :=
  let g := NoiseAlert.gate (NoiseAlert.prepared s)
  if g.pc=0x26f83 then NoiseAlert.updated g.core else g

/-- General first sector decision: revisit pruning or the three sector writes.
The endpoint still exposes line traversal or the return epilogue as unfinished. -/
theorem sector_execution (s : X86Memory.State) (f : Option Flags) :
    ∃ n, n≤24 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x26f60⟩ (sectorResult s) := by
  have p := (X86CodeMemory.lift_success (NoiseAlert.prepare_execution s f) FloorCaller.cm).transfer program [] contains_noise (by simp)
  obtain ⟨m,hm,q⟩ := path (NoiseAlert.gate_execution (NoiseAlert.prepared s) none)
  have pq := E1M1PspriteStep.prefix_trans p q
  let g := NoiseAlert.gate (NoiseAlert.prepared s)
  by_cases enter : g.pc=0x26f83
  · obtain ⟨k,hk,r⟩ := path (NoiseAlert.update_execution g.core g.flags)
    have eq : g=⟨g.core,g.flags,0x26f83⟩ := by rw [←enter]
    rw [←eq] at r
    exact ⟨9+m+k,by omega,by simpa only [sectorResult,g,if_pos enter] using E1M1PspriteStep.prefix_trans pq r⟩
  · exact ⟨9+m,by omega,by simpa only [sectorResult,g,if_neg enter] using pq⟩

def result (s : X86Memory.State) := sectorResult (NoiseAlert.result s).core

theorem alert_execution (s : X86Memory.State) (f : Option Flags) :
    ∃ n, n≤32 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x27020⟩ (result s) := by
  obtain ⟨n,hn,p⟩ := path (NoiseAlert.entry_execution s f)
  obtain ⟨m,hm,q⟩ := sector_execution (NoiseAlert.result s).core (NoiseAlert.result s).flags
  exact ⟨n+m,by omega,E1M1PspriteStep.prefix_trans p q⟩

def noiseCall (s : X86Memory.State) :=
  WeaponFire.noiseCall (E1M1WeaponContinuation.attackReturn s).core (E1M1WeaponContinuation.attackReturn s).flags

/-- Actual fire entry, ammo/pose/psprite calls, noise entry and sector decision.
This is not yet recursive propagation or the complete weapon-update theorem. -/
theorem fire_execution (s : X86Memory.State) (f : Option Flags) (enough : E1M1WeaponFire.Enough s)
    (actor : DeathSetter.SetterInputs E1M1WeaponFire.entry (E1M1WeaponFire.poseCall s).core 0x2d42a)
    (attack : E1M1WeaponContinuation.AttackReturns s) :
    ∃ n, n≤141 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2d410⟩ (result (noiseCall s).core) := by
  obtain ⟨n,hn,p⟩ := E1M1WeaponContinuation.noise_execution s f enough actor attack
  obtain ⟨m,hm,q⟩ := alert_execution (noiseCall s).core (noiseCall s).flags
  exact ⟨n+m,by omega,E1M1PspriteStep.prefix_trans (p.transfer program [] contains_prior (by simp)) q⟩
end Doom.Proofs.E1M1NoiseAlert
