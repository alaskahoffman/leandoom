import Doom.Proofs.OriginalNoiseTraversal
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
namespace Doom.Proofs.E1M1NoiseTraversal
open Verification X86 X86Memory X86Control BlockSummary

def program (pc : Nat) : Option (X86Routine.Op × Nat) :=
  if 0x26fa6≤pc ∧ pc<0x2701a then NoiseTraversal.program pc else E1M1NoiseAlert.program pc

theorem contains_traversal (pc : Nat) (h : NoiseTraversal.program pc≠none) : program pc=NoiseTraversal.program pc := by
  by_cases inside : 0x26fa6≤pc ∧ pc<0x2701a
  · simp [program,inside]
  · exact False.elim (h (by simp [NoiseTraversal.program,NoiseTraversal.bytesProgram,inside]))
theorem contains_prior (pc : Nat) (h : E1M1NoiseAlert.program pc≠none) : program pc=E1M1NoiseAlert.program pc := by
  by_cases inside : 0x26fa6≤pc ∧ pc<0x2701a
  · have checked : ∀ i : Fin 116, E1M1NoiseAlert.program (0x26fa6+i.val)=none := by decide
    have eq : 0x26fa6+(pc-0x26fa6)=pc := by omega
    exact False.elim (h (by simpa only [eq] using checked ⟨pc-0x26fa6,by omega⟩))
  · simp [program,inside]
private theorem contains_fire (pc : Nat) (h : WeaponFire.program pc≠none) : program pc=WeaponFire.program pc := by
  have a := E1M1WeaponFire.contains_fire pc h
  have b := E1M1WeaponContinuation.contains_prior pc (by rw [a]; exact h)
  have c := E1M1NoiseAlert.contains_prior pc (by rw [b,a]; exact h)
  rw [contains_prior pc (by rw [c,b,a]; exact h),c,b,a]
private theorem path {stops n s t} (run : X86Routine.run NoiseTraversal.program stops n s=some t) :
    ∃ k, k≤n ∧ X86CodeMemory.Prefix FloorCaller.cm program [] k s t := by
  obtain ⟨k,hk,p,_⟩ := X86Routine.run_path run
  exact ⟨k,hk,(X86CodeMemory.lift_success p FloorCaller.cm).transfer program [] contains_traversal (by simp)⟩
private theorem finish (s : X86Control.State) (pc : s.pc=0x27011) :
    X86CodeMemory.Prefix FloorCaller.cm program [] 7 s (NoiseTraversal.returned s.core) := by
  have p := (X86CodeMemory.lift_success (NoiseTraversal.return_execution s.core s.flags) FloorCaller.cm).transfer program [] contains_traversal (by simp)
  have eq : s=⟨s.core,s.flags,0x27011⟩ := by rw [←pc]
  rw [←eq] at p
  exact p

def firstLine (s : X86Memory.State) := NoiseTraversal.lineGate (NoiseTraversal.initialized s).core
/-- Start the line list and test its actual first line. No opening is assumed. -/
theorem first_line_execution (s : X86Memory.State) (f : Option Flags) :
    ∃ n, n≤5 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x26fa6⟩ (firstLine s) := by
  have p := (X86CodeMemory.lift_success (NoiseTraversal.initialize_execution s f) FloorCaller.cm).transfer program [] contains_traversal (by simp)
  obtain ⟨m,hm,q⟩ := path (NoiseTraversal.line_execution (NoiseTraversal.initialized s).core (NoiseTraversal.initialized s).flags)
  exact ⟨1+m,by omega,E1M1PspriteStep.prefix_trans p q⟩

theorem opening_execution (s : X86Memory.State) (f : Option Flags) (twoSided : (firstLine s).pc=0x26fb4) :
    ∃ n, n≤7 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x26fa6⟩
      (NoiseTraversal.openingCall (firstLine s).core (firstLine s).flags) := by
  obtain ⟨n,hn,p⟩ := first_line_execution s f
  obtain ⟨m,hm,q⟩ := path (NoiseTraversal.opening_call_execution (firstLine s).core (firstLine s).flags)
  have eq : firstLine s=⟨(firstLine s).core,(firstLine s).flags,0x26fb4⟩ := by rw [←twoSided]
  rw [←eq] at q
  exact ⟨n+m,by omega,E1M1PspriteStep.prefix_trans p q⟩

/-- A one-sided line advances the real loop counter and pointer offset. -/
theorem skip_line_execution (s : X86Memory.State) (f : Option Flags)
    (skip : (NoiseTraversal.lineGate s).pc=0x27006) :
    ∃ n, n≤9 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x26fa8⟩
      (NoiseTraversal.advanced (NoiseTraversal.lineGate s).core) := by
  obtain ⟨n,hn,p⟩ := path (NoiseTraversal.line_execution s f)
  obtain ⟨m,hm,q⟩ := path (NoiseTraversal.advance_execution (NoiseTraversal.lineGate s).core (NoiseTraversal.lineGate s).flags)
  have eq : NoiseTraversal.lineGate s=⟨(NoiseTraversal.lineGate s).core,(NoiseTraversal.lineGate s).flags,0x27006⟩ := by rw [←skip]
  rw [←eq] at q
  exact ⟨n+m,by omega,E1M1PspriteStep.prefix_trans p q⟩

def sectorReturn (s : X86Memory.State) := NoiseTraversal.returned (E1M1NoiseAlert.sectorResult s).core
/-- Revisited or leaf sectors now run through their actual stack restoration
and RET. The condition is on the proved sector-prefix result, not a callee axiom. -/
theorem terminal_sector_execution (s : X86Memory.State) (f : Option Flags)
    (terminal : (E1M1NoiseAlert.sectorResult s).pc=0x27011) :
    ∃ n, n≤31 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x26f60⟩ (sectorReturn s) := by
  obtain ⟨n,hn,p⟩ := E1M1NoiseAlert.sector_execution s f
  exact ⟨n+7,by omega,E1M1PspriteStep.prefix_trans (p.transfer program [] contains_prior (by simp)) (finish _ terminal)⟩

def childReturn (s : X86Memory.State) := sectorReturn (NoiseTraversal.blockResult s).core
/-- Cross a permitted sound block, execute a terminal/pruned child sector,
return to the real parent address, and advance the parent's line loop. -/
theorem child_execution (s : X86Memory.State) (f : Option Flags)
    (call : (NoiseTraversal.blockResult s).pc=0x26f60)
    (terminal : (E1M1NoiseAlert.sectorResult (NoiseTraversal.blockResult s).core).pc=0x27011)
    (ret : (childReturn s).pc=0x27006) :
    ∃ n, n≤43 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x26fee⟩
      (NoiseTraversal.advanced (childReturn s).core) := by
  obtain ⟨n,hn,p⟩ := path (NoiseTraversal.block_execution s f)
  obtain ⟨m,hm,q⟩ := terminal_sector_execution (NoiseTraversal.blockResult s).core (NoiseTraversal.blockResult s).flags terminal
  have eq : NoiseTraversal.blockResult s=⟨(NoiseTraversal.blockResult s).core,(NoiseTraversal.blockResult s).flags,0x26f60⟩ := by rw [←call]
  rw [←eq] at q
  obtain ⟨k,hk,r⟩ := path (NoiseTraversal.advance_execution (childReturn s).core (childReturn s).flags)
  have er : childReturn s=⟨(childReturn s).core,(childReturn s).flags,0x27006⟩ := by rw [←ret]
  rw [←er] at r
  exact ⟨n+m+k,by omega,E1M1PspriteStep.prefix_trans (E1M1PspriteStep.prefix_trans p q) r⟩

def noiseReturn (s : X86Memory.State) := NoiseTraversal.returned (E1M1NoiseAlert.result (E1M1NoiseAlert.noiseCall s).core).core
def fireReturn (s : X86Memory.State) := WeaponFire.returned (noiseReturn s).core (noiseReturn s).flags
/-- Complete the accepted-fire return when noise's first sector terminates.
The firing and actual return-address contracts remain explicit. -/
theorem fire_return_execution (s : X86Memory.State) (f : Option Flags) (enough : E1M1WeaponFire.Enough s)
    (actor : DeathSetter.SetterInputs E1M1WeaponFire.entry (E1M1WeaponFire.poseCall s).core 0x2d42a)
    (attack : E1M1WeaponContinuation.AttackReturns s)
    (terminal : (E1M1NoiseAlert.result (E1M1NoiseAlert.noiseCall s).core).pc=0x27011)
    (ret : (noiseReturn s).pc=0x2d44f) :
    ∃ n, n≤152 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2d410⟩ (fireReturn s) := by
  obtain ⟨n,hn,p⟩ := E1M1NoiseAlert.fire_execution s f enough actor attack
  have q := finish _ terminal
  have r := (X86CodeMemory.lift_success (WeaponFire.return_execution (noiseReturn s).core (noiseReturn s).flags) FloorCaller.cm).transfer program [] contains_fire (by simp)
  have eq : noiseReturn s=⟨(noiseReturn s).core,(noiseReturn s).flags,0x2d44f⟩ := by rw [←ret]
  rw [←eq] at r
  exact ⟨n+7+4,by omega,E1M1PspriteStep.prefix_trans (E1M1PspriteStep.prefix_trans (p.transfer program [] contains_prior (by simp)) q) r⟩
end Doom.Proofs.E1M1NoiseTraversal
