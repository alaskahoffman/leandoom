import Doom.Proofs.OriginalWeaponReadyGate
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace Doom.Proofs.E1M1WeaponReadyGate
open Verification X86 X86Memory X86Control

def program (pc : Nat) : Option (X86Routine.Op × Nat) :=
  if 0x2d333 ≤ pc ∧ pc < 0x2d392 then WeaponReadyGate.program pc
  else E1M1WeaponReady.program pc

theorem contains_gate (pc : Nat) (h : WeaponReadyGate.program pc≠none) : program pc=WeaponReadyGate.program pc := by
  by_cases inside : 0x2d333 ≤ pc ∧ pc < 0x2d392
  · simp [program,inside]
  · exact False.elim (h (by simp [WeaponReadyGate.program,WeaponReadyGate.bytesProgram,inside]))
theorem contains_prior (pc : Nat) (h : E1M1WeaponReady.program pc≠none) : program pc=E1M1WeaponReady.program pc := by
  by_cases inside : 0x2d333 ≤ pc ∧ pc < 0x2d392
  · have checked : ∀ i : Fin 95, E1M1WeaponReady.program (0x2d333+i.val)=none := by decide
    have e : 0x2d333+(pc-0x2d333)=pc := by omega
    exact False.elim (h (by simpa only [e] using checked ⟨pc-0x2d333,by omega⟩))
  · simp [program,inside]

theorem idle_gate (s : X86Memory.State) (f : Option Flags)
    (low : ¬WeaponReadyGate.lowering s) (a : WeaponReadyGate.attack s=0) :
    ∃ n, n≤16 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n
      ⟨s,f,0x2d333⟩ ⟨s,some (logical8 (WeaponReadyGate.attack s)),0x2d392⟩ := by
  obtain ⟨n,hn,p⟩ := WeaponReadyGate.execution s f
  rw [WeaponReadyGate.idle_result s low a] at p
  exact ⟨n,hn,(X86CodeMemory.lift_success p FloorCaller.cm).transfer program [] contains_gate (by simp)⟩

/-- Read-only decisions followed by the complete idle bob and actual RET. -/
theorem idle_execution (s : X86Memory.State) (f : Option Flags)
    (low : ¬WeaponReadyGate.lowering s) (a : WeaponReadyGate.attack s=0) :
    ∃ n, n≤39 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n
      ⟨s,f,0x2d333⟩ (WeaponReady.result s) := by
  obtain ⟨n,hn,p⟩ := idle_gate s f low a
  obtain ⟨m,hm,q⟩ := WeaponReady.execution s (some (logical8 (WeaponReadyGate.attack s)))
  have q := (X86CodeMemory.lift_success q FloorCaller.cm).transfer E1M1WeaponReady.program [] E1M1WeaponReady.contains_ready (by simp)
  have q := q.transfer program [] contains_prior (by simp)
  exact ⟨n+m,by omega,E1M1PspriteStep.prefix_trans p q⟩

/-- The same decision prefix also joins the earlier nested setter/raise return
proof. The successful-return premise remains explicit and executable. -/
theorem nested_execution (s : X86Memory.State) (f : Option Flags) (t : X86Control.State)
    (low : ¬WeaponReadyGate.lowering s) (a : WeaponReadyGate.attack s=0)
    (ok : E1M1WeaponReady.raisedIdleReturn s=some t) :
    ∃ n, n≤68 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2d333⟩ t := by
  obtain ⟨n,hn,p⟩ := idle_gate s f low a
  obtain ⟨m,hm,q⟩ := E1M1WeaponReady.raised_idle_return_execution s (some (logical8 (WeaponReadyGate.attack s))) t ok
  exact ⟨n+m,by omega,E1M1PspriteStep.prefix_trans p (q.transfer program [] contains_prior (by simp))⟩

/-- Branch, bob coordinates, attack latch and actual callback return agree
with the live helper, under the original table and byte-separation boundary. -/
theorem idle_live (s : X86Memory.State) (f : Option Flags) (v : Weapon.State)
    (bob : Fixed) (time : Int32) (h : WeaponReady.Inputs s bob time)
    (low : ¬WeaponReadyGate.lowering s) (a : WeaponReadyGate.attack s=0) :
    (∃ n, n≤39 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2d333⟩ (WeaponReady.result s)) ∧
    load32 (WeaponReady.result s).core.memory (WeaponReady.location s 0)=0 ∧
    load32 (WeaponReady.result s).core.memory (WeaponReady.location s 1)=(Weapon.readyIdle v bob time).weapon.x.raw.toBitVec ∧
    load32 (WeaponReady.result s).core.memory (WeaponReady.location s 2)=(Weapon.readyIdle v bob time).weapon.y.raw.toBitVec ∧
    (WeaponReady.result s).pc=0x2d095 ∧ (WeaponReady.result s).core.regs 4=s.regs 4+20 :=
  ⟨idle_execution s f low a,WeaponReady.live_result s v bob time h⟩
end Doom.Proofs.E1M1WeaponReadyGate
