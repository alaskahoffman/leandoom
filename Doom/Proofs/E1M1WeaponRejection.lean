import Doom.Proofs.E1M1WeaponContinuation
import Doom.Proofs.OriginalWeaponLowerProgress
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1WeaponRejection
open Verification X86 X86Memory X86Control BlockSummary
def state3 : List UInt8 := [0x2,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x0,0x0,0x0,0x90,0xd4,0x2,0x0,0x3,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]
def state11 : List UInt8 := [0x3,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x0,0x0,0x0,0x90,0xd4,0x2,0x0,0xb,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]
def state19 : List UInt8 := [0x1,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x0,0x0,0x0,0x90,0xd4,0x2,0x0,0x13,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]
def stateMemory (a : Word) : BitVec 8 :=
  if 0x15a7c≤a.toNat ∧ a.toNat<0x15a98 then state3.toArray[a.toNat-0x15a7c]!.toBitVec
  else if 0x15b5c≤a.toNat ∧ a.toNat<0x15b78 then state11.toArray[a.toNat-0x15b5c]!.toBitVec
  else if 0x15c3c≤a.toNat ∧ a.toNat<0x15c58 then state19.toArray[a.toNat-0x15c3c]!.toBitVec
  else 0

/-- Original mapped lowering states, including the relocated action target. -/
theorem lower_tables (w : Fin 3) :
    let id := Weapon.down w.val
    let p : Word := BitVec.ofNat 32 (0x15a28+28*id)
    load32 stateMemory (p+8)=(WeaponData.frames[id]!).tics.toBitVec ∧
    load32 stateMemory (p+12)=0x2d490 ∧ (WeaponData.frames[id]!).action="A_Lower" ∧
    load32 stateMemory (p+16)=BitVec.ofNat 32 (WeaponData.frames[id]!).next ∧
    load32 stateMemory (p+20)=0 ∧ load32 stateMemory (p+24)=0 := by
  have cases : w=0 ∨ w=1 ∨ w=2 := by omega
  rcases cases with rfl | rfl | rfl <;> decide

abbrev program := E1M1WeaponContinuation.program

theorem contains_ready (pc : Nat) (h : E1M1WeaponReady.program pc≠none) :
    program pc=E1M1WeaponReady.program pc := by
  have a := E1M1WeaponReadyGate.contains_prior pc h
  have b := E1M1WeaponReadyEntry.contains_prior pc (by rw [a]; exact h)
  have c := E1M1WeaponReadyReset.contains_prior pc (by rw [b,a]; exact h)
  have d := E1M1WeaponFire.contains_prior pc (by rw [c,b,a]; exact h)
  unfold program
  rw [E1M1WeaponContinuation.contains_prior pc (by rw [d,c,b,a]; exact h),d,c,b,a]
theorem contains_setter (pc : Nat) (h : E1M1PspriteSetter.program pc≠none) :
    program pc=E1M1PspriteSetter.program pc := by
  have a := E1M1PspriteLight.contains_prior pc h
  have b := E1M1WeaponReady.contains_prior pc (by rw [a]; exact h)
  rw [contains_ready pc (by rw [b,a]; exact h),b,a]
theorem contains_lower (pc : Nat) (h : WeaponLower.program pc≠none) :
    program pc=WeaponLower.program pc := by
  by_cases inside : 0x2d490≤pc ∧ pc<0x2d4cc
  · have checked : ∀ i : Fin 60, program (0x2d490+i.val)=WeaponLower.program (0x2d490+i.val) := by decide
    have eq : 0x2d490+(pc-0x2d490)=pc := by omega
    simpa only [eq] using checked ⟨pc-0x2d490,by omega⟩
  · exact False.elim (h (by simp [WeaponLower.program,WeaponLower.bytesProgram,inside]))

def lowerCall (s : X86Memory.State) := E1M1PspriteSetter.setterResult s
def lowerReturn (s : X86Memory.State) := WeaponLower.result (lowerCall s).core

/-- These conditions concern the real intermediate memory. In particular,
being below the threshold is checked after the callback's stack save. -/
structure LowerReturns (s : X86Memory.State) (t : X86Control.State) : Prop where
  callback : (lowerCall s).pc=0x2d490
  inProgress : WeaponLower.below (lowerCall s).core
  returnAddress : load32 (WeaponLower.advancedMemory (lowerCall s).core)
    ((lowerCall s).core.regs 4)=0x2d095
  finish : E1M1WeaponReady.finishSetter (lowerReturn s)=some t

/-- Install the lowering state, execute A_Lower, resume the setter and perform
its actual RET. No callback or stack restoration is supplied as a summary. -/
theorem lower_return_execution (s : X86Memory.State) (f : Option Flags) (t : X86Control.State)
    (h : LowerReturns s t) :
    ∃ n, n≤48 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2d040⟩ t := by
  obtain ⟨n,hn,p⟩ := E1M1PspriteSetter.setter_execution s f
  have p := p.transfer program [] contains_setter (by simp)
  obtain ⟨m,hm,q,_⟩ := X86Routine.run_path
    (WeaponLowerProgress.execution (lowerCall s).core (lowerCall s).flags h.inProgress h.returnAddress)
  have eq : lowerCall s=⟨(lowerCall s).core,(lowerCall s).flags,0x2d490⟩ := by rw [←h.callback]
  rw [←eq] at q
  have q := (X86CodeMemory.lift_success q FloorCaller.cm).transfer program [] contains_lower (by simp)
  obtain ⟨k,hk,r⟩ := E1M1WeaponReady.finish_setter_execution (lowerReturn s) t h.finish
  have r := r.transfer program [] contains_ready (by simp)
  exact ⟨n+m+k,by omega,E1M1PspriteStep.prefix_trans (E1M1PspriteStep.prefix_trans p q) r⟩

def fallback (s : X86Memory.State) := WeaponFallback.result (E1M1WeaponFire.afterCheck s).core
def rejected (t : X86Control.State) :=
  WeaponFire.returned (WeaponFallback.returned t.core).core (some (logical32 0))

/-- The whole rejected shot: ammo check, fallback choice, real lowering setter
and callback, both nested returns, and the fire routine's return to its caller.
The bottom-of-lowering weapon switch is deliberately outside this branch. -/
theorem rejected_execution (s : X86Memory.State) (f : Option Flags) (t : X86Control.State)
    (empty : ¬E1M1WeaponFire.Enough s)
    (inventory : WeaponFallback.Inventory (E1M1WeaponFire.afterCheck s).core)
    (lower : LowerReturns (fallback s).core t)
    (setterPC : t.pc=0x2d2aa)
    (ammoPC : (WeaponFallback.returned t.core).pc=0x2d41a) :
    ∃ n, n≤122 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2d410⟩ (rejected t) := by
  obtain ⟨n,hn,p⟩ := E1M1WeaponContinuation.empty_execution s f empty inventory
  obtain ⟨m,hm,q⟩ := lower_return_execution (fallback s).core (fallback s).flags t lower
  have eq : fallback s=⟨(fallback s).core,(fallback s).flags,0x2d040⟩ := rfl
  rw [←eq] at q
  obtain ⟨k,hk,r⟩ := E1M1WeaponContinuation.rejected_return_execution t.core t.flags ammoPC
  have et : t=⟨t.core,t.flags,0x2d2aa⟩ := by rw [←setterPC]
  rw [←et] at r
  exact ⟨n+m+k,by omega,E1M1PspriteStep.prefix_trans (E1M1PspriteStep.prefix_trans p q) r⟩
end Doom.Proofs.E1M1WeaponRejection
