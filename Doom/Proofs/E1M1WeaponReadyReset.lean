import Doom.Proofs.OriginalActorSetterReturn
import Doom.Proofs.E1M1WeaponReadyEntry
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
namespace Doom.Proofs.E1M1WeaponReadyReset
open Verification X86 X86Memory X86Control

def entry : DeathSetter.Entry := ⟨149,28,0,0xffffffff,0,by decide,by decide⟩
def stateBytes : List UInt8 := [28,0,0,0,0,0,0,0,255,255,255,255,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem table_decoded : DeathSetter.Table entry (fun a =>
    if 0x16a74 ≤ a.toNat ∧ a.toNat < 0x16a90 then stateBytes.toArray[a.toNat-0x16a74]!.toBitVec else 0) := by
  constructor <;> decide

def returned (s : X86Memory.State) := ActorSetterReturn.result entry s 0x2d319

theorem live_pose (s : X86Memory.State) :
    DeathSetter.observeFields (returned s).core.memory (s.regs 0)=
      (BitVec.ofNat 32 (0x15a28+28*(PlayerAnim.enter 149).1.frame),
        (PlayerAnim.enter 149).1.tics.toBitVec,28,0) := by
  simpa [returned,entry,DeathSetter.Entry.pointer,PlayerAnim.enter] using ActorSetterReturn.fields entry s 0x2d319

def program (pc : Nat) : Option (X86Routine.Op × Nat) :=
  if 0x30ea0 ≤ pc ∧ pc < 0x30efb then DeathSetter.program pc
  else E1M1WeaponReadyEntry.program pc

theorem contains_setter (pc : Nat) (h : DeathSetter.program pc≠none) : program pc=DeathSetter.program pc := by
  by_cases inside : 0x30ea0 ≤ pc ∧ pc < 0x30efb
  · simp [program,inside]
  · exact False.elim (h (by simp [DeathSetter.program,PainSetter.program,PainSetter.bytesProgram,inside]))
theorem contains_prior (pc : Nat) (h : E1M1WeaponReadyEntry.program pc≠none) : program pc=E1M1WeaponReadyEntry.program pc := by
  by_cases inside : 0x30ea0 ≤ pc ∧ pc < 0x30efb
  · have checked : ∀ i : Fin 91, E1M1WeaponReadyEntry.program (0x30ea0+i.val)=none ∨
        E1M1WeaponReadyEntry.program (0x30ea0+i.val)=DeathSetter.program (0x30ea0+i.val) := by decide
    have e : 0x30ea0+(pc-0x30ea0)=pc := by omega
    have q := checked ⟨pc-0x30ea0,by omega⟩
    simp only [e] at q
    rcases q with no | eq
    · exact False.elim (h no)
    · simp [program,inside,eq]
  · simp [program,inside]
private theorem contains_entry (pc : Nat) (h : WeaponReadyEntry.program pc≠none) : program pc=WeaponReadyEntry.program pc := by
  have eq := E1M1WeaponReadyEntry.contains_entry pc h
  rw [contains_prior pc (by rw [eq]; exact h),eq]
private theorem contains_gate (pc : Nat) (h : E1M1WeaponReadyGate.program pc≠none) : program pc=E1M1WeaponReadyGate.program pc := by
  have eq := E1M1WeaponReadyEntry.contains_prior pc h
  rw [contains_prior pc (by rw [eq]; exact h),eq]

theorem setter_execution (s : X86Memory.State) (f : Option Flags)
    (h : DeathSetter.SetterInputs entry s 0x2d319) :
    ∃ n, n≤24 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x30ea0⟩ (returned s) := by
  obtain ⟨n,hn,p⟩ := ActorSetterReturn.execution entry s f 0x2d319 h
  exact ⟨n,hn,(X86CodeMemory.lift_success p FloorCaller.cm).transfer program [] contains_setter (by simp)⟩

/-- The real call boundary from the entry summary, before any setter writes. -/
def call (s : X86Memory.State) := WeaponReadyEntry.result s
def afterReset (s : X86Memory.State) := returned (call s).core

/-- Both firing poses execute the actual setter and return to the next
instruction in A_WeaponReady; the previous summary's callee boundary is closed. -/
theorem reset_execution (s : X86Memory.State) (f : Option Flags)
    (reset : WeaponReadyEntry.needsReset (WeaponReadyEntry.prepared s))
    (h : DeathSetter.SetterInputs entry (call s).core 0x2d319) :
    ∃ n, n≤43 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2d2f0⟩ (afterReset s) := by
  obtain ⟨n,hn,p⟩ := WeaponReadyEntry.execution s f
  have p := (X86CodeMemory.lift_success p FloorCaller.cm).transfer program [] contains_entry (by simp)
  have eq : call s=⟨(call s).core,(call s).flags,0x30ea0⟩ := by
    simp [call,WeaponReadyEntry.result,reset,WeaponReadyEntry.resetCall]
  obtain ⟨m,hm,q⟩ := setter_execution (call s).core (call s).flags h
  rw [←eq] at q
  exact ⟨n+m,by omega,E1M1PspriteStep.prefix_trans p q⟩

/-- The ready-weapon read is transported across the setter using its exact
write footprint. ECX (the player pointer) is preserved by the callee. -/
theorem weapon_preserved (s : X86Memory.State)
    (safe : ∀ b, b ∈ DeathSetter.writes s → BlockSummary.Apart (s.regs 1+112) b) :
    WeaponReadyEntry.weapon (returned s).core=WeaponReadyEntry.weapon s := by
  have keep := ActorSetterReturn.memory_frame entry s 0x2d319 (s.regs 1+112) safe
  simpa [WeaponReadyEntry.weapon,returned,ActorSetterReturn.result,write] using keep

/-- Supported weapons bypass the chainsaw call after the actual pose reset.
The ready-weapon separation premise refers to the setter's input memory. -/
theorem gate_execution (s : X86Memory.State) (f : Option Flags) (w : Fin 3)
    (reset : WeaponReadyEntry.needsReset (WeaponReadyEntry.prepared s))
    (h : DeathSetter.SetterInputs entry (call s).core 0x2d319)
    (weapon : WeaponReadyEntry.weapon (call s).core=BitVec.ofNat 32 w.val)
    (safe : ∀ b, b ∈ DeathSetter.writes (call s).core → BlockSummary.Apart ((call s).core.regs 1+112) b) :
    ∃ n, n≤50 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2d2f0⟩
      ⟨(afterReset s).core,some (compare32 (WeaponReadyEntry.weapon (afterReset s).core) 7),0x2d333⟩ := by
  obtain ⟨n,hn,p⟩ := reset_execution s f reset h
  have ne : WeaponReadyEntry.weapon (afterReset s).core≠(7#32) := by
    rw [afterReset,weapon_preserved _ safe,weapon]
    have cases : w.val=0 ∨ w.val=1 ∨ w.val=2 := by omega
    rcases cases with e | e | e <;> rw [e] <;> decide
  obtain ⟨m,hm,q,_⟩ := X86Routine.run_path (WeaponReadyEntry.sound_execution (afterReset s).core (afterReset s).flags)
  have q := (X86CodeMemory.lift_success (q.transfer WeaponReadyEntry.program [] (by intros; rfl) (by simp)) FloorCaller.cm).transfer program [] contains_entry (by simp)
  have eq : afterReset s=⟨(afterReset s).core,(afterReset s).flags,0x2d319⟩ := rfl
  rw [←eq] at q
  simp only [WeaponReadyEntry.sound,if_pos ne] at q
  exact ⟨n+m,by omega,E1M1PspriteStep.prefix_trans p q⟩

theorem idle_execution (s : X86Memory.State) (f : Option Flags) (w : Fin 3)
    (reset : WeaponReadyEntry.needsReset (WeaponReadyEntry.prepared s))
    (h : DeathSetter.SetterInputs entry (call s).core 0x2d319)
    (weapon : WeaponReadyEntry.weapon (call s).core=BitVec.ofNat 32 w.val)
    (safe : ∀ b, b ∈ DeathSetter.writes (call s).core → BlockSummary.Apart ((call s).core.regs 1+112) b)
    (low : ¬WeaponReadyGate.lowering (afterReset s).core) (a : WeaponReadyGate.attack (afterReset s).core=0) :
    ∃ n, n≤89 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2d2f0⟩ (WeaponReady.result (afterReset s).core) := by
  obtain ⟨n,hn,p⟩ := gate_execution s f w reset h weapon safe
  obtain ⟨m,hm,q⟩ := E1M1WeaponReadyGate.idle_execution (afterReset s).core _ low a
  exact ⟨n+m,by omega,E1M1PspriteStep.prefix_trans p (q.transfer program [] contains_gate (by simp))⟩

theorem nested_execution (s : X86Memory.State) (f : Option Flags) (w : Fin 3)
    (reset : WeaponReadyEntry.needsReset (WeaponReadyEntry.prepared s))
    (h : DeathSetter.SetterInputs entry (call s).core 0x2d319)
    (weapon : WeaponReadyEntry.weapon (call s).core=BitVec.ofNat 32 w.val)
    (safe : ∀ b, b ∈ DeathSetter.writes (call s).core → BlockSummary.Apart ((call s).core.regs 1+112) b)
    (low : ¬WeaponReadyGate.lowering (afterReset s).core) (a : WeaponReadyGate.attack (afterReset s).core=0)
    (t : X86Control.State) (ok : E1M1WeaponReady.raisedIdleReturn (afterReset s).core=some t) :
    ∃ n, n≤118 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2d2f0⟩ t := by
  obtain ⟨n,hn,p⟩ := gate_execution s f w reset h weapon safe
  obtain ⟨m,hm,q⟩ := E1M1WeaponReadyGate.nested_execution (afterReset s).core _ t low a ok
  exact ⟨n+m,by omega,E1M1PspriteStep.prefix_trans p (q.transfer program [] contains_gate (by simp))⟩
/-- The previously connected raising path now also includes a real firing-pose
reset. All calls and returns belong to one instruction prefix. -/
theorem raise_reset_return (s : X86Memory.State) (f : Option Flags) (w : Fin 3)
    (ready : (E1M1WeaponReady.raiseNext s).pc=0x2d2f0)
    (reset : WeaponReadyEntry.needsReset (WeaponReadyEntry.prepared (E1M1WeaponReady.raiseNext s).core))
    (h : DeathSetter.SetterInputs entry (call (E1M1WeaponReady.raiseNext s).core).core 0x2d319)
    (weapon : WeaponReadyEntry.weapon (call (E1M1WeaponReady.raiseNext s).core).core=BitVec.ofNat 32 w.val)
    (safe : ∀ b, b ∈ DeathSetter.writes (call (E1M1WeaponReady.raiseNext s).core).core →
      BlockSummary.Apart ((call (E1M1WeaponReady.raiseNext s).core).core.regs 1+112) b)
    (low : ¬WeaponReadyGate.lowering (afterReset (E1M1WeaponReady.raiseNext s).core).core)
    (a : WeaponReadyGate.attack (afterReset (E1M1WeaponReady.raiseNext s).core).core=0)
    (t : X86Control.State) (ok : E1M1WeaponReady.raisedIdleReturn (afterReset (E1M1WeaponReady.raiseNext s).core).core=some t) :
    ∃ n, n≤164 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2d4d0⟩ t := by
  obtain ⟨n,hn,p⟩ := E1M1WeaponReady.raise_next_execution s f
  have p := p.transfer E1M1WeaponReadyGate.program [] E1M1WeaponReadyGate.contains_prior (by simp)
  have p := p.transfer program [] contains_gate (by simp)
  let r := E1M1WeaponReady.raiseNext s
  have eq : r=⟨r.core,r.flags,0x2d2f0⟩ := by rw [←ready]
  obtain ⟨m,hm,q⟩ := nested_execution r.core r.flags w reset h weapon safe low a t ok
  rw [←eq] at q
  exact ⟨n+m,by omega,E1M1PspriteStep.prefix_trans p q⟩
end Doom.Proofs.E1M1WeaponReadyReset
