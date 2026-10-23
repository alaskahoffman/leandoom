import Doom.Proofs.OriginalWeaponReadyEntry
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace Doom.Proofs.E1M1WeaponReadyEntry
open Verification X86 X86Memory X86Control

def program (pc : Nat) : Option (X86Routine.Op × Nat) :=
  if 0x2d2f0 ≤ pc ∧ pc < 0x2d333 then WeaponReadyEntry.program pc
  else E1M1WeaponReadyGate.program pc

theorem contains_entry (pc : Nat) (h : WeaponReadyEntry.program pc≠none) : program pc=WeaponReadyEntry.program pc := by
  by_cases inside : 0x2d2f0 ≤ pc ∧ pc < 0x2d333
  · simp [program,inside]
  · exact False.elim (h (by simp [WeaponReadyEntry.program,WeaponReadyEntry.bytesProgram,inside]))
theorem contains_prior (pc : Nat) (h : E1M1WeaponReadyGate.program pc≠none) : program pc=E1M1WeaponReadyGate.program pc := by
  by_cases inside : 0x2d2f0 ≤ pc ∧ pc < 0x2d333
  · have checked : ∀ i : Fin 67, E1M1WeaponReadyGate.program (0x2d2f0+i.val)=none := by decide
    have e : 0x2d2f0+(pc-0x2d2f0)=pc := by omega
    exact False.elim (h (by simpa only [e] using checked ⟨pc-0x2d2f0,by omega⟩))
  · simp [program,inside]

theorem entry_to_gate (s : X86Memory.State) (f : Option Flags) (frame : Fin 967) (w : Fin 3)
    (h : WeaponReadyEntry.Inputs s frame w) (idlePose : frame.val≠154 ∧ frame.val≠155) :
    ∃ n, n≤19 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2d2f0⟩
      ⟨WeaponReadyEntry.prepared s,some (compare32 (WeaponReadyEntry.weapon (WeaponReadyEntry.prepared s)) 7),0x2d333⟩ := by
  obtain ⟨n,hn,p⟩ := WeaponReadyEntry.execution s f
  rw [WeaponReadyEntry.ready_boundary s frame w h idlePose] at p
  exact ⟨n,hn,(X86CodeMemory.lift_success p FloorCaller.cm).transfer program [] contains_entry (by simp)⟩

/-- Full ordinary ready entry followed by the exact decision suffix. -/
theorem decision_execution (s : X86Memory.State) (f : Option Flags) (frame : Fin 967) (w : Fin 3)
    (h : WeaponReadyEntry.Inputs s frame w) (idlePose : frame.val≠154 ∧ frame.val≠155) :
    ∃ n, n≤35 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2d2f0⟩
      (WeaponReadyGate.result (WeaponReadyEntry.prepared s)) := by
  obtain ⟨n,hn,p⟩ := entry_to_gate s f frame w h idlePose
  obtain ⟨m,hm,q⟩ := WeaponReadyGate.execution (WeaponReadyEntry.prepared s) _
  have q := (X86CodeMemory.lift_success q FloorCaller.cm).transfer E1M1WeaponReadyGate.program [] E1M1WeaponReadyGate.contains_gate (by simp)
  exact ⟨n+m,by omega,E1M1PspriteStep.prefix_trans p (q.transfer program [] contains_prior (by simp))⟩

theorem idle_execution (s : X86Memory.State) (f : Option Flags) (frame : Fin 967) (w : Fin 3)
    (h : WeaponReadyEntry.Inputs s frame w) (idlePose : frame.val≠154 ∧ frame.val≠155)
    (low : ¬WeaponReadyGate.lowering (WeaponReadyEntry.prepared s))
    (a : WeaponReadyGate.attack (WeaponReadyEntry.prepared s)=0) :
    ∃ n, n≤58 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2d2f0⟩
      (WeaponReady.result (WeaponReadyEntry.prepared s)) := by
  obtain ⟨n,hn,p⟩ := entry_to_gate s f frame w h idlePose
  obtain ⟨m,hm,q⟩ := E1M1WeaponReadyGate.idle_execution (WeaponReadyEntry.prepared s) _ low a
  exact ⟨n+m,by omega,E1M1PspriteStep.prefix_trans p (q.transfer program [] contains_prior (by simp))⟩

theorem nested_execution (s : X86Memory.State) (f : Option Flags) (frame : Fin 967) (w : Fin 3)
    (h : WeaponReadyEntry.Inputs s frame w) (idlePose : frame.val≠154 ∧ frame.val≠155)
    (low : ¬WeaponReadyGate.lowering (WeaponReadyEntry.prepared s))
    (a : WeaponReadyGate.attack (WeaponReadyEntry.prepared s)=0) (t : X86Control.State)
    (ok : E1M1WeaponReady.raisedIdleReturn (WeaponReadyEntry.prepared s)=some t) :
    ∃ n, n≤87 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2d2f0⟩ t := by
  obtain ⟨n,hn,p⟩ := entry_to_gate s f frame w h idlePose
  obtain ⟨m,hm,q⟩ := E1M1WeaponReadyGate.nested_execution (WeaponReadyEntry.prepared s) _ t low a ok
  exact ⟨n+m,by omega,E1M1PspriteStep.prefix_trans p (q.transfer program [] contains_prior (by simp))⟩

/-- Uninterrupted original raising/setter/ready/return trace on the no-pose-reset
idle path. The ready-action address and post-prologue relations are explicit. -/
theorem raise_idle_return (s : X86Memory.State) (f : Option Flags) (frame : Fin 967) (w : Fin 3)
    (ready : (E1M1WeaponReady.raiseNext s).pc=0x2d2f0)
    (h : WeaponReadyEntry.Inputs (E1M1WeaponReady.raiseNext s).core frame w)
    (idlePose : frame.val≠154 ∧ frame.val≠155)
    (low : ¬WeaponReadyGate.lowering (WeaponReadyEntry.prepared (E1M1WeaponReady.raiseNext s).core))
    (a : WeaponReadyGate.attack (WeaponReadyEntry.prepared (E1M1WeaponReady.raiseNext s).core)=0)
    (t : X86Control.State)
    (ok : E1M1WeaponReady.raisedIdleReturn (WeaponReadyEntry.prepared (E1M1WeaponReady.raiseNext s).core)=some t) :
    ∃ n, n≤133 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2d4d0⟩ t := by
  obtain ⟨n,hn,p⟩ := E1M1WeaponReady.raise_next_execution s f
  have p := p.transfer E1M1WeaponReadyGate.program [] E1M1WeaponReadyGate.contains_prior (by simp)
  have p := p.transfer program [] contains_prior (by simp)
  let r := E1M1WeaponReady.raiseNext s
  have eq : r=⟨r.core,r.flags,0x2d2f0⟩ := by rw [←ready]
  obtain ⟨m,hm,q⟩ := nested_execution r.core r.flags frame w h idlePose low a t ok
  rw [←eq] at q
  exact ⟨n+m,by omega,E1M1PspriteStep.prefix_trans p q⟩

/-- The complete ordinary idle action restores the entry stack before RET;
its final stack pointer is entry ESP+4, not the suffix's ESP+20. -/
theorem idle_live (s : X86Memory.State) (f : Option Flags) (frame : Fin 967) (w : Fin 3)
    (entry : WeaponReadyEntry.Inputs s frame w) (idlePose : frame.val≠154 ∧ frame.val≠155)
    (low : ¬WeaponReadyGate.lowering (WeaponReadyEntry.prepared s))
    (a : WeaponReadyGate.attack (WeaponReadyEntry.prepared s)=0)
    (v : Weapon.State) (bob : Fixed) (time : Int32) (h : WeaponReady.Inputs (WeaponReadyEntry.prepared s) bob time) :
    let r := WeaponReady.result (WeaponReadyEntry.prepared s)
    (∃ n, n≤58 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2d2f0⟩ r) ∧
    load32 r.core.memory (WeaponReady.location (WeaponReadyEntry.prepared s) 0)=0 ∧
    load32 r.core.memory (WeaponReady.location (WeaponReadyEntry.prepared s) 1)=(Weapon.readyIdle v bob time).weapon.x.raw.toBitVec ∧
    load32 r.core.memory (WeaponReady.location (WeaponReadyEntry.prepared s) 2)=(Weapon.readyIdle v bob time).weapon.y.raw.toBitVec ∧
    r.pc=0x2d095 ∧ r.core.regs 4=s.regs 4+4 := by
  obtain ⟨l,x,y,pc,sp⟩ := WeaponReady.live_result (WeaponReadyEntry.prepared s) v bob time h
  refine ⟨idle_execution s f frame w entry idlePose low a,l,x,y,pc,?_⟩
  simpa [WeaponReadyEntry.prepared,WeaponReadyEntry.saved,X86Routine.pushWord,put,write,
    BitVec.sub_eq_add_neg,BitVec.add_assoc] using sp
end Doom.Proofs.E1M1WeaponReadyEntry
