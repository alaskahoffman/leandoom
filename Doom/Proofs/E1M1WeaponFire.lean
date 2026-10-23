import Doom.Proofs.OriginalWeaponFire
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1WeaponFire
open Verification X86 X86Memory X86Control BlockSummary

def entry : DeathSetter.Entry := ⟨154,28,4,12,149,by decide,by decide⟩
def poseBytes : List UInt8 := [0x1c,0x0,0x0,0x0,0x4,0x0,0x0,0x0,0xc,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x95,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]
def weaponsBytes : List UInt8 := [0x5,0x0,0x0,0x0,0x4,0x0,0x0,0x0,0x3,0x0,0x0,0x0,0x2,0x0,0x0,0x0,0x5,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xc,0x0,0x0,0x0,0xb,0x0,0x0,0x0,0xa,0x0,0x0,0x0,0xd,0x0,0x0,0x0,0x11,0x0,0x0,0x0,0x1,0x0,0x0,0x0,0x14,0x0,0x0,0x0,0x13,0x0,0x0,0x0,0x12,0x0,0x0,0x0,0x15,0x0,0x0,0x0,0x1e,0x0,0x0,0x0]
def tableMemory (a : Word) : BitVec 8 :=
  if 0x16b00 ≤ a.toNat ∧ a.toNat < 0x16b1c then poseBytes.toArray[a.toNat-0x16b00]!.toBitVec
  else if 0x12d90 ≤ a.toNat ∧ a.toNat < 0x12dd8 then weaponsBytes.toArray[a.toNat-0x12d90]!.toBitVec else 0

theorem table_decoded : DeathSetter.Table entry tableMemory := by constructor <;> decide
theorem weapon_table (w : Fin 3) :
    load32 tableMemory (0x12d90+24*BitVec.ofNat 32 w.val)=(if w.val=0 then 5 else if w.val=2 then 1 else 0) ∧
    load32 tableMemory (0x12da0+24*BitVec.ofNat 32 w.val)=BitVec.ofNat 32 (Weapon.attackState w.val) := by
  have cases : w=0 ∨ w=1 ∨ w=2 := by omega
  rcases cases with rfl | rfl | rfl <;> decide

def program (pc : Nat) : Option (X86Routine.Op × Nat) :=
  if (0x2d460 ≤ pc ∧ pc < 0x2d48d) ∨ (0x2d176 ≤ pc ∧ pc < 0x2d19f) then WeaponAmmo.program pc
  else if 0x2d410 ≤ pc ∧ pc < 0x2d453 then WeaponFire.program pc
  else E1M1WeaponReadyReset.program pc

theorem contains_ammo (pc : Nat) (h : WeaponAmmo.program pc≠none) : program pc=WeaponAmmo.program pc := by
  by_cases inside : (0x2d460 ≤ pc ∧ pc < 0x2d48d) ∨ (0x2d176 ≤ pc ∧ pc < 0x2d19f)
  · simp [program,inside]
  · have a : ¬(0x2d460 ≤ pc ∧ pc < 0x2d48d) := by omega
    have b : ¬(0x2d176 ≤ pc ∧ pc < 0x2d19f) := by omega
    exact False.elim (h (by simp [WeaponAmmo.program,WeaponAmmo.bytesProgram,a,b]))
theorem contains_fire (pc : Nat) (h : WeaponFire.program pc≠none) : program pc=WeaponFire.program pc := by
  have inside : 0x2d410 ≤ pc ∧ pc < 0x2d453 := by
    by_cases yes : 0x2d410 ≤ pc ∧ pc < 0x2d453
    · exact yes
    · exact False.elim (h (by simp [WeaponFire.program,WeaponFire.bytesProgram,yes]))
  have no : ¬((0x2d460 ≤ pc ∧ pc < 0x2d48d) ∨ (0x2d176 ≤ pc ∧ pc < 0x2d19f)) := by omega
  simp [program,no,inside]

theorem contains_prior (pc : Nat) (h : E1M1WeaponReadyReset.program pc≠none) : program pc=E1M1WeaponReadyReset.program pc := by
  by_cases a : 0x2d460 ≤ pc ∧ pc < 0x2d48d
  · have check : ∀ i : Fin 45, E1M1WeaponReadyReset.program (0x2d460+i.val)=none := by decide
    have eq : 0x2d460+(pc-0x2d460)=pc := by omega
    exact False.elim (h (by simpa only [eq] using check ⟨pc-0x2d460,by omega⟩))
  by_cases b : 0x2d176 ≤ pc ∧ pc < 0x2d19f
  · have check : ∀ i : Fin 41, E1M1WeaponReadyReset.program (0x2d176+i.val)=none := by decide
    have eq : 0x2d176+(pc-0x2d176)=pc := by omega
    exact False.elim (h (by simpa only [eq] using check ⟨pc-0x2d176,by omega⟩))
  by_cases c : 0x2d410 ≤ pc ∧ pc < 0x2d453
  · have check : ∀ i : Fin 67, E1M1WeaponReadyReset.program (0x2d410+i.val)=none := by decide
    have eq : 0x2d410+(pc-0x2d410)=pc := by omega
    exact False.elim (h (by simpa only [eq] using check ⟨pc-0x2d410,by omega⟩))
  simp [program,a,b,c]

def afterCheck (s : X86Memory.State) := WeaponAmmo.result (WeaponFire.checkCall s none).core

theorem check_execution (s : X86Memory.State) (f : Option Flags) :
    ∃ n, n≤30 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2d410⟩ (afterCheck s) := by
  obtain ⟨n,hn,p,_⟩ := X86Routine.run_path (WeaponFire.check_call_execution s f)
  obtain ⟨m,hm,q⟩ := WeaponAmmo.execution (WeaponFire.checkCall s f).core f
  have eq : WeaponFire.checkCall s f=⟨(WeaponFire.checkCall s f).core,f,0x2d460⟩ := rfl
  rw [←eq] at q
  have p := (X86CodeMemory.lift_success (p.transfer WeaponFire.program [] (by intros; rfl) (by simp)) FloorCaller.cm).transfer program [] contains_fire (by simp)
  have q := (X86CodeMemory.lift_success q FloorCaller.cm).transfer program [] contains_ammo (by simp)
  exact ⟨n+m,by omega,E1M1PspriteStep.prefix_trans p q⟩

abbrev Enough (s : X86Memory.State) := WeaponAmmo.allowed (WeaponAmmo.charged (WeaponAmmo.prepared (WeaponFire.checkCall s none).core)).core

theorem check_return (s : X86Memory.State) (h : Enough s) :
    (afterCheck s).pc=0x2d41a ∧ (afterCheck s).core.regs 0=1 := by
  have q := WeaponAmmo.success_return (WeaponFire.checkCall s none).core h
  have pc : (afterCheck s).pc=0x2d41a := by
    simpa [afterCheck,WeaponFire.checkCall,X86Routine.pushWord,put,write,load_store] using q.1
  exact ⟨pc,q.2.1⟩

def poseCall (s : X86Memory.State) := WeaponFire.poseCall (afterCheck s).core (WeaponFire.branch (afterCheck s).core).flags

theorem pose_call_execution (s : X86Memory.State) (f : Option Flags) (h : Enough s) :
    ∃ n, n≤35 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2d410⟩ (poseCall s) := by
  obtain ⟨n,hn,p⟩ := check_execution s f
  have check := check_return s h
  have eq : afterCheck s=⟨(afterCheck s).core,(afterCheck s).flags,0x2d41a⟩ := by rw [←check.1]
  obtain ⟨m,hm,q,_⟩ := X86Routine.run_path (WeaponFire.branch_execution (afterCheck s).core (afterCheck s).flags)
  rw [←eq] at q
  have branch : WeaponFire.branch (afterCheck s).core=⟨(afterCheck s).core,(WeaponFire.branch (afterCheck s).core).flags,0x2d41e⟩ := by simp [WeaponFire.branch,check.2]
  obtain ⟨k,hk,r,_⟩ := X86Routine.run_path (WeaponFire.pose_call_execution (afterCheck s).core (WeaponFire.branch (afterCheck s).core).flags)
  rw [←branch] at r
  have q := (X86CodeMemory.lift_success (q.transfer WeaponFire.program [] (by intros; rfl) (by simp)) FloorCaller.cm).transfer program [] contains_fire (by simp)
  have r := (X86CodeMemory.lift_success (r.transfer WeaponFire.program [] (by intros; rfl) (by simp)) FloorCaller.cm).transfer program [] contains_fire (by simp)
  exact ⟨n+m+k,by omega,E1M1PspriteStep.prefix_trans (E1M1PspriteStep.prefix_trans p q) r⟩

def afterPose (s : X86Memory.State) := ActorSetterReturn.result entry (poseCall s).core 0x2d42a

theorem pose_execution (s : X86Memory.State) (f : Option Flags) (h : Enough s)
    (setter : DeathSetter.SetterInputs entry (poseCall s).core 0x2d42a) :
    ∃ n, n≤59 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2d410⟩ (afterPose s) := by
  obtain ⟨n,hn,p⟩ := pose_call_execution s f h
  obtain ⟨m,hm,q⟩ := ActorSetterReturn.execution entry (poseCall s).core (poseCall s).flags 0x2d42a setter
  have eq : poseCall s=⟨(poseCall s).core,(poseCall s).flags,0x30ea0⟩ := rfl
  rw [←eq] at q
  have q := (X86CodeMemory.lift_success q FloorCaller.cm).transfer E1M1WeaponReadyReset.program [] E1M1WeaponReadyReset.contains_setter (by simp)
  exact ⟨n+m,by omega,E1M1PspriteStep.prefix_trans p (q.transfer program [] contains_prior (by simp))⟩

theorem live_pose (s : X86Memory.State) :
    DeathSetter.observeFields (afterPose s).core.memory ((poseCall s).core.regs 0)=
      (BitVec.ofNat 32 (0x15a28+28*(PlayerAnim.enter 154).1.frame),(PlayerAnim.enter 154).1.tics.toBitVec,28,4) := by
  simpa [afterPose,entry,DeathSetter.Entry.pointer,PlayerAnim.enter] using ActorSetterReturn.fields entry (poseCall s).core 0x2d42a

/-- The actor setter is closed; the weapon-state setter is still a real callee
boundary. This theorem does not assume an attack callback or noise propagation. -/
theorem attack_execution (s : X86Memory.State) (f : Option Flags) (h : Enough s)
    (setter : DeathSetter.SetterInputs entry (poseCall s).core 0x2d42a) :
    ∃ n, n≤66 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2d410⟩ (WeaponFire.attackCall (afterPose s).core) := by
  obtain ⟨n,hn,p⟩ := pose_execution s f h setter
  obtain ⟨m,hm,q,_⟩ := X86Routine.run_path (WeaponFire.attack_call_execution (afterPose s).core (afterPose s).flags)
  have eq : afterPose s=⟨(afterPose s).core,(afterPose s).flags,0x2d42a⟩ := rfl
  rw [←eq] at q
  have q := (X86CodeMemory.lift_success (q.transfer WeaponFire.program [] (by intros; rfl) (by simp)) FloorCaller.cm).transfer program [] contains_fire (by simp)
  exact ⟨n+m,by omega,E1M1PspriteStep.prefix_trans p q⟩


private theorem contains_base (pc : Nat) (h : E1M1PspriteSetter.program pc≠none) : program pc=E1M1PspriteSetter.program pc := by
  have a := E1M1PspriteLight.contains_prior pc h
  have b := E1M1WeaponReady.contains_prior pc (by rw [a]; exact h)
  have c := E1M1WeaponReadyGate.contains_prior pc (by rw [b,a]; exact h)
  have d := E1M1WeaponReadyEntry.contains_prior pc (by rw [c,b,a]; exact h)
  have e := E1M1WeaponReadyReset.contains_prior pc (by rw [d,c,b,a]; exact h)
  rw [contains_prior pc (by rw [e,d,c,b,a]; exact h),e,d,c,b,a]

/-- Continue into the actual weapon-state setter, through installation and
its action dispatch boundary. The callback itself remains a separate proof. -/
theorem attack_state_execution (s : X86Memory.State) (f : Option Flags) (h : Enough s)
    (setter : DeathSetter.SetterInputs entry (poseCall s).core 0x2d42a) :
    ∃ n, n≤95 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2d410⟩
      (E1M1PspriteSetter.setterResult (WeaponFire.attackCall (afterPose s).core).core) := by
  obtain ⟨n,hn,p⟩ := attack_execution s f h setter
  let call := WeaponFire.attackCall (afterPose s).core
  obtain ⟨m,hm,q⟩ := E1M1PspriteSetter.setter_execution call.core call.flags
  have eq : call=⟨call.core,call.flags,0x2d040⟩ := rfl
  rw [←eq] at q
  exact ⟨n+m,by omega,E1M1PspriteStep.prefix_trans p (q.transfer program [] contains_base (by simp))⟩


private theorem contains_gate (pc : Nat) (h : WeaponReadyGate.program pc≠none) : program pc=WeaponReadyGate.program pc := by
  have inside : 0x2d333 ≤ pc ∧ pc < 0x2d392 := by
    by_cases yes : 0x2d333 ≤ pc ∧ pc < 0x2d392
    · exact yes
    · exact False.elim (h (by simp [WeaponReadyGate.program,WeaponReadyGate.bytesProgram,yes]))
  have check : ∀ i : Fin 95, program (0x2d333+i.val)=WeaponReadyGate.program (0x2d333+i.val) := by decide
  have eq : 0x2d333+(pc-0x2d333)=pc := by omega
  simpa only [eq] using check ⟨pc-0x2d333,by omega⟩

/-- Join the earlier ready decision and its actual fire CALL, including the
attack-latch store, through ammo acceptance, actor pose and attack-state entry. -/
theorem ready_fire_execution (s : X86Memory.State) (f : Option Flags)
    (fire : (WeaponReadyGate.result s).pc=0x2d410)
    (h : Enough (WeaponReadyGate.result s).core)
    (setter : DeathSetter.SetterInputs entry (poseCall (WeaponReadyGate.result s).core).core 0x2d42a) :
    ∃ n, n≤111 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2d333⟩
      (E1M1PspriteSetter.setterResult (WeaponFire.attackCall (afterPose (WeaponReadyGate.result s).core).core).core) := by
  obtain ⟨n,hn,p⟩ := WeaponReadyGate.execution s f
  let call := WeaponReadyGate.result s
  obtain ⟨m,hm,q⟩ := attack_state_execution call.core call.flags h setter
  have eq : call=⟨call.core,call.flags,0x2d410⟩ := by rw [←fire]
  rw [←eq] at q
  have p := (X86CodeMemory.lift_success p FloorCaller.cm).transfer program [] contains_gate (by simp)
  exact ⟨n+m,by omega,E1M1PspriteStep.prefix_trans p q⟩
end Doom.Proofs.E1M1WeaponFire
