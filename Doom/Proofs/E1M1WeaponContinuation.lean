import Doom.Proofs.OriginalWeaponFallback
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1WeaponContinuation
open Verification X86 X86Memory X86Control BlockSummary
def state5 : List UInt8 := [0x2,0x0,0x0,0x0,0x1,0x0,0x0,0x0,0x4,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x6,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]
def state13 : List UInt8 := [0x3,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x4,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xe,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]
def state21 : List UInt8 := [0x1,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x16,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]
def stateMemory (a : Word) : BitVec 8 :=
  if 0x15ab4≤a.toNat ∧ a.toNat<0x15ad0 then state5.toArray[a.toNat-0x15ab4]!.toBitVec
  else if 0x15b94≤a.toNat ∧ a.toNat<0x15bb0 then state13.toArray[a.toNat-0x15b94]!.toBitVec
  else if 0x15c74≤a.toNat ∧ a.toNat<0x15c90 then state21.toArray[a.toNat-0x15c74]!.toBitVec else 0

/-- Pin the initial attack timers and action-free successor records to the
production state table, for all three weapons in the current scope. -/
theorem attack_tables (w : Fin 3) :
    let id := Weapon.attackState w.val
    let p : Word := BitVec.ofNat 32 (0x15a28+28*id)
    load32 stateMemory (p+8)=(WeaponData.frames[id]!).tics.toBitVec ∧
    load32 stateMemory (p+12)=0 ∧
    load32 stateMemory (p+16)=BitVec.ofNat 32 (WeaponData.frames[id]!).next ∧
    load32 stateMemory (p+20)=0 ∧ load32 stateMemory (p+24)=0 := by
  have cases : w=0 ∨ w=1 ∨ w=2 := by omega
  rcases cases with rfl | rfl | rfl <;> decide

def program (pc : Nat) : Option (X86Routine.Op × Nat) :=
  if 0x2d19f≤pc ∧ pc<0x2d2b1 then WeaponFallback.program pc else E1M1WeaponFire.program pc

theorem contains_fallback (pc : Nat) (h : WeaponFallback.program pc≠none) : program pc=WeaponFallback.program pc := by
  by_cases inside : 0x2d19f≤pc ∧ pc<0x2d2b1
  · simp [program,inside]
  · exact False.elim (h (by simp [WeaponFallback.program,WeaponFallback.bytesProgram,inside]))
theorem contains_prior (pc : Nat) (h : E1M1WeaponFire.program pc≠none) : program pc=E1M1WeaponFire.program pc := by
  by_cases inside : 0x2d19f≤pc ∧ pc<0x2d2b1
  · have checked : ∀ i : Fin 274, E1M1WeaponFire.program (0x2d19f+i.val)=none := by decide
    have eq : 0x2d19f+(pc-0x2d19f)=pc := by omega
    exact False.elim (h (by simpa only [eq] using checked ⟨pc-0x2d19f,by omega⟩))
  · simp [program,inside]
private theorem contains_base (pc : Nat) (h : E1M1PspriteSetter.program pc≠none) : program pc=E1M1PspriteSetter.program pc := by
  have a := E1M1PspriteLight.contains_prior pc h
  have b := E1M1WeaponReady.contains_prior pc (by rw [a]; exact h)
  have c := E1M1WeaponReadyGate.contains_prior pc (by rw [b,a]; exact h)
  have d := E1M1WeaponReadyEntry.contains_prior pc (by rw [c,b,a]; exact h)
  have e := E1M1WeaponReadyReset.contains_prior pc (by rw [d,c,b,a]; exact h)
  have g := E1M1WeaponFire.contains_prior pc (by rw [e,d,c,b,a]; exact h)
  rw [contains_prior pc (by rw [g,e,d,c,b,a]; exact h),g,e,d,c,b,a]
private theorem contains_setter (pc : Nat) (h : PspriteSetter.program pc≠none) : program pc=PspriteSetter.program pc := by
  have eq := E1M1PspriteSetter.contains_setter pc h
  rw [contains_base pc (by rw [eq]; exact h),eq]
private theorem contains_fire (pc : Nat) (h : WeaponFire.program pc≠none) : program pc=WeaponFire.program pc := by
  have eq := E1M1WeaponFire.contains_fire pc h
  rw [contains_prior pc (by rw [eq]; exact h),eq]

/-- The rejected ammo branch continues through actual inventory selection and
CALLs the lowering-state setter. The lowering callback remains a callee. -/
theorem empty_execution (s : X86Memory.State) (f : Option Flags)
    (empty : ¬E1M1WeaponFire.Enough s)
    (inventory : WeaponFallback.Inventory (E1M1WeaponFire.afterCheck s).core) :
    ∃ n, n≤62 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2d410⟩
      (WeaponFallback.result (E1M1WeaponFire.afterCheck s).core) := by
  obtain ⟨n,hn,p⟩ := E1M1WeaponFire.check_execution s f
  have eq : E1M1WeaponFire.afterCheck s=⟨(E1M1WeaponFire.afterCheck s).core,(E1M1WeaponFire.afterCheck s).flags,0x2d19f⟩ := by
    simp only [E1M1WeaponFire.afterCheck,WeaponAmmo.result,if_neg empty]
    simp [WeaponAmmo.checked,WeaponAmmo.decision,empty]
  obtain ⟨m,hm,q⟩ := WeaponFallback.execution (E1M1WeaponFire.afterCheck s).core (E1M1WeaponFire.afterCheck s).flags inventory
  rw [←eq] at q
  have q := (X86CodeMemory.lift_success q FloorCaller.cm).transfer program [] contains_fallback (by simp)
  exact ⟨n+m,by omega,E1M1PspriteStep.prefix_trans (p.transfer program [] contains_prior (by simp)) q⟩

def setterReturn (s : X86Memory.State) :=
  let r := E1M1PspriteChain.continued (PspriteSetter.prepared s)
  PspriteSetter.returned r.core r.flags

/-- Reusable action-free, nonzero-timer state entry with both actual pops and
RET. Conditions refer to the real intermediate memory, allowing aliasing. -/
theorem setter_return_execution (s : X86Memory.State) (f : Option Flags)
    (nonzero : s.regs 3≠(0#32))
    (quiet : E1M1PspriteChain.NoAction (PspriteSetter.prepared s))
    (timer : (E1M1PspriteChain.continued (PspriteSetter.prepared s)).pc=0x2d0ac) :
    ∃ n, n≤40 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2d040⟩ (setterReturn s) := by
  obtain ⟨n,hn,p,_⟩ := X86Routine.run_path (PspriteSetter.entry_execution s f)
  have eq : PspriteSetter.entered s=⟨PspriteSetter.prepared s,(PspriteSetter.entered s).flags,0x2d05e⟩ := by
    simp [PspriteSetter.entered,nonzero]
  obtain ⟨m,hm,q⟩ := E1M1PspriteChain.iteration_execution (PspriteSetter.prepared s) (PspriteSetter.entered s).flags quiet
  rw [←eq] at q
  let r := E1M1PspriteChain.continued (PspriteSetter.prepared s)
  have er : r=⟨r.core,r.flags,0x2d0ac⟩ := by rw [←timer]
  have tail := PspriteSetter.return_execution r.core r.flags
  rw [←er] at tail
  have p := (X86CodeMemory.lift_success (p.transfer PspriteSetter.program [] (by intros; rfl) (by simp)) FloorCaller.cm).transfer program [] contains_setter (by simp)
  have q := q.transfer program [] contains_base (by simp)
  have tail := (X86CodeMemory.lift_success tail FloorCaller.cm).transfer program [] contains_setter (by simp)
  exact ⟨n+m+3,by omega,E1M1PspriteStep.prefix_trans (E1M1PspriteStep.prefix_trans p q) tail⟩

def attackCall (s : X86Memory.State) := WeaponFire.attackCall (E1M1WeaponFire.afterPose s).core
def attackReturn (s : X86Memory.State) := setterReturn (attackCall s).core
structure AttackReturns (s : X86Memory.State) : Prop where
  nonzero : (attackCall s).core.regs 3≠(0#32)
  quiet : E1M1PspriteChain.NoAction (PspriteSetter.prepared (attackCall s).core)
  timer : (E1M1PspriteChain.continued (PspriteSetter.prepared (attackCall s).core)).pc=0x2d0ac
  returnPC : (attackReturn s).pc=0x2d446

theorem attack_return_execution (s : X86Memory.State) (f : Option Flags) (h : E1M1WeaponFire.Enough s)
    (setter : DeathSetter.SetterInputs E1M1WeaponFire.entry (E1M1WeaponFire.poseCall s).core 0x2d42a)
    (ret : AttackReturns s) :
    ∃ n, n≤106 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2d410⟩ (attackReturn s) := by
  obtain ⟨n,hn,p⟩ := E1M1WeaponFire.attack_execution s f h setter
  obtain ⟨m,hm,q⟩ := setter_return_execution (attackCall s).core (attackCall s).flags ret.nonzero ret.quiet ret.timer
  have eq : attackCall s=⟨(attackCall s).core,(attackCall s).flags,0x2d040⟩ := rfl
  rw [←eq] at q
  exact ⟨n+m,by omega,E1M1PspriteStep.prefix_trans (p.transfer program [] contains_prior (by simp)) q⟩

/-- Noise alert is a gameplay effect (monster wakeup). The theorem reaches the
real P_NoiseAlert entry, without assuming its implementation or replacing it. -/
theorem noise_execution (s : X86Memory.State) (f : Option Flags) (h : E1M1WeaponFire.Enough s)
    (setter : DeathSetter.SetterInputs E1M1WeaponFire.entry (E1M1WeaponFire.poseCall s).core 0x2d42a)
    (ret : AttackReturns s) :
    ∃ n, n≤109 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2d410⟩
      (WeaponFire.noiseCall (attackReturn s).core (attackReturn s).flags) := by
  obtain ⟨n,hn,p⟩ := attack_return_execution s f h setter ret
  obtain ⟨m,hm,q,_⟩ := X86Routine.run_path (WeaponFire.noise_call_execution (attackReturn s).core (attackReturn s).flags)
  have eq : attackReturn s=⟨(attackReturn s).core,(attackReturn s).flags,0x2d446⟩ := by rw [←ret.returnPC]
  rw [←eq] at q
  have q := (X86CodeMemory.lift_success (q.transfer WeaponFire.program [] (by intros; rfl) (by simp)) FloorCaller.cm).transfer program [] contains_fire (by simp)
  exact ⟨n+m,by omega,E1M1PspriteStep.prefix_trans p q⟩


/-- After the lowering setter returns, ammo failure returns zero and the
fire caller returns without entering an attack pose or issuing a noise alert. -/
theorem rejected_return_execution (s : X86Memory.State) (f : Option Flags)
    (ret : (WeaponFallback.returned s).pc=0x2d41a) :
    ∃ n, n≤12 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2d2aa⟩
      (WeaponFire.returned (WeaponFallback.returned s).core (some (logical32 0))) := by
  let r := WeaponFallback.returned s
  have p := (X86CodeMemory.lift_success (WeaponFallback.return_execution s f) FloorCaller.cm).transfer program [] contains_fallback (by simp)
  have zero : r.core.regs 0=(0#32) := by simp [r,WeaponFallback.returned,PspriteLoop.popped,put,write]
  obtain ⟨n,hn,q,_⟩ := X86Routine.run_path (WeaponFire.branch_execution r.core r.flags)
  have eq : r=⟨r.core,r.flags,0x2d41a⟩ := by rw [←ret]
  rw [←eq] at q
  have branch : WeaponFire.branch r.core=⟨r.core,some (logical32 0),0x2d44f⟩ := by simp [WeaponFire.branch,zero]
  rw [branch] at q
  have q := (X86CodeMemory.lift_success (q.transfer WeaponFire.program [] (by intros; rfl) (by simp)) FloorCaller.cm).transfer program [] contains_fire (by simp)
  have tail := (X86CodeMemory.lift_success (WeaponFire.return_execution r.core (some (logical32 0))) FloorCaller.cm).transfer program [] contains_fire (by simp)
  exact ⟨6+n+4,by omega,E1M1PspriteStep.prefix_trans (E1M1PspriteStep.prefix_trans p q) tail⟩
end Doom.Proofs.E1M1WeaponContinuation
