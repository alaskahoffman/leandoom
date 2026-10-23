import Doom.Proofs.OriginalWeaponReady
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace Doom.Proofs.E1M1WeaponReady
open Verification X86 X86Memory X86Control

def program (pc : Nat) : Option (X86Routine.Op × Nat) :=
  if 0x2d392 ≤ pc ∧ pc < 0x2d3e7 then WeaponReady.program pc
  else if 0x2d4d0 ≤ pc ∧ pc < 0x2d510 then WeaponRaise.program pc
  else E1M1PspriteLight.program pc

theorem contains_ready (pc : Nat) (h : WeaponReady.program pc≠none) : program pc=WeaponReady.program pc := by
  by_cases inside : 0x2d392 ≤ pc ∧ pc < 0x2d3e7
  · simp [program,inside]
  · exact False.elim (h (by simp [WeaponReady.program,WeaponReady.bytesProgram,inside]))
theorem contains_raise (pc : Nat) (h : WeaponRaise.program pc≠none) : program pc=WeaponRaise.program pc := by
  by_cases inside : 0x2d4d0 ≤ pc ∧ pc < 0x2d510
  · have outside : ¬(0x2d392 ≤ pc ∧ pc < 0x2d3e7) := by omega
    simp [program,inside,outside]
  · exact False.elim (h (by simp [WeaponRaise.program,WeaponRaise.bytesProgram,inside]))
theorem contains_prior (pc : Nat) (h : E1M1PspriteLight.program pc≠none) : program pc=E1M1PspriteLight.program pc := by
  by_cases ready : 0x2d392 ≤ pc ∧ pc < 0x2d3e7
  · have checked : ∀ i : Fin 85, E1M1PspriteLight.program (0x2d392+i.val)=none := by decide
    have e : 0x2d392+(pc-0x2d392)=pc := by omega
    exact False.elim (h (by simpa only [e] using checked ⟨pc-0x2d392,by omega⟩))
  · by_cases raise : 0x2d4d0 ≤ pc ∧ pc < 0x2d510
    · have checked : ∀ i : Fin 64, E1M1PspriteLight.program (0x2d4d0+i.val)=none := by decide
      have e : 0x2d4d0+(pc-0x2d4d0)=pc := by omega
      exact False.elim (h (by simpa only [e] using checked ⟨pc-0x2d4d0,by omega⟩))
    · simp [program,ready,raise]
theorem contains_setter (pc : Nat) (h : PspriteSetter.program pc≠none) : program pc=PspriteSetter.program pc := by
  have eq := E1M1PspriteLight.contains_setter pc h
  rw [contains_prior pc (by rw [eq]; exact h),eq]
private theorem contains_base (pc : Nat) (h : E1M1PspriteSetter.program pc≠none) : program pc=E1M1PspriteSetter.program pc := by
  have eq := E1M1PspriteLight.contains_prior pc h
  rw [contains_prior pc (by rw [eq]; exact h),eq]

/-- A_Raise followed by its actual setter invocation. A progressing raise
instead resumes the outer setter. The ready callback is the next boundary. -/
def raiseNext (s : X86Memory.State) : X86Control.State :=
  let r := WeaponRaise.result s
  if r.pc=0x2d040 then E1M1PspriteSetter.setterResult r.core
  else if r.pc=0x2d095 then E1M1PspriteSetter.resumed r.core else r

theorem raise_next_execution (s : X86Memory.State) (f : Option Flags) :
    ∃ n, n ≤ 46 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2d4d0⟩ (raiseNext s) := by
  obtain ⟨n,hn,a⟩ := WeaponRaise.execution s f
  have a := (X86CodeMemory.lift_success a FloorCaller.cm).transfer program [] contains_raise (by simp)
  let r := WeaponRaise.result s
  by_cases call : (WeaponRaise.result s).pc=0x2d040
  · obtain ⟨m,hm,b⟩ := E1M1PspriteSetter.setter_execution r.core r.flags
    have b := b.transfer program [] contains_base (by simp)
    have e : r=⟨r.core,r.flags,0x2d040⟩ := by rw [←call]
    rw [←e] at b
    exact ⟨n+m,by omega,by simpa only [raiseNext,r,if_pos call] using E1M1PspriteStep.prefix_trans a b⟩
  · by_cases ret : (WeaponRaise.result s).pc=0x2d095
    · obtain ⟨m,hm,b⟩ := E1M1PspriteSetter.resume_execution r.core r.flags
      have b := b.transfer program [] contains_base (by simp)
      have e : r=⟨r.core,r.flags,0x2d095⟩ := by rw [←ret]
      rw [←e] at b
      exact ⟨n+m,by omega,by simpa only [raiseNext,r,if_neg call,if_pos ret] using E1M1PspriteStep.prefix_trans a b⟩
    · exact ⟨n,by omega,by simpa only [raiseNext,r,if_neg call,if_neg ret] using a⟩

/-- Resume a real callback return and finish a nonzero-tic state. Unsupported
zero-tic continuations fail explicitly; no callee behavior is substituted. -/
def finishSetter (s : X86Control.State) : Option X86Control.State :=
  if s.pc=0x2d095 then
    let r := E1M1PspriteSetter.resumed s.core
    if r.pc=0x2d0ac then some (PspriteSetter.returned r.core r.flags) else none
  else none

theorem finish_setter_execution (s t : X86Control.State) (ok : finishSetter s=some t) :
    ∃ n, n ≤ 13 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n s t := by
  simp only [finishSetter] at ok
  split at ok
  · rename_i pc
    split at ok
    · rename_i exit
      obtain ⟨n,hn,a⟩ := E1M1PspriteSetter.resume_execution s.core s.flags
      have a := a.transfer program [] contains_base (by simp)
      have e : s=⟨s.core,s.flags,0x2d095⟩ := by rw [←pc]
      rw [←e] at a
      let r := E1M1PspriteSetter.resumed s.core
      have b := (X86CodeMemory.lift_success (PspriteSetter.return_execution r.core r.flags) FloorCaller.cm).transfer program [] contains_setter (by simp)
      have er : r=⟨r.core,r.flags,0x2d0ac⟩ := by rw [←exit]
      rw [←er] at b
      have out := Option.some.inj ok
      rw [out] at b
      exact ⟨n+3,by omega,E1M1PspriteStep.prefix_trans a b⟩
    · cases ok
  · cases ok

/-- Complete the idle ready suffix and, when present, both nested returns:
ready -> inner setter -> A_Raise -> outer setter. -/
def raisedIdleReturn (s : X86Memory.State) : Option X86Control.State := do
  let inner ← finishSetter (WeaponReady.result s)
  if inner.pc≠0x2d50d then none else
    finishSetter (WeaponRaise.returned inner.core inner.flags)

theorem raised_idle_return_execution (s : X86Memory.State) (f : Option Flags) (t : X86Control.State)
    (ok : raisedIdleReturn s=some t) :
    ∃ n, n ≤ 52 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2d392⟩ t := by
  cases inner : finishSetter (WeaponReady.result s) with
  | none => simp [raisedIdleReturn,inner] at ok
  | some u =>
    simp only [raisedIdleReturn,inner,Bind.bind,Option.bind] at ok
    split at ok
    · cases ok
    · rename_i pc
      have pc : u.pc=0x2d50d := by simpa using pc
      obtain ⟨n,hn,a⟩ := WeaponReady.execution s f
      have a := (X86CodeMemory.lift_success a FloorCaller.cm).transfer program [] contains_ready (by simp)
      obtain ⟨m,hm,b⟩ := finish_setter_execution _ _ inner
      have c := (X86CodeMemory.lift_success (WeaponRaise.return_execution u.core u.flags) FloorCaller.cm).transfer program [] contains_raise (by simp)
      have e : u=⟨u.core,u.flags,0x2d50d⟩ := by rw [←pc]
      rw [←e] at c
      obtain ⟨k,hk,d⟩ := finish_setter_execution _ _ ok
      exact ⟨n+m+3+k,by omega,E1M1PspriteStep.prefix_trans (E1M1PspriteStep.prefix_trans (E1M1PspriteStep.prefix_trans a b) c) d⟩
/-- Attach the already proved flash phase to the complete nested return path.
The post-weapon boundary is explicit; deriving it from reachable game states
and covering the earlier ready-action gates remain separate obligations. -/
theorem raised_idle_flash (s : X86Memory.State) (f : Option Flags) (u : X86Control.State)
    (p : Word) (v : Weapon.State) (ok : raisedIdleReturn s=some u)
    (pc : u.pc=0x2dc95) (boundary : E1M1WeaponFlash.Boundary u.core p v)
    (supported : WeaponFlash.Supported v)
    (expiry : ¬ E1M1FlashUpdate.NoTransition v → E1M1FlashExpiry.Tables u.core.memory ∧
      E1M1FlashExpiry.Separated p (u.core.regs 4)) :
    ∃ n t, n ≤ 162 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2d392⟩ t ∧
      E1M1FlashUpdate.observe t.core.memory p=WeaponFlash.observe (Weapon.tickFlash v) := by
  obtain ⟨n,hn,a⟩ := raised_idle_return_execution s f u ok
  obtain ⟨m,t,hm,b,obs⟩ := E1M1WeaponFlash.suffix_correspondence u p v pc boundary supported expiry
  have b := b.transfer program [] contains_prior (by simp)
  exact ⟨n+m,t,by omega,E1M1PspriteStep.prefix_trans a b,obs⟩
end Doom.Proofs.E1M1WeaponReady

