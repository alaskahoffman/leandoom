import Doom.Proofs.OriginalPspriteLight
import Doom.Proofs.PspriteChainDriver
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace Doom.Proofs.E1M1PspriteLight
open Verification X86 X86Memory X86Control BlockSummary

def program (pc : Nat) : Option (X86Routine.Op × Nat) :=
  match PspriteLight.program pc with
  | some op => some op
  | none => E1M1PspriteChain.program pc

theorem contains_light (pc : Nat) (h : PspriteLight.program pc≠none) : program pc=PspriteLight.program pc := by
  unfold program
  cases e : PspriteLight.program pc with
  | none => exact False.elim (h e)
  | some op => rfl

theorem contains_prior (pc : Nat) (h : E1M1PspriteChain.program pc≠none) : program pc=E1M1PspriteChain.program pc := by
  by_cases inside : 0x2db40 ≤ pc ∧ pc < 0x2db6b
  · have checked : ∀ i : Fin 43, E1M1PspriteChain.program (0x2db40+i.val)=none := by decide
    have e : 0x2db40+(pc-0x2db40)=pc := by omega
    exact False.elim (h (by simpa only [e] using checked ⟨pc-0x2db40,by omega⟩))
  · have none : PspriteLight.program pc=none := by
      have a : ¬(0x2db40 ≤ pc ∧ pc < 0x2db4b) := by omega
      have b : ¬(0x2db50 ≤ pc ∧ pc < 0x2db5b) := by omega
      have c : ¬(0x2db60 ≤ pc ∧ pc < 0x2db6b) := by omega
      simp [PspriteLight.program,PspriteLight.bytesProgram,a,b,c]
    simp [program,none]

theorem contains_setter (pc : Nat) (h : PspriteSetter.program pc≠none) : program pc=PspriteSetter.program pc := by
  have eq := E1M1PspriteSetter.contains_setter pc h
  change E1M1PspriteChain.program pc=PspriteSetter.program pc at eq
  rw [contains_prior pc (by rw [eq]; exact h),eq]

def index (pc : Nat) : Option (Fin 3) :=
  if pc=0x2db40 then some 0 else if pc=0x2db50 then some 1 else if pc=0x2db60 then some 2 else none

theorem index_entry (pc : Nat) (i : Fin 3) (h : index pc=some i) : pc=PspriteLight.entry i := by
  unfold index at h
  split at h <;> (try split at h) <;> (try split at h) <;> simp_all [PspriteLight.entry]
  all_goals subst i <;> decide

/-- Only proved light callbacks are executed. Their actual RET must lead back
to the setter before its post-action state is reread. -/
def advance (s : X86Memory.State) : Option X86Control.State :=
  if E1M1PspriteChain.NoAction s then some (E1M1PspriteChain.continued s)
  else do
    let d := E1M1PspriteSetter.dispatched s
    let i ← index d.pc
    let r := PspriteLight.result i d.core d.flags
    if r.pc=0x2d095 then some (E1M1PspriteSetter.resumed r.core) else none

theorem advance_execution (s : X86Memory.State) (f : Option Flags) (t : X86Control.State)
    (ok : advance s=some t) :
    ∃ n, n ≤ 32 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2d05e⟩ t := by
  simp only [advance] at ok
  split at ok
  · rename_i quiet
    obtain ⟨n,hn,p⟩ := E1M1PspriteChain.iteration_execution s f quiet
    have out := Option.some.inj ok
    rw [out] at p
    exact ⟨n,by omega,p.transfer program [] contains_prior (by simp)⟩
  · let d := E1M1PspriteSetter.dispatched s
    cases found : index d.pc with
    | none => simp [show index (E1M1PspriteSetter.dispatched s).pc=none from found] at ok
    | some i =>
      simp only [show index (E1M1PspriteSetter.dispatched s).pc=some i from found,Bind.bind,Option.bind] at ok
      split at ok
      · rename_i returned
        obtain ⟨n,hn,p⟩ := E1M1PspriteSetter.dispatch_execution s f
        have p := p.transfer program [] contains_prior (by simp)
        have a := (X86CodeMemory.lift_success (PspriteLight.execution i d.core d.flags) FloorCaller.cm).transfer program [] contains_light (by simp)
        have e : d=⟨d.core,d.flags,PspriteLight.entry i⟩ := by rw [←index_entry d.pc i found]
        rw [←e] at a
        let r := PspriteLight.result i d.core d.flags
        obtain ⟨m,hm,b⟩ := E1M1PspriteSetter.resume_execution r.core r.flags
        have b := b.transfer program [] contains_prior (by simp)
        have er : r=⟨r.core,r.flags,0x2d095⟩ := by rw [←returned]
        rw [←er] at b
        have out := Option.some.inj ok
        rw [out] at b
        exact ⟨n+2+m,by omega,E1M1PspriteStep.prefix_trans (E1M1PspriteStep.prefix_trans p a) b⟩
      · cases ok

def chain := PspriteChainDriver.chain advance

theorem chain_execution (fuel : Nat) (s t : X86Control.State) (ok : chain fuel s=some t) :
    ∃ n, n ≤ 32*fuel+4 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n s t :=
  PspriteChainDriver.execution program advance 32 contains_setter advance_execution fuel s t ok

theorem chain_mono (fuel extra : Nat) (s t : X86Control.State) (ok : chain fuel s=some t) :
    chain (fuel+extra) s=some t := PspriteChainDriver.mono advance fuel extra s t ok


private theorem path {stops n s t}
    (run : X86Routine.run PspriteSetter.program stops n s=some t) :
    ∃ k, k ≤ n ∧ X86CodeMemory.Prefix FloorCaller.cm program [] k s t := by
  obtain ⟨k,hk,p,_⟩ := X86Routine.run_path run
  exact ⟨k,hk,(X86CodeMemory.lift_success p FloorCaller.cm).transfer program [] contains_setter (by simp)⟩

theorem contains_slot (pc : Nat) (h : PspriteStep.program pc≠none) : program pc=PspriteStep.program pc := by
  have eq := E1M1PspriteLoop.contains_slot pc h
  change E1M1PspriteChain.program pc=PspriteStep.program pc at eq
  rw [contains_prior pc (by rw [eq]; exact h),eq]

theorem contains_tail (pc : Nat) (h : PspriteLoop.program pc≠none) : program pc=PspriteLoop.program pc := by
  have eq := E1M1PspriteLoop.contains_tail pc h
  change E1M1PspriteChain.program pc=PspriteLoop.program pc at eq
  rw [contains_prior pc (by rw [eq]; exact h),eq]

def complete (fuel : Nat) (s : X86Memory.State) := chain fuel (PspriteSetter.entered s)

theorem complete_execution (fuel : Nat) (s : X86Memory.State) (f : Option Flags)
    (t : X86Control.State) (ok : complete fuel s=some t) :
    ∃ n, n ≤ 32*fuel+13 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2d040⟩ t := by
  obtain ⟨n,hn,a⟩ := path (PspriteSetter.entry_execution s f)
  obtain ⟨m,hm,b⟩ := chain_execution fuel (PspriteSetter.entered s) t ok
  exact ⟨n+m,by omega,E1M1PspriteStep.prefix_trans a b⟩

def slot (fuel : Nat) (s : X86Memory.State) : Option X86Control.State :=
  let t := PspriteStep.result s
  if t.pc=0x2d040 then complete fuel t.core else some t

theorem slot_execution (fuel : Nat) (s : X86Memory.State) (f : Option Flags)
    (t : X86Control.State) (ok : slot fuel s=some t) :
    ∃ n, n ≤ 32*fuel+28 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2dc6f⟩ t := by
  obtain ⟨n,hn,a,_⟩ := X86Routine.run_path (PspriteStep.slot_execution s f)
  have a := (X86CodeMemory.lift_success a FloorCaller.cm).transfer program [] contains_slot (by simp)
  simp only [slot] at ok
  split at ok
  · rename_i expires
    obtain ⟨m,hm,b⟩ := complete_execution fuel (PspriteStep.result s).core (PspriteStep.result s).flags t ok
    have e : PspriteStep.result s=⟨(PspriteStep.result s).core,(PspriteStep.result s).flags,0x2d040⟩ := by rw [←expires]
    rw [←e] at b
    exact ⟨n+m,by omega,E1M1PspriteStep.prefix_trans a b⟩
  · have e := Option.some.inj ok
    rw [←e]
    exact ⟨n,by omega,a⟩


private theorem loop_path {stops n s t}
    (run : X86Routine.run PspriteLoop.program stops n s=some t) :
    ∃ k, k ≤ n ∧ X86CodeMemory.Prefix FloorCaller.cm program [] k s t := by
  obtain ⟨k,hk,p,_⟩ := X86Routine.run_path run
  exact ⟨k,hk,(X86CodeMemory.lift_success p FloorCaller.cm).transfer program [] contains_tail (by simp)⟩

def finished := E1M1PspriteChain.finished

theorem finish_execution (s : X86Control.State) (pc : s.pc=0x2dc95)
    (flashIndex : s.core.regs 6=(1#32)) :
    ∃ n, n ≤ 14 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n s (finished s) := by
  obtain ⟨n,hn,p⟩ := E1M1PspriteChain.finish_execution s pc flashIndex
  exact ⟨n,hn,p.transfer program [] contains_prior (by simp)⟩

def suffix (fuel : Nat) (s : X86Control.State) : Option X86Control.State := do
  let t ← slot fuel (PspriteLoop.advanced s.core).core
  if t.pc=0x2dc95 ∧ t.core.regs 6=(1#32) then some (finished t) else none

theorem suffix_execution (fuel : Nat) (s t : X86Control.State)
    (pc : s.pc=0x2dc95) (weaponIndex : s.core.regs 6=(0#32))
    (ok : suffix fuel s=some t) :
    ∃ n, n ≤ 32*fuel+46 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n s t := by
  obtain ⟨n,hn,a⟩ := loop_path (PspriteLoop.advance_execution s.core s.flags)
  have e : s=⟨s.core,s.flags,0x2dc95⟩ := by rw [←pc]
  rw [←e] at a
  let u := PspriteLoop.advanced s.core
  have e2 : u=⟨u.core,u.flags,0x2dc6f⟩ := by
    change PspriteLoop.advanced s.core=_
    have h : (PspriteLoop.advanced s.core).pc=0x2dc6f := by simp [PspriteLoop.advanced,weaponIndex]
    rw [←h]
  cases result : slot fuel u.core with
  | none => simp [suffix,show slot fuel (PspriteLoop.advanced s.core).core=none from result] at ok
  | some v =>
    obtain ⟨m,hm,b⟩ := slot_execution fuel u.core u.flags v result
    rw [←e2] at b
    simp only [suffix,show slot fuel (PspriteLoop.advanced s.core).core=some v from result,Bind.bind,Option.bind] at ok
    split at ok
    · rename_i good
      obtain ⟨j,hj,c⟩ := finish_execution v good.1 good.2
      have out := Option.some.inj ok
      rw [out] at c
      exact ⟨n+m+j,by omega,E1M1PspriteStep.prefix_trans (E1M1PspriteStep.prefix_trans a b) c⟩
    · cases ok

end Doom.Proofs.E1M1PspriteLight
