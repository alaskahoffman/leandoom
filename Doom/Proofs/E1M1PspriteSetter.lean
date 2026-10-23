import Doom.Proofs.OriginalPspriteSetter
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace Doom.Proofs.E1M1PspriteSetter
open Verification X86 X86Memory X86Control BlockSummary

/-- The setter is already present in the earlier weapon-lowering byte chain. -/
def program := E1M1PspriteLoop.program

theorem contains_setter (pc : Nat) (h : PspriteSetter.program pc≠none) :
    program pc=PspriteSetter.program pc := by
  by_cases inside : 0x2d040 ≤ pc ∧ pc < 0x2d0af
  · have checked : ∀ i : Fin 111, program (0x2d040+i.val)=PspriteSetter.program (0x2d040+i.val) := by decide
    have e : 0x2d040+(pc-0x2d040)=pc := by omega
    simpa only [e] using checked ⟨pc-0x2d040,by omega⟩
  · exact False.elim (h (by simp [PspriteSetter.program,PspriteSetter.bytesProgram,inside]))

private theorem lift {n s t} (p : X86Routine.Prefix PspriteSetter.program [] n s t) :
    X86CodeMemory.Prefix FloorCaller.cm program [] n s t :=
  (X86CodeMemory.lift_success p FloorCaller.cm).transfer program [] contains_setter (by simp)

private theorem path {stops n s t}
    (run : X86Routine.run PspriteSetter.program stops n s=some t) :
    ∃ k, k ≤ n ∧ X86CodeMemory.Prefix FloorCaller.cm program [] k s t := by
  obtain ⟨k,hk,p,_⟩ := X86Routine.run_path run
  exact ⟨k,hk,lift (p.transfer PspriteSetter.program [] (by intros; rfl) (by simp))⟩

def removed (s : X86Memory.State) :=
  PspriteSetter.returned (PspriteSetter.cleared (PspriteSetter.prepared s)) (some (logical32 0))

/-- S_NULL performs the real clear and returns. No action or return is stubbed. -/
theorem remove_execution (s : X86Memory.State) (f : Option Flags) (null : s.regs 3= (0#32)) :
    ∃ n, n ≤ 13 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2d040⟩ (removed s) := by
  obtain ⟨n,hn,p⟩ := path (PspriteSetter.entry_execution s f)
  have e : PspriteSetter.entered s=⟨PspriteSetter.prepared s,some (logical32 0),0x2d055⟩ := by
    simp [PspriteSetter.entered,null]
  rw [e] at p
  exact ⟨n+4,by omega,E1M1PspriteStep.prefix_trans p (lift (PspriteSetter.clear_execution _ _))⟩

def positioned (s : X86Memory.State) : X86Control.State :=
  let t := PspriteSetter.installed s none
  if t.core.regs 2= (0#32) then ⟨t.core,some (logical32 0),0x2d088⟩
  else PspriteSetter.coordinates t.core (some (logical32 (t.core.regs 2)))

theorem position_execution (s : X86Memory.State) (f : Option Flags) :
    ∃ n, n ≤ 15 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2d05e⟩ (positioned s) := by
  let t := PspriteSetter.installed s f
  have a := lift (PspriteSetter.installed_execution s f)
  obtain ⟨n,hn,b⟩ := path (PspriteSetter.coordinateGate_execution t.core t.flags)
  have e : t=⟨t.core,t.flags,0x2d073⟩ := rfl
  change X86CodeMemory.Prefix _ _ _ _ _ t at a
  rw [←e] at b
  have ab := E1M1PspriteStep.prefix_trans a b
  by_cases zero : t.core.regs 2= (0#32)
  · refine ⟨7+n,by omega,?_⟩
    have endpoint : PspriteSetter.coordinateGate t.core=positioned s := by
      change ⟨t.core,some (logical32 (t.core.regs 2)),if t.core.regs 2= (0#32) then 0x2d088 else 0x2d077⟩=
        (if t.core.regs 2= (0#32) then ⟨t.core,some (logical32 0),0x2d088⟩ else PspriteSetter.coordinates t.core (some (logical32 (t.core.regs 2))))
      simp only [zero,↓reduceIte,BitVec.ofNat_eq_ofNat]
    rw [←endpoint]; exact ab
  · have endPC : PspriteSetter.coordinateGate t.core=
        ⟨t.core,some (logical32 (t.core.regs 2)),0x2d077⟩ := by simp [PspriteSetter.coordinateGate,zero]
    rw [endPC] at ab
    have c := lift (PspriteSetter.coordinates_execution t.core (some (logical32 (t.core.regs 2))))
    refine ⟨7+n+6,by omega,?_⟩
    have h := E1M1PspriteStep.prefix_trans ab c
    have endpoint : positioned s=PspriteSetter.coordinates t.core (some (logical32 (t.core.regs 2))) := by
      change (if t.core.regs 2= (0#32) then _ else _)=_
      exact if_neg zero
    rw [endpoint]; exact h

def dispatched (s : X86Memory.State) : X86Control.State :=
  let t := positioned s
  let gate := PspriteSetter.actionGate t.core
  if load32 t.core.memory (t.core.regs 1+(12#32))= (0#32) then gate
  else PspriteSetter.called t.core gate.flags

/-- A general state install up to the actual indirect action entry, or the
successor read when there is no action. Includes optional x/y assignment. -/
theorem dispatch_execution (s : X86Memory.State) (f : Option Flags) :
    ∃ n, n ≤ 20 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2d05e⟩ (dispatched s) := by
  obtain ⟨n,hn,a⟩ := position_execution s f
  let t := positioned s
  have e : t=⟨t.core,t.flags,0x2d088⟩ := by
    dsimp [t,positioned]; split <;> rfl
  obtain ⟨m,hm,b⟩ := path (PspriteSetter.actionGate_execution t.core t.flags)
  rw [←e] at b
  have ab := E1M1PspriteStep.prefix_trans a b
  by_cases zero : load32 t.core.memory (t.core.regs 1+(12#32))= (0#32)
  · have endpoint : dispatched s=PspriteSetter.actionGate t.core := by
      change (if load32 t.core.memory (t.core.regs 1+12)= (0#32) then _ else _)=_
      exact if_pos zero
    exact ⟨n+m,by omega,by rw [endpoint]; exact ab⟩
  · have gate : PspriteSetter.actionGate t.core=⟨t.core,(PspriteSetter.actionGate t.core).flags,0x2d08e⟩ := by
      simp [PspriteSetter.actionGate,zero]
    rw [gate] at ab
    have c := lift (PspriteSetter.called_execution t.core (PspriteSetter.actionGate t.core).flags)
    have endpoint : dispatched s=PspriteSetter.called t.core (PspriteSetter.actionGate t.core).flags := by
      change (if load32 t.core.memory (t.core.regs 1+12)= (0#32) then _ else _)=_
      exact if_neg zero
    exact ⟨n+m+3,by omega,by rw [endpoint]; exact E1M1PspriteStep.prefix_trans ab c⟩

/-- The successor is read after the action. Zero-tic states loop to removal
or installation; nonzero timers reach the return epilogue. -/
def resumed (s : X86Memory.State) : X86Control.State :=
  if load32 s.memory (s.regs 3)= (0#32) then PspriteSetter.afterAction s
  else PspriteSetter.next (PspriteSetter.successor s none).core

theorem resume_execution (s : X86Memory.State) (f : Option Flags) :
    ∃ n, n ≤ 10 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2d095⟩ (resumed s) := by
  obtain ⟨n,hn,a⟩ := path (PspriteSetter.afterAction_execution s f)
  by_cases zero : load32 s.memory (s.regs 3)= (0#32)
  · exact ⟨n,by omega,by simpa [resumed,zero] using a⟩
  · have gate : PspriteSetter.afterAction s=⟨s,(PspriteSetter.afterAction s).flags,0x2d09a⟩ := by
      simp [PspriteSetter.afterAction,zero]
    rw [gate] at a
    have b := lift (PspriteSetter.successor_execution s (PspriteSetter.afterAction s).flags)
    let t := PspriteSetter.successor s (PspriteSetter.afterAction s).flags
    obtain ⟨m,hm,c⟩ := path (PspriteSetter.next_execution t.core t.flags)
    have e : t=⟨t.core,t.flags,0x2d0a2⟩ := rfl
    rw [←e] at c
    have endpoint : resumed s=PspriteSetter.next t.core := by
      change (if load32 s.memory (s.regs 3)= (0#32) then _ else _)=_
      exact if_neg zero
    exact ⟨n+3+m,by omega,by rw [endpoint]; exact E1M1PspriteStep.prefix_trans (E1M1PspriteStep.prefix_trans a b) c⟩


def setterResult (s : X86Memory.State) : X86Control.State :=
  if s.regs 3=(0#32) then removed s else dispatched (PspriteSetter.prepared s)

/-- From the actual setter entry through either S_NULL and RET, or the installed
state's action dispatch. Callback execution is a separate obligation. -/
theorem setter_execution (s : X86Memory.State) (f : Option Flags) :
    ∃ n, n ≤ 29 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2d040⟩ (setterResult s) := by
  by_cases null : s.regs 3=(0#32)
  · obtain ⟨n,hn,p⟩ := remove_execution s f null
    exact ⟨n,by omega,by simpa only [setterResult,if_pos null] using p⟩
  · obtain ⟨n,hn,a⟩ := path (PspriteSetter.entry_execution s f)
    have e : PspriteSetter.entered s=⟨PspriteSetter.prepared s,some (logical32 (s.regs 3)),0x2d05e⟩ := by
      simp [PspriteSetter.entered,null]
    rw [e] at a
    obtain ⟨m,hm,b⟩ := dispatch_execution (PspriteSetter.prepared s) (some (logical32 (s.regs 3)))
    exact ⟨n+m,by omega,by simpa only [setterResult,if_neg null] using E1M1PspriteStep.prefix_trans a b⟩

def slotResult (s : X86Memory.State) : X86Control.State :=
  let t := PspriteStep.result s
  if t.pc=0x2d040 then setterResult t.core else t

/-- Join an arbitrary slot countdown with the real setter entry, preserving
all machine state at the CALL. Expiration no longer stops before installation. -/
theorem slot_execution (s : X86Memory.State) (f : Option Flags) :
    ∃ n, n ≤ 44 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2dc6f⟩ (slotResult s) := by
  obtain ⟨n,hn,a,_⟩ := X86Routine.run_path (PspriteStep.slot_execution s f)
  have a := (X86CodeMemory.lift_success a FloorCaller.cm).transfer program [] E1M1PspriteLoop.contains_slot (by simp)
  by_cases expires : (PspriteStep.result s).pc=0x2d040
  · have e : PspriteStep.result s=⟨(PspriteStep.result s).core,(PspriteStep.result s).flags,0x2d040⟩ := by rw [←expires]
    obtain ⟨m,hm,b⟩ := setter_execution (PspriteStep.result s).core (PspriteStep.result s).flags
    rw [←e] at b
    exact ⟨n+m,by omega,by simpa only [slotResult,if_pos expires] using E1M1PspriteStep.prefix_trans a b⟩
  · exact ⟨n,by omega,by simpa only [slotResult,if_neg expires] using a⟩

end Doom.Proofs.E1M1PspriteSetter
