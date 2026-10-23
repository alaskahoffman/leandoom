import Doom.Proofs.OriginalGroupSplit
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000
namespace Doom.Proofs.OriginalGroupSelected
open Verification X86 X86Memory X86Control BlockSummary

def picked (s : X86Memory.State) := put s 0 (OriginalGroupSplit.candidateSize s)
def allocated (s : X86Memory.State) := OriginalGroupSplit.result (picked s)
def result (s : X86Memory.State) := OriginalGroupHandoff.result (allocated s).core

def program : X86Routine.Program := fun pc =>
  if 0x396f8≤pc ∧ pc<0x39731 then OriginalGroupSplit.program pc else OriginalGroupHandoff.program pc

theorem split_agrees (pc : Nat) (h : OriginalGroupSplit.program pc≠none) :
    program pc=OriginalGroupSplit.program pc := by
  by_cases yes : 0x396f8≤pc ∧ pc<0x39731
  · simp [program,yes]
  · simp [OriginalGroupSplit.program,OriginalGroupSplit.bytesProgram,yes] at h

theorem handoff_agrees (pc : Nat) (h : OriginalGroupHandoff.program pc≠none) :
    program pc=OriginalGroupHandoff.program pc := by
  by_cases yes : 0x396f8≤pc ∧ pc<0x39731
  · have a : ¬(0x39731≤pc ∧ pc<0x39776) := by omega
    have b : ¬(0x2e63e≤pc ∧ pc<0x2e661) := by omega
    have c : ¬(0x241c0≤pc ∧ pc<0x241dc) := by omega
    simp [OriginalGroupHandoff.program,a,OriginalGroupEntry.program,OriginalGroupEntry.bytesProgram,b,c] at h
  · simp [program,yes]

theorem picked_candidate (s : X86Memory.State)
    (free : load32 s.memory (s.regs 3+(4#32))=(0#32))
    (fits : (s.regs 1).toInt≤(OriginalGroupSplit.candidateSize s).toInt) :
    OriginalGroupSplit.candidate s=
      ⟨picked s,some (compare32 (s.regs 1) (OriginalGroupSplit.candidateSize s)),0x39704⟩ := by
  simp [OriginalGroupSplit.candidate,picked,free,show ¬(OriginalGroupSplit.candidateSize s).toInt<(s.regs 1).toInt by omega]

theorem selected_execution (s : X86Memory.State) (f : Option Flags)
    (free : load32 s.memory (s.regs 3+(4#32))=(0#32))
    (fits : (s.regs 1).toInt≤(OriginalGroupSplit.candidateSize s).toInt) :
    X86Routine.run OriginalGroupSplit.program [0x39731] 19 ⟨s,f,0x396f8⟩=some (allocated s) := by
  have gate := OriginalGroupSplit.candidate_execution s f
  rw [picked_candidate s free fits] at gate
  obtain ⟨n,hn,path,_⟩ := X86Routine.run_path gate
  have path := path.transfer OriginalGroupSplit.program [0x39731] (by intros; rfl) (by
    intro pc h member
    simp only [List.mem_singleton] at member
    subst pc
    exact h (by decide))
  exact path.finish (OriginalGroupSplit.execution (picked s) _) 19 (by omega)

theorem allocated_registers (s : X86Memory.State) (r : Reg) (h0 : r≠0) (h2 : r≠2) :
    (allocated s).core.regs r=s.regs r := by
  unfold allocated
  rw [OriginalGroupSplit.registers _ r h0 h2]
  simp [picked,put,write,h0]

theorem allocated_frame (s : X86Memory.State) (a : Word)
    (safe : OriginalGroupSplit.SafeWord a (picked s)) :
    load32 (allocated s).core.memory a=load32 s.memory a := OriginalGroupSplit.frame (picked s) a safe

/-- Static footprint conditions on the initial state and its explicitly computed
split summary. No successful execution or post-execution memory is a premise. -/
def SafeWord (a : Word) (s : X86Memory.State) : Prop :=
  OriginalGroupSplit.SafeWord a (picked s) ∧ OriginalGroupHandoff.SafeWord a (allocated s).core

/-- The saved allocator return must survive only until its RET. The caller
subsequently reuses that exact stack slot for M_ClearBox's return address. -/
def ReturnSafe (s : X86Memory.State) : Prop :=
  OriginalGroupSplit.SafeWord (s.regs 4+16) (picked s) ∧
    OriginalGroupAllocation.SafeWord (s.regs 4+16) (allocated s).core

theorem execution (s : X86Memory.State) (f : Option Flags)
    (free : load32 s.memory (s.regs 3+(4#32))=(0#32))
    (fits : (s.regs 1).toInt≤(OriginalGroupSplit.candidateSize s).toInt)
    (user : s.regs 7=(0#32)) (tag : s.regs 5=(50#32))
    (safe : ReturnSafe s)
    (ret : load32 s.memory (s.regs 4+16)=0x2e63e) :
    X86Routine.run program [0x2e661,0x2e791] 53 ⟨s,f,0x396f8⟩=some (result s) := by
  obtain ⟨n,hn,path,_⟩ := X86Routine.run_path (selected_execution s f free fits)
  have path := path.transfer program [0x2e661,0x2e791] split_agrees (by
    intro pc h member
    simp at member
    rcases member with rfl|rfl <;> exact h (by decide))
  have sp := allocated_registers s 4 (by decide) (by decide)
  have tail := OriginalGroupHandoff.execution (allocated s).core (allocated s).flags
    ((allocated_registers s 7 (by decide) (by decide)).trans user)
    ((allocated_registers s 5 (by decide) (by decide)).trans tag)
    (by rw [sp]; exact safe.2)
    (by rw [sp]; exact (allocated_frame s _ safe.1).trans ret)
  have eta : (⟨(allocated s).core,(allocated s).flags,0x39731⟩ : X86Control.State)=allocated s := by
    rw [←OriginalGroupSplit.result_pc (picked s)]
    rfl
  rw [eta] at tail
  rw [←X86Routine.run_sound program OriginalGroupHandoff.program handoff_agrees _ _ _ (by rw [tail]; simp)] at tail
  exact path.finish tail 53 (by omega)

theorem frame (s : X86Memory.State) (a : Word) (safe : SafeWord a s) :
    load32 (result s).core.memory a=load32 s.memory a :=
  (OriginalGroupHandoff.frame (allocated s).core a safe.2).trans (allocated_frame s a safe.1)

theorem inputs (es : List OriginalGroupOutput.Line) (s : X86Memory.State)
    (before : OriginalGroupOutput.Inputs es s.memory)
    (safe : ∀ e∈es, SafeWord (e.address+46) s ∧ SafeWord (e.address+50) s) :
    OriginalGroupOutput.Inputs es (result s).core.memory := by
  intro e he
  exact ⟨(frame s _ (safe e he).1).trans (before e he).1,
    (frame s _ (safe e he).2).trans (before e he).2⟩

theorem count_field (s : X86Memory.State) (sector value : Word)
    (before : load32 s.memory (sector+78)=value) (safe : SafeWord (sector+78) s) :
    load32 (result s).core.memory (sector+78)=value := (frame s _ safe).trans before
end Doom.Proofs.OriginalGroupSelected
