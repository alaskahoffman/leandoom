import Doom.Proofs.OriginalGroupEntry
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalGroupHandoff
open Verification X86 X86Memory X86Control BlockSummary

def program : X86Routine.Program := fun pc =>
  if 0x39731≤pc ∧ pc<0x39776 then OriginalGroupAllocation.program pc else OriginalGroupEntry.program pc

theorem allocation_agrees (pc : Nat) (h : OriginalGroupAllocation.program pc≠none) :
    program pc=OriginalGroupAllocation.program pc := by
  have inside : 0x39731≤pc ∧ pc<0x39776 := by
    by_cases yes : 0x39731≤pc ∧ pc<0x39776
    · exact yes
    · simp [OriginalGroupAllocation.program,OriginalGroupAllocation.bytesProgram,yes] at h
  simp [program,inside]
theorem entry_agrees (pc : Nat) (h : OriginalGroupEntry.program pc≠none) :
    program pc=OriginalGroupEntry.program pc := by
  have outside : ¬(0x39731≤pc ∧ pc<0x39776) := by
    intro inside
    have a : ¬(0x2e63e≤pc ∧ pc<0x2e661) := by omega
    have b : ¬(0x241c0≤pc ∧ pc<0x241dc) := by omega
    simp [OriginalGroupEntry.program,OriginalGroupEntry.bytesProgram,a,b] at h
  simp [program,outside]

def result (s : X86Memory.State) := OriginalGroupEntry.result (OriginalGroupAllocation.returned s).core

theorem execution (s : X86Memory.State) (f : Option Flags)
    (user : s.regs 7=(0#32)) (tag : s.regs 5=(50#32))
    (safe : OriginalGroupAllocation.SafeWord (s.regs 4+16) s)
    (ret : load32 s.memory (s.regs 4+16)=0x2e63e) :
    X86Routine.run program [0x2e661,0x2e791] 34 ⟨s,f,0x39731⟩=some (result s) := by
  obtain ⟨n,hn,path,_⟩ := X86Routine.run_path (OriginalGroupAllocation.from_initial s f user tag safe ret)
  have path := path.transfer program [0x2e661,0x2e791] allocation_agrees (by
    intro pc h member
    simp at member
    rcases member with rfl|rfl <;> exact h (by decide))
  have tail := OriginalGroupEntry.execution (OriginalGroupAllocation.returned s).core (OriginalGroupAllocation.returned s).flags
  have eta : (⟨(OriginalGroupAllocation.returned s).core,(OriginalGroupAllocation.returned s).flags,0x2e63e⟩ : X86Control.State)=OriginalGroupAllocation.returned s := by
    rw [←OriginalGroupAllocation.return_pc s safe ret]
  rw [eta] at tail
  rw [←X86Routine.run_sound program OriginalGroupEntry.program entry_agrees _ _ _ (by rw [tail]; simp)] at tail
  exact path.finish tail _ (by omega)

/-- Finite write separation at the selected-block boundary. No claim is made
here that the preceding heap search/split has already established it. -/
def SafeWord (a : Word) (s : X86Memory.State) : Prop :=
  OriginalGroupAllocation.SafeWord a s ∧ OriginalGroupEntry.SafeWord a (s.regs 4+20)

theorem frame (s : X86Memory.State) (a : Word) (safe : SafeWord a s) :
    load32 (result s).core.memory a=load32 s.memory a := by
  have later := OriginalGroupEntry.frame (OriginalGroupAllocation.returned s).core a
    (by rw [(OriginalGroupAllocation.returned_registers s).2]; exact safe.2)
  exact later.trans (OriginalGroupAllocation.returned_frame s a safe.1)

theorem registers (s : X86Memory.State) (sectorSafe : OriginalGroupAllocation.SafeWord 0x2c148 s) :
    (result s).core.regs 5=load32 s.memory 0x2c148 ∧
    (result s).core.regs 6=s.regs 3+24 ∧ (result s).core.regs 4=s.regs 4+20 := by
  obtain ⟨owner,array,stack⟩ := OriginalGroupEntry.registers (OriginalGroupAllocation.returned s).core
  exact ⟨owner.trans (OriginalGroupAllocation.returned_frame s _ sectorSafe),
    array.trans (OriginalGroupAllocation.returned_registers s).1,
    stack.trans (OriginalGroupAllocation.returned_registers s).2⟩

theorem positive_pc (s : X86Memory.State) (countSafe : OriginalGroupAllocation.SafeWord 0x2c14c s)
    (positive : 0<(load32 s.memory 0x2c14c).toInt) : (result s).pc=0x2e661 := by
  apply OriginalGroupEntry.positive_pc
  change 0<(load32 (OriginalGroupAllocation.returned s).core.memory 0x2c14c).toInt
  rw [OriginalGroupAllocation.returned_frame s _ countSafe]; exact positive

theorem inputs (es : List OriginalGroupOutput.Line) (s : X86Memory.State)
    (before : OriginalGroupOutput.Inputs es s.memory)
    (safe : ∀ e∈es, SafeWord (e.address+46) s ∧ SafeWord (e.address+50) s) :
    OriginalGroupOutput.Inputs es (result s).core.memory := by
  intro e he
  exact ⟨(frame s _ (safe e he).1).trans (before e he).1,
    (frame s _ (safe e he).2).trans (before e he).2⟩

/-- Preserve any already-proved count, including the counting-loop postcondition. -/
theorem count_field (s : X86Memory.State) (sector value : Word)
    (before : load32 s.memory (sector+78)=value) (safe : SafeWord (sector+78) s) :
    load32 (result s).core.memory (sector+78)=value := (frame s _ safe).trans before

end Doom.Proofs.OriginalGroupHandoff
