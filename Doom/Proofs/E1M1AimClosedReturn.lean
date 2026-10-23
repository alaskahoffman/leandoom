import Doom.Proofs.E1M1AimBlockingSource
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
namespace Doom.Proofs.E1M1AimClosedReturn
open Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1AimRepeatProgram (program)
attribute [local irreducible] load32 store32

/-- All opening and guard bytes already belong to the repeated-callback program. -/
theorem contains_opening (pc : Nat) (h : E1M1AimOpening.program pc≠none) :
    program pc=E1M1AimOpening.program pc := by
  have a := E1M1AimDistance.contains_opening pc h
  have b := E1M1AimFloor.contains_distance pc (by rw [a]; exact h)
  have c := E1M1AimCeiling.contains_floor pc (by rw [b,a]; exact h)
  have d := E1M1AimWindow.contains_ceiling pc (by rw [c,b,a]; exact h)
  have e := E1M1AimResume.contains_window pc (by rw [d,c,b,a]; exact h)
  exact (E1M1AimRepeatProgram.contains_resume pc (by rw [e,d,c,b,a]; exact h)).trans
    (e.trans (d.trans (c.trans (b.trans a))))

theorem contains_guard (pc : Nat) (h : OriginalAimGuard.program pc≠none) :
    program pc=OriginalAimGuard.program pc := by
  have eq := E1M1AimOpening.contains_guard pc h
  exact (contains_opening pc (by rw [eq]; exact h)).trans eq

/-- The shared false-return epilogue restores six slots and pops the real return
address. It performs no memory writes and returns EAX = 0. -/
theorem stop_fields (s : X86Memory.State) :
    (OriginalAimGuard.stopped s).core.regs 0=0 ∧
    (OriginalAimGuard.stopped s).core.regs 4=s.regs 4+(28#32) ∧
    (OriginalAimGuard.stopped s).core.memory=s.memory ∧
    (OriginalAimGuard.stopped s).pc=(load32 s.memory (s.regs 4+(24#32))).toNat := by
  have fields := OriginalAimWindow.returned_fields s 0 (some (logical32 0))
  exact ⟨fields.1,fields.2.1,fields.2.2.1,fields.2.2.2.1⟩

/-- The caller's return address is protected by the existing layout invariant,
not supplied again at the reached epilogue. -/
theorem return_frame (s : X86Memory.State) (safe : E1M1AimReturnFrame.Safe s) :
    load32 (E1M1AimOpeningFrame.result s).core.memory (s.regs 4)=load32 s.memory (s.regs 4) := by
  apply E1M1AimOpeningFrame.output_frame
  intro a member
  simp only [E1M1AimOpeningFrame.writes,E1M1AimOpeningFrame.pushes,List.mem_append,
    List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with ((rfl|rfl|rfl|rfl|rfl|rfl|rfl)|(rfl|rfl|rfl|rfl))|member
  · exact E1M1AimWall.return_safe _ 4 (by simp)
  · exact E1M1AimWall.return_safe _ 8 (by simp)
  · exact E1M1AimWall.return_safe _ 12 (by simp)
  · exact E1M1AimWall.return_safe _ 16 (by simp)
  · exact E1M1AimWall.return_safe _ 20 (by simp)
  · exact E1M1AimWall.return_safe _ 24 (by simp)
  · simpa using E1M1AimReturnFrame.stack_apart (s.regs 4) 0 28 (by simp [E1M1AimReturnFrame.slots]) (by simp)
  · simpa using E1M1AimReturnFrame.stack_apart (s.regs 4) 0 32 (by simp [E1M1AimReturnFrame.slots]) (by simp)
  · simpa using E1M1AimReturnFrame.stack_apart (s.regs 4) 0 36 (by simp [E1M1AimReturnFrame.slots]) (by simp)
  · simpa using E1M1AimReturnFrame.stack_apart (s.regs 4) 0 40 (by simp [E1M1AimReturnFrame.slots]) (by simp)
  · simpa using E1M1AimReturnFrame.stack_apart (s.regs 4) 0 44 (by simp [E1M1AimReturnFrame.slots]) (by simp)
  · simpa using safe 0 (by simp [E1M1AimReturnFrame.slots]) a (List.mem_append_left _ member)

def returned (s : X86Memory.State) := OriginalAimGuard.stopped (E1M1AimOpeningFrame.result s).core
def result (s : X86Memory.State) := OriginalInterceptGate.resumed (returned s).core

/-- Execute a closed two-sided opening from callback entry through the actual
RET and the parent's false-return branch. No distance division is required. -/
theorem execution (s : X86Memory.State) (f : Option Flags) (hit : Intercept)
    (line front back ff fc bf bc : Word)
    (h : E1M1AimMapped.Inputs s hit line front back ff fc bf bc)
    (safe : E1M1AimReturnFrame.Safe s) (returnWord : load32 s.memory (s.regs 4)=0x2c86d)
    (closed : (if bc.toInt≤fc.toInt then bc else fc).toInt ≤
      (if ff.toInt≤bf.toInt then bf else ff).toInt) :
    (∃ n≤60, X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2b760⟩ (result s)) ∧
    (result s).pc=0x2c88c ∧ (result s).core.regs 0=0 ∧
    (result s).core.regs 4=s.regs 4+4 ∧
    (result s).core.memory=(E1M1AimOpeningFrame.result s).core.memory := by
  obtain ⟨⟨n,hn,run⟩,decision⟩ := E1M1AimMapped.execution s f hit line front back ff fc bf bc h
  have run := run.transfer program [] contains_opening (by simp)
  have atStop : (E1M1AimOpeningFrame.result s).pc=0x2b8d2 := by rw [decision,if_pos closed]
  have tail := (X86CodeMemory.lift_success (OriginalAimGuard.stop_execution
    (E1M1AimOpeningFrame.result s).core (E1M1AimOpeningFrame.result s).flags) FloorCaller.cm).transfer
    program [] contains_guard (by simp)
  rw [OriginalPathXStep.at_pc _ _ atStop] at tail
  have fields := stop_fields (E1M1AimOpeningFrame.result s).core
  have stack := (E1M1AimOpeningFrame.output_regs s h.helperSafe).2
  have pc : (returned s).pc=0x2c86d := by
    change (OriginalAimGuard.stopped (E1M1AimOpeningFrame.result s).core).pc=_
    rw [fields.2.2.2,stack,BitVec.sub_add_cancel,return_frame s safe,returnWord]
    rfl
  have parent := (X86CodeMemory.lift_success
    (OriginalInterceptGate.resume_execution (returned s).core (returned s).flags) FloorCaller.cm).transfer
    program [] E1M1AimRepeatProgram.contains_call (by simp)
  rw [OriginalPathXStep.at_pc _ _ pc] at parent
  have zero : (returned s).core.regs 0=0 := fields.1
  have count : OriginalInterceptGate.resumeSteps (returned s).core=4 := by
    simp only [OriginalInterceptGate.resumeSteps,zero,ite_true]
  rw [count] at parent
  refine ⟨⟨n+8+4,by omega,E1M1PspriteStep.prefix_trans (E1M1PspriteStep.prefix_trans run tail) parent⟩,?_,?_,?_,?_⟩
  · simp only [result,OriginalInterceptGate.resumed,zero,ite_true]
  · simp [result,OriginalInterceptGate.resumed,zero,OriginalInterceptGate.restored,put,write]
  · change (returned s).core.regs 4=_
    change (OriginalAimGuard.stopped (E1M1AimOpeningFrame.result s).core).core.regs 4=_
    rw [fields.2.1,stack]
    simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  · exact fields.2.2.1

/-- The early stop preserves words outside the opening helper's writes; the
parent does not sentinel-mark the selected fraction on this false branch. -/
theorem frame (s : X86Memory.State) (a : Word)
    (safe : ∀ b∈E1M1AimOpeningFrame.writes (s.regs 4), Apart a b) :
    load32 (result s).core.memory a=load32 s.memory a := by
  have fields := stop_fields (E1M1AimOpeningFrame.result s).core
  have zero : (returned s).core.regs 0=0 := fields.1
  simp only [result,OriginalInterceptGate.resumed,zero,ite_true]
  change load32 (returned s).core.memory a=_
  change load32 (OriginalAimGuard.stopped (E1M1AimOpeningFrame.result s).core).core.memory a=_
  rw [fields.2.2.1]
  exact E1M1AimOpeningFrame.output_frame s a safe

end Doom.Proofs.E1M1AimClosedReturn
