import Doom.Proofs.OriginalMoveMotion
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 3200000
namespace Doom.Proofs
open Verification X86 X86Memory X86Control BlockSummary

/-- Retain registers and flags as well as the already-proved motion memory. -/
def motionSideEnd (s : X86Memory.State) : X86Control.State :=
  if sideGuardResult s = 16 then ⟨sideEnd (sideGuardCore s),none,213⟩
  else shiftState 120 (sideGuardEnd s)

theorem motion_side_full (s : X86Memory.State) (flags : Option Flags) :
    runProgram (decodeAt moveMotionBytes) [213] 29 ⟨s,flags,120⟩ = some (motionSideEnd s) := by
  have shifted := runProgram_shift sideGuardProgram side_guard_forward 120 [16,93] 5 ⟨s,flags,0⟩
  rw [side_guard_full] at shifted
  obtain ⟨k,hk,path,_⟩ := runProgram_path shifted
  have path := path.transfer (decodeAt moveMotionBytes) [213] motion_contains_guard motion_guard_active
  have tail : runProgram (decodeAt moveMotionBytes) [213] 24 (shiftState 120 (sideGuardEnd s)) = some (motionSideEnd s) := by
    by_cases hs : sideGuardResult s = 16
    · have eq : shiftState 120 (sideGuardEnd s) =
          ⟨sideGuardCore s,(sideGuardEnd s).flags,136⟩ := by simp [shiftState,sideGuardEnd,hs]
      rw [eq,show 24 = 24 + 0 by rfl,(side_linear_motion _ _).run 0]
      simp [runProgram,motionSideEnd,hs,side_end_memory]
    · have he : sideGuardResult s = 93 := by
        unfold sideGuardResult at *; split at * <;> simp_all
      simp [shiftState,sideGuardEnd,he,runProgram,motionSideEnd,sideGuardCore]
  exact path.finish tail 29 (by omega)


def motionEnd (s : X86Memory.State) (body : Motion) (cmd : Ticcmd) : X86Control.State :=
  motionSideEnd (afterForward s body cmd)

theorem motion_full_run (s : X86Memory.State) (flags : Option Flags) (body : Motion) (cmd : Ticcmd)
    (h : MoveEntryInputs s body cmd) :
    X86Control.run moveMotionBytes [213] 69 ⟨s,flags,0⟩ = some (motionEnd s body cmd) := by
  obtain ⟨k,hk,path,_⟩ := runProgram_path (move_entry_full s flags)
  have path := path.transfer (decodeAt moveMotionBytes) [213] motion_contains_entry motion_entry_active
  have hp := entry_pc s body cmd h
  have tail : runProgram (decodeAt moveMotionBytes) [213] 52 (moveEntryEnd s) = some (motionEnd s body cmd) := by
    by_cases hf : body.onGround ∧ cmd.forwardMove ≠ 0
    · rw [if_pos hf] at hp
      have eq : moveEntryEnd s = ⟨(moveEntryEnd s).core,(moveEntryEnd s).flags,48⟩ := by rw [←hp]
      rw [eq,show 52 = 23 + 29 by rfl,(forward_linear_motion _ _).run 29,motion_side_full]
      simp [motionEnd,afterForward,hf]
    · rw [if_neg hf] at hp
      have eq : moveEntryEnd s = ⟨(moveEntryEnd s).core,(moveEntryEnd s).flags,120⟩ := by rw [←hp]
      rw [eq]
      simpa [motionEnd,afterForward,hf] using runProgram_mono (motion_side_full (moveEntryEnd s).core (moveEntryEnd s).flags) 23
  exact path.finish tail 69 (by omega)


theorem motion_end_memory_pc (s : X86Memory.State) (flags : Option Flags)
    (body : Motion) (cmd : Ticcmd) (h : MoveMotionInputs s body cmd) :
    (motionEnd s body cmd).pc = 213 ∧
    (motionEnd s body cmd).core.memory = moveMotionResultMemory s body cmd := by
  have result := move_motion_matches_engine s flags body cmd h
  rw [motion_full_run s flags body cmd h.toMoveEntryInputs] at result
  simpa using result

theorem side_end_pointers (s : X86Memory.State) :
    (sideEnd s).regs 1 = s.regs 1 ∧ (sideEnd s).regs 6 = s.regs 6 ∧ (sideEnd s).regs 4 = s.regs 4 := by
  constructor
  · simp only [sideEnd,summarized_correct]
    summarize_x86 sideThrustOps
  · constructor <;> simp only [sideEnd,summarized_correct]
    all_goals summarize_x86 sideThrustOps

theorem motion_end_pointers (s : X86Memory.State) (body : Motion) (cmd : Ticcmd) :
    (motionEnd s body cmd).core.regs 1 = s.regs 0 ∧
    (motionEnd s body cmd).core.regs 6 = s.regs 0+(8#32) ∧
    (motionEnd s body cmd).core.regs 4 = s.regs 4 := by
  unfold motionEnd motionSideEnd
  split <;> simp only [side_end_pointers,shiftState,sideGuardEnd,sideGuardCore,write,
    show (1 : Reg) ≠ 2 by decide,show (6 : Reg) ≠ 2 by decide,show (4 : Reg) ≠ 2 by decide,↓reduceIte]
  all_goals exact after_forward_pointers s body cmd

end Doom.Proofs
