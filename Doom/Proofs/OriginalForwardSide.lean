import Doom.Proofs.OriginalInlineThrust
import Doom.Proofs.OriginalMoveEntry
import Doom.Verification.X86Linear

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

namespace Doom.Proofs
open Verification X86 X86Memory X86Control BlockSummary

def forwardSideBytes := Doom19.forwardThrustBytes ++ Doom19.sideGuardBytes
def forwardPackets := (decodePackets 23 Doom19.forwardThrustBytes).getD []
def forwardEnd (s : X86Memory.State) : X86Memory.State := X86Block.eval forwardThrustOps s

theorem forward_packets_ops : forwardPackets.map Prod.fst = forwardThrustOps := by rfl

theorem forward_linear_prefix (s : X86Memory.State) (flags : Option Flags) :
    Prefix (decodeAt forwardSideBytes) [88, 165] 23 ⟨s, flags, 0⟩ ⟨forwardEnd s, none, 72⟩ := by
  have fits : LinearFits (decodeAt forwardSideBytes) [88, 165] 0 forwardPackets := by decide
  have path := linear_prefix forwardPackets (decodeAt forwardSideBytes) [88, 165] ⟨s, flags, 0⟩ fits
  rw [linear_state, forward_packets_ops] at path
  exact path

theorem forward_end_memory (s : X86Memory.State) :
    (forwardEnd s).memory = inlineThrustMemory s false := by
  have h := original_forward_thrust_memory s
  simpa only [X86Block.run, forward_thrust_decoded, Option.map_some, Option.some.injEq, forwardEnd] using h

theorem forward_end_pointers (s : X86Memory.State) :
    (forwardEnd s).regs 1 = s.regs 1 ∧ (forwardEnd s).regs 6 = s.regs 6 := by
  constructor <;> simp only [forwardEnd, summarized_correct]
  all_goals
    conv => lhs; pattern (forwardThrustOps); reduce
    simp [summarized, X86Block.execute, X86Memory.execute, X86.execute,
      X86Block.Address.eval, put, multiply, write, eax, ebx, edx]

theorem side_guard_forward (pc : Nat) (op : X86Control.Op) (len : Nat)
    (h : sideGuardProgram pc = some (op, len)) : ForwardOp op := by
  fun_cases sideGuardProgram pc <;> simp_all [sideGuardProgram]
  all_goals rcases h with ⟨rfl, rfl⟩; simp [ForwardOp]

theorem forward_side_contains_guard (pc : Nat)
    (h : shiftProgram 72 sideGuardProgram pc ≠ none) :
    decodeAt forwardSideBytes pc = shiftProgram 72 sideGuardProgram pc := by
  have hp : 72 ≤ pc := by
    by_cases hp : 72 ≤ pc
    · exact hp
    · simp [shiftProgram, hp] at h
  have cases : pc = 72 ∨ pc = 75 ∨ pc = 77 ∨ pc = 79 ∨ pc = 86 := by
    simp only [shiftProgram, hp, ↓reduceIte] at h
    generalize he : pc - 72 = localPC at h
    fun_cases sideGuardProgram localPC <;> simp_all [sideGuardProgram] <;> omega
  rcases cases with h | h | h | h | h <;> subst pc <;> rfl

private theorem valid_map {α β : Type} {v : Option α} {f : α → β} {b : β}
    (h : v.map f = some b) : v ≠ none := by cases v <;> simp_all

/-- The skipped-forward path enters the same byte slice directly at its guard. -/
theorem original_skip_forward_side (s : X86Memory.State) (flags : Option Flags) :
    (X86Control.run forwardSideBytes [88, 165] 5 ⟨s, flags, 72⟩).map
      (fun t => (t.pc, t.core.memory)) = some (72 + sideGuardResult s, s.memory) := by
  have shifted := runProgram_shift sideGuardProgram side_guard_forward 72 [16, 93] 5 ⟨s, flags, 0⟩
  have valid := valid_map (side_guard_program s flags)
  have validShift : runProgram (shiftProgram 72 sideGuardProgram) [88, 165] 5 ⟨s, flags, 72⟩ ≠ none := by
    change runProgram (shiftProgram 72 sideGuardProgram) (List.map (72 + ·) [16, 93]) 5
      (shiftState 72 ⟨s, flags, 0⟩) ≠ none
    rw [shifted]
    simpa using valid
  unfold X86Control.run
  rw [runProgram_extend _ _ forward_side_contains_guard _ _ _ validShift]
  change (runProgram (shiftProgram 72 sideGuardProgram) (List.map (72 + ·) [16, 93]) 5
    (shiftState 72 ⟨s, flags, 0⟩)).map _ = _
  rw [shifted]
  have result := congrArg (Option.map (fun p : Nat × Memory => (72 + p.1, p.2))) (side_guard_program s flags)
  simpa [Option.map_map, Function.comp_def, shiftState] using result

/-- No fresh machine state is supplied to the side guard: it receives all
registers, memory and flags from the actual inlined forward instructions. -/
theorem original_forward_side (s : X86Memory.State) (flags : Option Flags) :
    (X86Control.run forwardSideBytes [88, 165] 28 ⟨s, flags, 0⟩).map
      (fun t => (t.pc, t.core.memory)) =
      some (72 + sideGuardResult (forwardEnd s), inlineThrustMemory s false) := by
  unfold X86Control.run
  rw [show 28 = 23 + 5 by rfl, (forward_linear_prefix s flags).run 5]
  change (X86Control.run forwardSideBytes [88,165] 5 ⟨forwardEnd s,none,72⟩).map _ = _
  rw [original_skip_forward_side, forward_end_memory]

/-- Extra live data read by the next guard, plus separation from all three
forward-thrust writes. Every premise describes memory before forward thrust. -/
structure ForwardSideInputs (s : X86Memory.State) (body : Motion) (cmd : Ticcmd) : Prop
    extends InlineThrustInputs s body false cmd.forwardMove where
  ground : load32 s.memory 0x2cf90 = if body.onGround then 1 else 0
  side : s.memory (s.regs 6 + (1#32)) = cmd.sideMove.toBitVec
  groundScratch : Apart 0x2cf90 (s.regs 4)
  groundMomx : Apart 0x2cf90 (load32 s.memory (s.regs 1) + 72)
  groundMomy : Apart 0x2cf90 (load32 s.memory (s.regs 1) + 76)
  sideScratch : Apart (s.regs 6 + (1#32)) (s.regs 4)
  sideMomx : Apart (s.regs 6 + (1#32)) (load32 s.memory (s.regs 1) + 72)
  sideMomy : Apart (s.regs 6 + (1#32)) (load32 s.memory (s.regs 1) + 76)

/-- Single-byte preservation follows from the shared byte-range invariant. -/
theorem byte_store_apart (m : Memory) (a b v : Word) (h : Apart b a) :
    store32 m a v b = m b := by
  have h0 := h 0 0; have h1 := h 0 1; have h2 := h 0 2; have h3 := h 0 3
  simp at h0 h1 h2 h3
  exact turn_store_preserves m a v b h0 h1 h2 h3

theorem forward_establishes_side_inputs (s : X86Memory.State) (body : Motion) (cmd : Ticcmd)
    (h : ForwardSideInputs s body cmd) :
    load32 (forwardEnd s).memory 0x2cf90 = (if body.onGround then 1 else 0) ∧
    (forwardEnd s).memory ((forwardEnd s).regs 6 + (1#32)) = cmd.sideMove.toBitVec := by
  rw [forward_end_memory, inline_thrust_matches_engine s body false cmd.forwardMove h.toInlineThrustInputs,
    (forward_end_pointers s).2]
  dsimp only [inlineThrustResult, inlineScratch]
  rw [load_store_apart _ _ _ _ h.groundMomy,
    load_store_apart _ _ _ _ h.groundMomx, load_store_apart _ _ _ _ h.groundScratch,
    byte_store_apart _ _ _ _ h.sideMomy, byte_store_apart _ _ _ _ h.sideMomx,
    byte_store_apart _ _ _ _ h.sideScratch]
  exact ⟨h.ground, h.side⟩

/-- Actual continuous forward-thrust/side-guard correspondence: final memory
contains engine momentum plus the original scratch word, and the next branch
uses the original cached ground flag and preserved side command. -/
theorem forward_side_matches_engine (s : X86Memory.State) (flags : Option Flags)
    (body : Motion) (cmd : Ticcmd) (h : ForwardSideInputs s body cmd) :
    (X86Control.run forwardSideBytes [88,165] 28 ⟨s,flags,0⟩).map
      (fun t => (t.pc, t.core.memory)) =
      some (if body.onGround ∧ cmd.sideMove ≠ 0 then 88 else 165,
        inlineThrustResult s body false cmd.forwardMove) := by
  have ⟨hg, hc⟩ := forward_establishes_side_inputs s body cmd h
  rw [original_forward_side, side_guard_matches_engine _ body cmd hg hc,
    inline_thrust_matches_engine s body false cmd.forwardMove h.toInlineThrustInputs]
  by_cases takeSide : body.onGround ∧ cmd.sideMove ≠ 0 <;> simp [takeSide]

/-- Skipping forward thrust preserves all memory while choosing the same side
branch. The previous entry proof decides which of these two entries is used;
linking its complete output relation to these premises remains a separate task. -/
theorem skip_forward_side_matches_engine (s : X86Memory.State) (flags : Option Flags)
    (body : Motion) (cmd : Ticcmd)
    (hg : load32 s.memory 0x2cf90 = if body.onGround then 1 else 0)
    (hc : s.memory (s.regs 6 + (1#32)) = cmd.sideMove.toBitVec) :
    (X86Control.run forwardSideBytes [88,165] 5 ⟨s,flags,72⟩).map
      (fun t => (t.pc,t.core.memory)) =
      some (if body.onGround ∧ cmd.sideMove ≠ 0 then 88 else 165, s.memory) := by
  rw [original_skip_forward_side, side_guard_matches_engine _ body cmd hg hc]
  by_cases takeSide : body.onGround ∧ cmd.sideMove ≠ 0 <;> simp [takeSide]

end Doom.Proofs
