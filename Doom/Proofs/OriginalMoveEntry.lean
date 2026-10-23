import Doom.Proofs.OriginalMoveGuards
import Doom.Proofs.OriginalTurn
import Doom.Verification.X86Compose

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

namespace Doom.Proofs
open Verification X86 X86Memory X86Control BlockSummary

/-- Contiguous original bytes: turning immediately followed by the first guard. -/
def moveEntryBytes := Doom19.playerTurnBytes ++ Doom19.forwardGuardBytes

def moveEntryProgram : Program
  | 0 => some (.block (.legacy (.mov 1 0)), 2)
  | 2 => some (.block (.legacy (.lea 6 0 8)), 3)
  | 5 => some (.block (.legacy (.movsx16 3 6 2)), 4)
  | 9 => some (.block (.legacy (.load 0 0 0)), 2)
  | 11 => some (.block (.legacy (.shl 3 16)), 3)
  | 14 => some (.block (.legacy (.addMemory 0 3 32)), 3)
  | 17 => some (.block (.legacy (.load 0 1 0)), 2)
  | 19 => some (.block (.legacy (.load 3 0 20)), 3)
  | 22 => some (.cmpMemory 3 ⟨some 0, none, 0, 56⟩, 3)
  | 25 => some (.setle 0, 3)
  | 28 => some (.andEax 255, 5)
  | 33 => some (.loadByte 2 ⟨some 6, none, 0, 0⟩, 2)
  | 35 => some (.storeEax 0x2cf90, 5)
  | 40 => some (.testByte 2 2, 2)
  | 42 => some (.jumpZero true 76, 2)
  | 44 => some (.testWord 0 0, 2)
  | 46 => some (.jumpZero true 72, 2)
  | _ => none

theorem move_entry_decoded (pc : Nat) (h : moveEntryProgram pc ≠ none) :
    decodeAt moveEntryBytes pc = moveEntryProgram pc := by
  fun_cases moveEntryProgram pc <;> simp_all [moveEntryProgram] <;> rfl

/-- Complete state at the first seam; the original player pointer and command
pointer have been established by execution, not supplied as new assumptions. -/
def turnEndCore (s : X86Memory.State) : X86Memory.State :=
  let obj := load32 s.memory (s.regs eax)
  let turn := (load16 s.memory (s.regs eax + (10#32))).signExtend 32 <<< 16
  { regs := write (write (write (write (write s.regs ecx (s.regs eax)) esi (s.regs eax + (8#32)))
      ebx ((load16 s.memory (s.regs eax + (10#32))).signExtend 32)) eax obj) ebx turn
    memory := store32 s.memory (obj + (32#32)) (load32 s.memory (obj + (32#32)) + turn) }

theorem move_entry_turn_prefix (s : X86Memory.State) (flags : Option Flags) :
    Prefix moveEntryProgram [48, 120] 6 ⟨s, flags, 0⟩ ⟨turnEndCore s, none, 17⟩ := by
  apply Prefix.step (by simp) (by rfl) (by rfl)
  apply Prefix.step (by simp) (by rfl) (by rfl)
  apply Prefix.step (by simp) (by rfl) (by rfl)
  apply Prefix.step (by simp) (by rfl) (by rfl)
  apply Prefix.step (by simp) (by rfl) (by rfl)
  apply Prefix.step (by simp) (by rfl) (by rfl)
  simpa [turnEndCore, X86Control.execute, X86Block.execute, X86Memory.execute,
    blockPreservesFlags, put, write, eax, ebx, ecx, esi, BitVec.add_assoc] using
    (Prefix.nil (program := moveEntryProgram) (exits := [48, 120])
      (⟨turnEndCore s, none, 17⟩ : X86Control.State))

theorem forward_guard_forward (pc : Nat) (op : X86Control.Op) (len : Nat)
    (h : forwardGuardProgram pc = some (op, len)) : ForwardOp op := by
  fun_cases forwardGuardProgram pc <;> simp_all [forwardGuardProgram]
  all_goals rcases h with ⟨rfl, rfl⟩; simp [ForwardOp]

theorem move_entry_contains_guard (pc : Nat)
    (h : shiftProgram 17 forwardGuardProgram pc ≠ none) :
    moveEntryProgram pc = shiftProgram 17 forwardGuardProgram pc := by
  have hp : 17 ≤ pc := by
    by_cases hp : 17 ≤ pc
    · exact hp
    · simp [shiftProgram, hp] at h
  have cases : pc = 17 ∨ pc = 19 ∨ pc = 22 ∨ pc = 25 ∨ pc = 28 ∨ pc = 33 ∨
      pc = 35 ∨ pc = 40 ∨ pc = 42 ∨ pc = 44 ∨ pc = 46 := by
    simp only [shiftProgram, hp, ↓reduceIte] at h
    generalize he : pc - 17 = localPC at h
    fun_cases forwardGuardProgram localPC <;> simp_all [forwardGuardProgram] <;> omega
  rcases cases with h | h | h | h | h | h | h | h | h | h | h <;> subst pc <;> rfl

private theorem valid_map {α β : Type} {v : Option α} {f : α → β} {b : β}
    (h : v.map f = some b) : v ≠ none := by cases v <;> simp_all

/-- Continuous execution through the real turning/guard seam. The guard consumes
exactly the memory/register state produced by turning, including alias effects. -/
theorem move_entry_program (s : X86Memory.State) (flags : Option Flags) :
    (runProgram moveEntryProgram [48, 120] 17 ⟨s, flags, 0⟩).map
      (fun t => (t.pc, t.core.memory)) =
      some (17 + forwardGuardResult (turnEndCore s),
        store32 (turnEndCore s).memory 0x2cf90 (if groundFlag (turnEndCore s) then 1 else 0)) := by
  rw [show 17 = 6 + 11 by rfl, (move_entry_turn_prefix s flags).run 11]
  have shifted := runProgram_shift forwardGuardProgram forward_guard_forward 17 [31, 103] 11
    ⟨turnEndCore s, none, 0⟩
  have valid := valid_map (forward_guard_program (turnEndCore s) none)
  have validShift : runProgram (shiftProgram 17 forwardGuardProgram) [48, 120] 11
      ⟨turnEndCore s, none, 17⟩ ≠ none := by
    change runProgram (shiftProgram 17 forwardGuardProgram) (List.map (17 + ·) [31, 103]) 11
      (shiftState 17 ⟨turnEndCore s, none, 0⟩) ≠ none
    rw [shifted]
    simpa using valid
  rw [runProgram_extend _ _ move_entry_contains_guard _ _ _ validShift]
  change ((runProgram (shiftProgram 17 forwardGuardProgram) (List.map (17 + ·) [31, 103]) 11
    (shiftState 17 ⟨turnEndCore s, none, 0⟩))).map _ = _
  rw [shifted]
  have result := congrArg (Option.map (fun p : Nat × Memory => (17 + p.1, p.2)))
    (forward_guard_program (turnEndCore s) none)
  simpa [Option.map_map, Function.comp_def, shiftState] using result

theorem original_move_entry (s : X86Memory.State) (flags : Option Flags) :
    (X86Control.run moveEntryBytes [48, 120] 17 ⟨s, flags, 0⟩).map
      (fun t => (t.pc, t.core.memory)) =
      some (17 + forwardGuardResult (turnEndCore s),
        store32 (turnEndCore s).memory 0x2cf90 (if groundFlag (turnEndCore s) then 1 else 0)) := by
  rw [runProgram_sound _ _ move_entry_decoded _ _ _ (valid_map (move_entry_program s flags))]
  exact move_entry_program s flags

/-- All premises describe entry memory, before any of these instructions run.
In particular, no ground predicate or command is assumed again at the seam. -/
structure MoveEntryInputs (s : X86Memory.State) (body : Motion) (cmd : Ticcmd) : Prop where
  angle : load32 s.memory (load32 s.memory (s.regs eax) + (32#32)) = body.angle.raw.toBitVec
  turn : load16 s.memory (s.regs eax + (10#32)) = cmd.angleTurn.toBitVec
  forward : s.memory (s.regs eax + (8#32)) = cmd.forwardMove.toBitVec
  height : load32 s.memory (load32 s.memory (s.regs eax) + (20#32)) = body.z.raw.toBitVec
  floor : load32 s.memory (load32 s.memory (s.regs eax) + (56#32)) = body.floorz.raw.toBitVec
  playerApart : Apart (s.regs eax) (load32 s.memory (s.regs eax) + (32#32))
  heightApart : Apart (load32 s.memory (s.regs eax) + (20#32)) (load32 s.memory (s.regs eax) + (32#32))
  floorApart : Apart (load32 s.memory (s.regs eax) + (56#32)) (load32 s.memory (s.regs eax) + (32#32))
  commandsApart : Apart (s.regs eax + (8#32)) (load32 s.memory (s.regs eax) + (32#32))
  groundApartAngle : Apart (load32 s.memory (s.regs eax) + (32#32)) 0x2cf90

theorem turn_establishes_guard_inputs (s : X86Memory.State) (body : Motion) (cmd : Ticcmd)
    (h : MoveEntryInputs s body cmd) :
    load32 (turnEndCore s).memory (load32 (turnEndCore s).memory ((turnEndCore s).regs 1) + (20#32)) = body.z.raw.toBitVec ∧
    load32 (turnEndCore s).memory (load32 (turnEndCore s).memory ((turnEndCore s).regs 1) + (56#32)) = body.floorz.raw.toBitVec ∧
    (turnEndCore s).memory ((turnEndCore s).regs 6) = cmd.forwardMove.toBitVec := by
  have hp (v : Word) := load_store_apart s.memory _ _ v h.playerApart
  have hz (v : Word) := load_store_apart s.memory _ _ v h.heightApart
  have hf (v : Word) := load_store_apart s.memory _ _ v h.floorApart
  have hc0 := h.commandsApart 0 0
  have hc1 := h.commandsApart 0 1
  have hc2 := h.commandsApart 0 2
  have hc3 := h.commandsApart 0 3
  simp at hc0 hc1 hc2 hc3
  simp [turnEndCore, write, eax, ebx, ecx, esi]
  rw [hp, hz, hf, h.height, h.floor]
  simp only [true_and]
  exact (turn_store_preserves s.memory _ _ _ hc0 hc1 hc2 hc3).trans h.forward

def moveEntryResultMemory (s : X86Memory.State) (body : Motion) (cmd : Ticcmd) : Memory :=
  store32 (store32 s.memory (load32 s.memory (s.regs eax) + (32#32))
    (body.turn cmd.angleTurn).angle.raw.toBitVec) 0x2cf90 (if body.onGround then 1 else 0)

/-- Any related starting state and any command: continuous original-byte
execution stores the engine's turned angle and chooses its forward-thrust path. -/
theorem move_entry_matches_engine (s : X86Memory.State) (flags : Option Flags)
    (body : Motion) (cmd : Ticcmd) (h : MoveEntryInputs s body cmd) :
    (X86Control.run moveEntryBytes [48, 120] 17 ⟨s, flags, 0⟩).map
      (fun t => (t.pc, t.core.memory)) =
      some (if body.onGround ∧ cmd.forwardMove ≠ 0 then 48 else 120,
        moveEntryResultMemory s body cmd) := by
  have ⟨hz, hf, hc⟩ := turn_establishes_guard_inputs s body cmd h
  rw [original_move_entry, forward_guard_matches_engine _ body cmd hz hf hc,
    ground_flag_matches_engine _ body hz hf]
  simp only [turnEndCore, h.angle, h.turn, turn_shift_matches_engine,
    decide_eq_true_eq, moveEntryResultMemory]
  by_cases hg : body.onGround ∧ cmd.forwardMove ≠ 0 <;> simp [hg]

/-- The cached-ground write does not erase the newly computed angle. -/
theorem move_entry_final_angle (s : X86Memory.State) (flags : Option Flags)
    (body : Motion) (cmd : Ticcmd) (h : MoveEntryInputs s body cmd) :
    (X86Control.run moveEntryBytes [48, 120] 17 ⟨s, flags, 0⟩).map
      (fun t => load32 t.core.memory (load32 s.memory (s.regs eax) + (32#32))) =
      some (body.turn cmd.angleTurn).angle.raw.toBitVec := by
  have result := congrArg (Option.map (fun p : Nat × Memory =>
    load32 p.2 (load32 s.memory (s.regs eax) + (32#32)))) (move_entry_matches_engine s flags body cmd h)
  simpa only [Option.map_map, Function.comp_def, Option.map_some, moveEntryResultMemory,
    load_store_apart _ _ _ _ h.groundApartAngle, load_store] using result

end Doom.Proofs
