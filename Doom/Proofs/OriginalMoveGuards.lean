import Doom.Motion
import Doom.Proofs.BlockSummary
import Doom.Verification.X86Control

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

namespace Doom.Proofs
open Verification X86 X86Memory X86Control

theorem cmp32_signed_le (a b : BitVec 32) :
    (compare32 a b).lessEqual =
      decide (a.toInt ≤ b.toInt) := by
  change (((a-b) == (0#32)) || ((a-b).msb != ((a.msb != b.msb) && ((a-b).msb != a.msb)))) = _
  have haBound := a.isLt
  have hbBound := b.isLt
  cases ha : a.msb <;> cases hb : b.msb <;> cases hr : (a-b).msb <;>
    simp [ha, hb, hr, BitVec.toInt_eq_msb_cond, ← BitVec.toNat_inj] <;>
    simp only [BitVec.msb_eq_decide, BitVec.toNat_sub, decide_eq_true_eq, decide_eq_false_iff_not] at ha hb hr <;>
    (try apply Bool.eq_iff_iff.mpr) <;>
    (try simp only [beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj, BitVec.toNat_zero, BitVec.toNat_sub]) <;>
    omega


theorem cmp32_zero (a b : BitVec 32) : (compare32 a b).zero = (a == b) := by
  simp only [compare32]
  try dsimp only [Word] at *
  bv_decide

/-- Register-byte writes preserve the other bits, including DH when writing DL. -/
theorem write_low_read (a : BitVec 32) (v : BitVec 8) :
    ((a &&& (0xffffff00#32)) ||| v.zeroExtend 32).extractLsb' 0 8 = v := by
  try dsimp only [Word] at *
  bv_decide

theorem write_high_read (a : BitVec 32) (v : BitVec 8) :
    ((a &&& (0xffff00ff#32)) ||| (v.zeroExtend 32 <<< 8)).extractLsb' 8 8 = v := by
  rw [BitVec.extractLsb'_or, BitVec.extractLsb'_and]
  simp
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  by_cases hi : i < 8
  · have h1 : 8+i < 32 := by omega
    have h2 : ¬8+i < 8 := by omega
    have h3 : i < 32 := by omega
    simp [hi, h1, h2, h3]
  · simp [hi]


theorem low_mask_zero (a : BitVec 32) : (a &&& (0xffffff00#32)).extractLsb' 0 8 = 0 := by
  try dsimp only [Word] at *
  bv_decide

theorem high_mask_zero (a : BitVec 32) : (a &&& (0xffff00ff#32)).extractLsb' 8 8 = 0 := by
  try dsimp only [Word] at *
  bv_decide

theorem setle_false_mask (a : BitVec 32) : (a &&& (0xffffff00#32)) &&& (255#32) = 0 := by
  try dsimp only [Word] at *
  bv_decide

theorem setle_true_mask (a : BitVec 32) : ((a &&& (0xffffff00#32)) ||| (1#32)) &&& (255#32) = 1 := by
  rw [BitVec.and_or_distrib_right, BitVec.and_assoc]
  simp


/-- Proposed control-flow listings. Each executed entry is checked against the
actual byte decoder below; these listings are not assumptions. -/
def forwardGuardProgram : Program
  | 0 => some (.block (.legacy (.load 0 1 0)), 2)
  | 2 => some (.block (.legacy (.load 3 0 20)), 3)
  | 5 => some (.cmpMemory 3 ⟨some 0, none, 0, 56⟩, 3)
  | 8 => some (.setle 0, 3)
  | 11 => some (.andEax 255, 5)
  | 16 => some (.loadByte 2 ⟨some 6, none, 0, 0⟩, 2)
  | 18 => some (.storeEax 0x2cf90, 5)
  | 23 => some (.testByte 2 2, 2)
  | 25 => some (.jumpZero true 76, 2)
  | 27 => some (.testWord 0 0, 2)
  | 29 => some (.jumpZero true 72, 2)
  | _ => none

def sideGuardProgram : Program
  | 0 => some (.loadByte 6 ⟨some 6, none, 0, 1⟩, 3)
  | 3 => some (.testByte 6 6, 2)
  | 5 => some (.jumpZero true 86, 2)
  | 7 => some (.cmpImmediate ⟨none, none, 0, 0x2cf90⟩ 0, 7)
  | 14 => some (.jumpZero true 77, 2)
  | _ => none

theorem forward_guard_decoded (pc : Nat) (h : forwardGuardProgram pc ≠ none) :
    decodeAt Doom19.forwardGuardBytes pc = forwardGuardProgram pc := by
  fun_cases forwardGuardProgram pc <;> simp_all [forwardGuardProgram] <;> rfl

theorem side_guard_decoded (pc : Nat) (h : sideGuardProgram pc ≠ none) :
    decodeAt Doom19.sideGuardBytes pc = sideGuardProgram pc := by
  fun_cases sideGuardProgram pc <;> simp_all [sideGuardProgram] <;> rfl

def groundFlag (s : X86Memory.State) : Bool :=
  decide ((load32 s.memory (load32 s.memory (s.regs 1) + (20#32))).toInt ≤
    (load32 s.memory (load32 s.memory (s.regs 1) + (56#32))).toInt)

def forwardGuardResult (s : X86Memory.State) : Nat :=
  if s.memory (s.regs 6) = 0 then 103 else if groundFlag s then 31 else 103

def sideGuardResult (s : X86Memory.State) : Nat :=
  if s.memory (s.regs 6 + 1) = 0 then 93 else if load32 s.memory 0x2cf90 = 0 then 93 else 16

theorem forward_guard_program (s : X86Memory.State) (flags : Option Flags) :
    (runProgram forwardGuardProgram [31, 103] 11 ⟨s, flags, 0⟩).map (fun t => (t.pc, t.core.memory)) =
      some (forwardGuardResult s, store32 s.memory 0x2cf90 (if groundFlag s then 1 else 0)) := by
  have hl : (s.regs 2 &&& (4294967040#32)).extractLsb' 0 8 = (0#8) := low_mask_zero (s.regs 2)
  have hw : ((s.regs 2 &&& (4294967040#32)) ||| (s.memory (s.regs 6)).setWidth 32).extractLsb' 0 8 = s.memory (s.regs 6) := write_low_read _ _
  have hm0 : (load32 s.memory (s.regs 1) &&& (4294967040#32)) &&& (255#32) = (0#32) := setle_false_mask _
  have hm1 : ((load32 s.memory (s.regs 1) &&& (4294967040#32)) ||| (1#32)) &&& (255#32) = (1#32) := setle_true_mask _
  by_cases hf : s.memory (s.regs 6) = 0 <;>
    by_cases hg : (load32 s.memory (load32 s.memory (s.regs 1) + (20#32))).toInt ≤
      (load32 s.memory (load32 s.memory (s.regs 1) + (56#32))).toInt <;>
    simp [runProgram, forwardGuardProgram, X86Control.execute, X86Block.execute,
      X86Memory.execute, blockPreservesFlags, X86Block.Address.eval, putByte,
      readByte, byteReg, put, write, logical8, logical32, cmp32_signed_le,
      setle_false_mask, setle_true_mask, write_low_read, low_mask_zero, forwardGuardResult, groundFlag, hf, hg,
      eax]
  all_goals dsimp only [Word] at *
  all_goals simp_all only [hm0, hm1, cmp32_signed_le, BitVec.setWidth_zero, BitVec.or_zero]
  all_goals simp_all (config := { maxSteps := 300000 }) [write]

theorem side_guard_program (s : X86Memory.State) (flags : Option Flags) :
    (runProgram sideGuardProgram [16, 93] 5 ⟨s, flags, 0⟩).map (fun t => (t.pc, t.core.memory)) =
      some (sideGuardResult s, s.memory) := by
  have hv6 : (6 : Reg).val = 6 := rfl
  have hl : (s.regs 2 &&& (4294902015#32)).extractLsb' 8 8 = (0#8) := high_mask_zero (s.regs 2)
  have hw : ((s.regs 2 &&& (4294902015#32)) |||
      ((s.memory (s.regs 6 + (1#32))).setWidth 32 <<< 8)).extractLsb' 8 8 =
      s.memory (s.regs 6 + (1#32)) := write_high_read _ _
  by_cases hc : s.memory (s.regs 6 + (1#32)) = 0 <;>
    by_cases hg : load32 s.memory (0x2cf90#32) = 0 <;>
    simp [runProgram, sideGuardProgram, X86Control.execute, X86Block.Address.eval,
      putByte, readByte, byteReg, put, write, logical8, cmp32_zero,
      sideGuardResult, hc, hg, hl, hw, hv6]
  all_goals try dsimp only [Word] at *
  all_goals simp_all [write, cmp32_zero]

private theorem map_some_valid {α β : Type} {v : Option α} {f : α → β} {b : β}
    (h : v.map f = some b) : v ≠ none := by
  cases v <;> simp_all

theorem original_forward_guard (s : X86Memory.State) (flags : Option Flags) :
    (X86Control.run Doom19.forwardGuardBytes [31, 103] 11 ⟨s, flags, 0⟩).map
      (fun t => (t.pc, t.core.memory)) =
      some (forwardGuardResult s, store32 s.memory 0x2cf90 (if groundFlag s then 1 else 0)) := by
  rw [runProgram_sound _ _ forward_guard_decoded _ _ _ (map_some_valid (forward_guard_program s flags))]
  exact forward_guard_program s flags

theorem original_side_guard (s : X86Memory.State) (flags : Option Flags) :
    (X86Control.run Doom19.sideGuardBytes [16, 93] 5 ⟨s, flags, 0⟩).map
      (fun t => (t.pc, t.core.memory)) = some (sideGuardResult s, s.memory) := by
  rw [runProgram_sound _ _ side_guard_decoded _ _ _ (map_some_valid (side_guard_program s flags))]
  exact side_guard_program s flags

theorem ground_flag_matches_engine (s : X86Memory.State) (body : Motion)
    (hz : load32 s.memory (load32 s.memory (s.regs 1) + (20#32)) = body.z.raw.toBitVec)
    (hf : load32 s.memory (load32 s.memory (s.regs 1) + (56#32)) = body.floorz.raw.toBitVec) :
    groundFlag s = decide body.onGround := by
  unfold groundFlag
  rw [hz, hf]
  simp [Motion.onGround, Int32.le_iff_toInt_le]

private theorem command_zero (v : Int8) : v.toBitVec = 0 ↔ v = 0 := by
  simpa using (Int8.toBitVec_inj (a := v) (b := 0))

/-- The original forward branch predicate equals the conditions in movePlayer.
This does not identify the inlined thrust body with the standalone routine. -/
theorem forward_guard_matches_engine (s : X86Memory.State) (body : Motion) (cmd : Ticcmd)
    (hz : load32 s.memory (load32 s.memory (s.regs 1) + (20#32)) = body.z.raw.toBitVec)
    (hf : load32 s.memory (load32 s.memory (s.regs 1) + (56#32)) = body.floorz.raw.toBitVec)
    (hc : s.memory (s.regs 6) = cmd.forwardMove.toBitVec) :
    forwardGuardResult s = if body.onGround ∧ cmd.forwardMove ≠ 0 then 31 else 103 := by
  rw [forwardGuardResult, ground_flag_matches_engine s body hz hf, hc]
  simp only [command_zero, decide_eq_true_eq]
  split <;> simp_all

/-- The second guard consumes the cached ground value, even if some unrelated
memory field has since changed. Its correspondence premise makes that explicit. -/
theorem side_guard_matches_engine (s : X86Memory.State) (body : Motion) (cmd : Ticcmd)
    (hg : load32 s.memory 0x2cf90 = if body.onGround then 1 else 0)
    (hc : s.memory (s.regs 6 + 1) = cmd.sideMove.toBitVec) :
    sideGuardResult s = if body.onGround ∧ cmd.sideMove ≠ 0 then 16 else 93 := by
  rw [sideGuardResult, hg, hc]
  simp only [command_zero]
  by_cases h : body.onGround <;> by_cases c : cmd.sideMove = 0 <;> simp [h, c]

/-- Factoring the ground predicate preserves the exact prior player update. -/
theorem movePlayer_ground_definition (body : Motion) :
    body.onGround ↔ body.z.raw ≤ body.floorz.raw := Iff.rfl

theorem turn_preserves_ground (body : Motion) (amount : Int16) :
    (body.turn amount).onGround ↔ body.onGround := Iff.rfl

theorem thrust_preserves_ground (body : Motion) (angle : Angle) (move : Fixed) :
    (body.thrust angle move).onGround ↔ body.onGround := Iff.rfl

/-- Direct original-byte-to-engine branch claim, composing the execution and
input-relation theorems without assuming any path or initial flags. -/
theorem forward_guard_engine_pc (s : X86Memory.State) (flags : Option Flags)
    (body : Motion) (cmd : Ticcmd)
    (hz : load32 s.memory (load32 s.memory (s.regs 1) + (20#32)) = body.z.raw.toBitVec)
    (hf : load32 s.memory (load32 s.memory (s.regs 1) + (56#32)) = body.floorz.raw.toBitVec)
    (hc : s.memory (s.regs 6) = cmd.forwardMove.toBitVec) :
    (X86Control.run Doom19.forwardGuardBytes [31, 103] 11 ⟨s, flags, 0⟩).map (·.pc) =
      some (if body.onGround ∧ cmd.forwardMove ≠ 0 then 31 else 103) := by
  have h := congrArg (Option.map Prod.fst) (original_forward_guard s flags)
  simpa only [Option.map_map, Function.comp_def, Option.map_some,
    forward_guard_matches_engine s body cmd hz hf hc] using h

theorem side_guard_engine_pc (s : X86Memory.State) (flags : Option Flags)
    (body : Motion) (cmd : Ticcmd)
    (hg : load32 s.memory 0x2cf90 = if body.onGround then 1 else 0)
    (hc : s.memory (s.regs 6 + 1) = cmd.sideMove.toBitVec) :
    (X86Control.run Doom19.sideGuardBytes [16, 93] 5 ⟨s, flags, 0⟩).map (·.pc) =
      some (if body.onGround ∧ cmd.sideMove ≠ 0 then 16 else 93) := by
  have h := congrArg (Option.map Prod.fst) (original_side_guard s flags)
  simpa only [Option.map_map, Function.comp_def, Option.map_some,
    side_guard_matches_engine s body cmd hg hc] using h

end Doom.Proofs
