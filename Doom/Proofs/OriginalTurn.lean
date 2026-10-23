import Doom.Motion
import Doom.Verification.Doom19
import Doom.Verification.X86Memory
import Init.Data.SInt.Lemmas
import Std.Tactic.BVDecide

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Doom.Proofs
open Verification X86 X86Memory

/-- All four bytes are written, including unaligned and wrapping addresses. -/
theorem turn_load_store (memory : Memory) (address value : Word) :
    load32 (store32 memory address value) address = value := by
  simp only [load32, store32]
  bv_decide

theorem turn_store_preserves (memory : Memory) (address value other : Word)
    (h0 : other ≠ address) (h1 : other ≠ address+1)
    (h2 : other ≠ address+2) (h3 : other ≠ address+3) :
    store32 memory address value other = memory other := by
  simp_all [store32]

/-- Universal signed 16-bit command / 32-bit angle identity. -/
theorem turn_shift_matches_engine (body : Motion) (amount : Int16) :
    body.angle.raw.toBitVec + (amount.toBitVec.signExtend 32 <<< 16) =
      (body.turn amount).angle.raw.toBitVec := by
  simp only [Motion.turn, UInt32.toBitVec_add, Int32.toBitVec_toUInt32,
    Int32.toBitVec_ofInt]
  congr 1
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  change amount.toBitVec.signExtend 32 * BitVec.ofInt 32 65536 = _
  rw [show amount.toBitVec.signExtend 32 = BitVec.ofInt 32 amount.toInt by rfl,
    ← BitVec.ofInt_mul]

/-- This summary is reduced from the byte decoder and instruction semantics,
not assumed from a disassembly listing. No hypotheses on initial registers or
memory; reads occur in their original order before the only memory write. -/
theorem original_turn_memory (s : X86Memory.State) :
    (X86Memory.run 6 Doom19.playerTurnBytes s).map (·.memory) =
      some (store32 s.memory (load32 s.memory (s.regs eax) + 32)
        (load32 s.memory (load32 s.memory (s.regs eax) + 32) +
          ((load16 s.memory (s.regs eax + 10)).signExtend 32 <<< 16))) := by
  simp [X86Memory.run, Doom19.playerTurnBytes, X86Memory.decode, address,
    rm, reg, displacement, X86Memory.execute, put, write, BitVec.add_assoc]

/-- The gameplay claim: when player->mo, the angle field and the signed command
word correspond, the actual original angle-update block stores exactly the
angle computed by the engine's Motion.turn. Other engine fields are unchanged
by Motion.turn; this does not cover thrust, collision or a complete player tic. -/
theorem player_turn_matches_doom19 (s : X86Memory.State) (body : Motion)
    (amount : Int16)
    (angle : load32 s.memory (load32 s.memory (s.regs eax) + 32) = body.angle.raw.toBitVec)
    (command : load16 s.memory (s.regs eax + 10) = amount.toBitVec) :
    ((X86Memory.run 6 Doom19.playerTurnBytes s).map (·.memory)).map
      (fun m => load32 m (load32 s.memory (s.regs eax) + 32)) =
      some (body.turn amount).angle.raw.toBitVec := by
  rw [original_turn_memory]
  simp only [Option.map_some, turn_load_store, angle, command]
  rw [turn_shift_matches_engine]

/-- Exact write footprint: all bytes outside the four-byte angle field survive.
This remains true for aliasing inputs: no disjoint typed-memory fiction is used. -/
theorem player_turn_preserves_other_bytes (s : X86Memory.State) (other : Word)
    (h0 : other ≠ load32 s.memory (s.regs eax) + 32)
    (h1 : other ≠ (load32 s.memory (s.regs eax) + 32) + 1)
    (h2 : other ≠ (load32 s.memory (s.regs eax) + 32) + 2)
    (h3 : other ≠ (load32 s.memory (s.regs eax) + 32) + 3) :
    ((X86Memory.run 6 Doom19.playerTurnBytes s).map (·.memory)).map (fun m => m other) =
      some (s.memory other) := by
  rw [original_turn_memory]
  simp only [Option.map_some, turn_store_preserves s.memory _ _ other h0 h1 h2 h3]

/-- The block preserves EDX, ESP, EBP and EDI in this register projection. -/
theorem player_turn_preserves_register (s : X86Memory.State) (r : Reg)
    (ha : r ≠ eax) (hb : r ≠ ebx) (hc : r ≠ X86Memory.ecx) (hs : r ≠ X86Memory.esi) :
    (X86Memory.run 6 Doom19.playerTurnBytes s).map (fun t => t.regs r) = some (s.regs r) := by
  simp [X86Memory.run, Doom19.playerTurnBytes, X86Memory.decode, address,
    rm, reg, displacement, X86Memory.execute, put, write, ha, hb, hc, hs]

-- Fail closed on prefixes, missing operands, SIB, unsupported opcode,
-- incorrect instruction counts, and trailing instruction bytes.
example : X86Memory.decode [0x66, 0x89, 0xc1] = none := by decide
example : X86Memory.decode [0x0f, 0xbf, 0x5e] = none := by decide
example : X86Memory.decode [0x8b, 0x04, 0x24] = none := by decide
example : X86Memory.decode [0x8b, 0x05] = none := by decide
example : X86Memory.decode [0x29, 0x58, 0x20] = none := by decide
example (s : X86Memory.State) : X86Memory.run 5 Doom19.playerTurnBytes s = none := by rfl
example (s : X86Memory.State) : X86Memory.run 6 (Doom19.playerTurnBytes ++ [0x90]) s = none := by rfl

end Doom.Proofs
