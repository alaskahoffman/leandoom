import Doom.Fixed
import Doom.Verification.X86
import Doom.Verification.Doom19
import Init.Data.SInt.Lemmas
import Init.Data.BitVec.Lemmas
import Init.Omega

namespace Doom.Proofs

open Verification X86

private theorem middle_bits (p : Int) :
    ((BitVec.ofInt 64 p >>> 16).setWidth 32) = BitVec.ofInt 32 (p / 65536) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofInt,
    Nat.shiftRight_eq_div_pow]
  change (p % 18446744073709551616).toNat / 65536 % 4294967296 =
    (p / 65536 % 4294967296).toNat
  omega

/-- The actual original bytes decode to these two instructions. Checked by
kernel reduction, not an external disassembler or a native evaluator. -/
theorem original_mul_decode :
    decode Doom19.fixedMulBytes = some (.imul ebx, [0x0f, 0xac, 0xd0, 0x10]) ∧
    decode [0x0f, 0xac, 0xd0, 0x10] = some (.shrd eax edx 16, []) := by
  decide

/-- Universal result equivalence, for EVERY initial register state. The two
input bit patterns are EAX and EBX. Initial EDX and all other registers are
unconstrained. Uses the real engine's Fixed.mul, not a duplicate specification.
This theorem is about the register-result x86 semantics above; its connection
to the on-disk executable is checked separately by verify-original-mul. -/
theorem original_mul_result (regs : Registers) :
    (run 2 Doom19.fixedMulBytes regs).map (fun final => final eax) =
      some (Fixed.mul ⟨Int32.ofBitVec (regs eax)⟩
        ⟨Int32.ofBitVec (regs ebx)⟩).raw.toBitVec := by
  change some (((BitVec.ofInt 64 ((regs eax).toInt * (regs ebx).toInt)).extractLsb' 32 32 ++
    (BitVec.ofInt 64 ((regs eax).toInt * (regs ebx).toInt)).extractLsb' 0 32) >>> 16 |>.setWidth 32) = _
  rw [BitVec.extractLsb'_append_extractLsb', middle_bits]
  rfl

/-- Successful execution and preservation of every register except the two
documented IMUL outputs (EAX and EDX). No assumptions on input magnitudes. -/
theorem original_mul_frame (regs : Registers) :
    ∃ final, run 2 Doom19.fixedMulBytes regs = some final ∧
      ∀ r, r ≠ eax → r ≠ edx → final r = regs r := by
  refine ⟨execute (.shrd eax edx 16) (execute (.imul ebx) regs), rfl, ?_⟩
  intro r ha hd
  simp [execute, write, ha, hd]

/-- EAX/EBX calling convention for the inlined original multiplication. -/
def originalMulInputs (a b : Fixed) : Registers :=
  fun r => if r = eax then a.raw.toBitVec else if r = ebx then b.raw.toBitVec else 0

/-- Public arithmetic statement: exact equality of all 32 result bits, over
all 2^64 pairs of signed 16.16 input bit patterns. No range preconditions. -/
theorem fixed_mul_matches_doom19 (a b : Fixed) :
    (run 2 Doom19.fixedMulBytes (originalMulInputs a b)).map (fun final => final eax) =
      some (a * b).raw.toBitVec := by
  cases a; cases b
  exact original_mul_result (originalMulInputs _ _)

-- Regression checks on the model, including a deliberately wrong shift count.
example : decode [0xf7, 0xe3] = none := by decide -- MUL, not IMUL
example : decode [0xf7, 0x2b] = none := by decide -- memory operand is unsupported
example : decode [0x0f, 0xac, 0xd0] = none := by decide -- missing immediate
example : run 1 Doom19.fixedMulBytes (originalMulInputs ⟨1⟩ ⟨1⟩) = none := by decide
example : (run 2 [0xf7, 0xeb, 0x0f, 0xac, 0xd0, 15]
    (originalMulInputs ⟨65536⟩ ⟨65536⟩)).map (fun r => r eax) ≠ some (65536#32) := by decide
example : (Fixed.mul ⟨-1⟩ ⟨1⟩).raw = -1 := by decide
example : (Fixed.mul ⟨-2147483648⟩ ⟨-2147483648⟩).raw = 0 := by decide

end Doom.Proofs
