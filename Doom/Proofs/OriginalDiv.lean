import Doom.Fixed
import Doom.Verification.X86ValueRoutine
import Doom.Verification.Doom19
import Init.Data.SInt.Lemmas
import Init.Omega

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

namespace Doom.Proofs
open Verification X86 X86ValueRoutine

theorem wrapped_abs_bits (w : Word) :
    (w ^^^ signMask w) - signMask w = (Fixed.absWrap (Int32.ofBitVec w)).toBitVec := by
  unfold signMask Fixed.absWrap
  simp only [Int32.lt_iff_toInt_lt, Int32.toInt_ofBitVec, Int32.toInt_zero]
  split
  · simp only [BitVec.xor_allOnes, Int32.toBitVec_neg, Int32.toBitVec_ofBitVec]
    change ~~~w - (-1#32) = -w
    rw [BitVec.sub_neg]
    exact (BitVec.neg_eq_not_add w).symm
  · simp

theorem lowByte_mask (w : Word) (b : BitVec 8) :
    lowByte w b &&& 255#32 = b.setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  simp only [lowByte, BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_setWidth]
  change ((w.toNat / 256 * 256 + b.toNat) % 4294967296) &&& (2^8-1) = b.toNat % 4294967296
  rw [Nat.and_two_pow_sub_one_eq_mod]
  have := b.isLt
  omega

def divisionInputs (a b : Fixed) : State :=
  { regs := fun r => if r = eax then a.raw.toBitVec else if r = edx then b.raw.toBitVec else 0 }

def divisionAnswer (answer : Except Fixed.DivisionError Fixed) : Except Fault Word :=
  match answer with
  | .ok v => .ok v.raw.toBitVec
  | .error .divideByZero => .error .divideByZero
  | .error .quotientOverflow => .error .quotientOverflow

def divGuard (a b : Word) : Prop :=
  (((a ^^^ signMask a) - signMask a).sshiftRight 14).toInt <
    ((b ^^^ signMask b) - signMask b).toInt
instance (a b : Word) : Decidable (divGuard a b) := inferInstanceAs (Decidable (_ < _))

def divDividend (a : Word) : Int :=
  ((((signMask a ++ a) <<< 16).extractLsb' 32 32) ++ (a <<< 16)).toInt

theorem divDividend_exact (a : Word) : divDividend a = a.toInt * 65536 := by
  unfold divDividend
  have low : a <<< 16 = (((signMask a ++ a) <<< 16).extractLsb' 0 32) := by
    rw [← BitVec.setWidth_eq_extractLsb' (by decide), BitVec.setWidth_shiftLeft_of_le (by decide)]
    rw [BitVec.setWidth_eq_extractLsb' (by decide), BitVec.extractLsb'_append_eq_right]
  rw [low, BitVec.extractLsb'_append_extractLsb']
  have join : (signMask a ++ a).toInt = a.toInt := by
    rw [BitVec.toInt_append]
    have hn := a.isLt
    have hr := BitVec.toInt_eq_toNat_cond a
    by_cases h : a.toInt < 0
    · simp [signMask, h, BitVec.toInt_append]
      split at hr <;> omega
    · simp [signMask, h, BitVec.toInt_append]
      split at hr <;> omega
  have eqx : signMask a ++ a = BitVec.ofInt 64 a.toInt := by
    rw [← join]
    exact BitVec.ofInt_toInt.symm
  rw [BitVec.shiftLeft_eq_mul_twoPow, eqx,
    show BitVec.twoPow 64 16 = BitVec.ofInt 64 65536 from rfl,
    ← BitVec.ofInt_mul, BitVec.toInt_ofInt]
  apply Int.bmod_eq_of_le
  · have := a.le_toInt; omega
  · have := a.toInt_lt; omega

def divProgram : Nat → Option (Op × Nat)
  | 0 => some (.push ebx, 1)
  | 1 => some (.push ecx, 1)
  | 2 => some (.push esi, 1)
  | 3 => some (.mov ecx eax, 2)
  | 5 => some (.mov ebx edx, 2)
  | 7 => some (.cdq, 1)
  | 8 => some (.xor eax edx, 2)
  | 10 => some (.sub eax edx, 2)
  | 12 => some (.mov esi eax, 2)
  | 14 => some (.mov eax ebx, 2)
  | 16 => some (.sar esi 14, 3)
  | 19 => some (.cdq, 1)
  | 20 => some (.xor eax edx, 2)
  | 22 => some (.sub eax edx, 2)
  | 24 => some (.cmp esi eax, 2)
  | 26 => some (.jl 21, 2)
  | 28 => some (.xor ebx ecx, 2)
  | 30 => some (.test ebx ebx, 2)
  | 32 => some (.setlAl, 3)
  | 35 => some (.andEax 255, 5)
  | 40 => some (.addEax 2147483647, 5)
  | 45 => some (.pop esi, 1)
  | 46 => some (.pop ecx, 1)
  | 47 => some (.pop ebx, 1)
  | 48 => some (.ret, 1)
  | 49 => some (.mov eax ecx, 2)
  | 51 => some (.cdq, 1)
  | 52 => some (.shld edx eax 16, 4)
  | 56 => some (.shl eax 16, 3)
  | 59 => some (.idiv ebx, 2)
  | 61 => some (.pop esi, 1)
  | 62 => some (.pop ecx, 1)
  | 63 => some (.pop ebx, 1)
  | 64 => some (.ret, 1)
  | _ => none

-- Only instruction-boundary entries are used; other offsets need not decode to none.
set_option maxRecDepth 4096 in
private theorem div_decode_at : ∀ pc : Fin 65, divProgram pc.val ≠ none →
    X86ValueRoutine.decode (Doom19.fixedDivBytes.drop pc.val) = divProgram pc.val := by decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
theorem div_execution (a b : Fixed) :
    resultWord (runProgram divProgram 40 (divisionInputs a b)) =
      some (if divGuard a.raw.toBitVec b.raw.toBitVec then
        if b.raw.toInt = 0 then .error .divideByZero
        else let q := (divDividend a.raw.toBitVec).tdiv b.raw.toInt
             if q < -2147483648 ∨ 2147483647 < q then .error .quotientOverflow
             else .ok (BitVec.ofInt 32 q)
      else .ok ((if (b.raw.toBitVec ^^^ a.raw.toBitVec).toInt < 0 then 1 else 0) + 2147483647)) := by
  by_cases hg : divGuard a.raw.toBitVec b.raw.toBitVec
  all_goals
    simp [divGuard, -Int.not_lt] at hg
    unfold divisionInputs
    iterate 16 (rw [runProgram.eq_def]; simp [divProgram, X86ValueRoutine.execute, put, write, eax, ebx, ecx, edx, esi])
    try simp only [hg, decide_true, decide_false, if_true, if_false]
  case pos =>
    iterate 4 (rw [runProgram.eq_def]; simp [divProgram, X86ValueRoutine.execute, put, write, eax, ebx, ecx, edx, esi])
    rw [runProgram.eq_def]
    simp [divProgram, X86ValueRoutine.execute, put, write, eax, ebx, ecx, edx, esi]
    by_cases hd : b.raw.toInt = 0
    · simp [hd, resultWord, divGuard, hg]
    · by_cases hq : (divDividend a.raw.toBitVec).tdiv b.raw.toInt < -2147483648 ∨
          2147483647 < (divDividend a.raw.toBitVec).tdiv b.raw.toInt
      all_goals
        simp only [divDividend] at hq
        simp only [hd, hq, if_false, if_true]
        try iterate 4 (rw [runProgram.eq_def]; simp [divProgram, X86ValueRoutine.execute, put, write, eax, ebx, ecx, edx, esi])
        simp [resultWord, write, eax, divGuard, hg, hd, divDividend, hq]

  case neg =>
    by_cases hs : (b.raw.toBitVec ^^^ a.raw.toBitVec).toInt < 0
    all_goals
      simp [BitVec.toInt_xor, -Int.not_lt] at hs
      iterate 9 (rw [runProgram.eq_def]; simp [divProgram, X86ValueRoutine.execute, put, write, eax, ebx, ecx, edx, esi])
      simp [resultWord, divGuard, hg, hs, write, eax]
      rw [lowByte_mask]
      rfl


theorem divGuard_eq (a b : Fixed) :
    divGuard a.raw.toBitVec b.raw.toBitVec ↔ (Fixed.absWrap a.raw >>> 14) < Fixed.absWrap b.raw := by
  unfold divGuard
  rw [wrapped_abs_bits, wrapped_abs_bits]
  simp only [Int32.ofBitVec_toBitVec, Int32.lt_iff_toInt_lt]
  rfl

set_option maxRecDepth 4096 in
theorem div_program_matches (a b : Fixed) :
    resultWord (runProgram divProgram 40 (divisionInputs a b)) =
      some (divisionAnswer (Fixed.divChecked a b)) := by
  rw [div_execution]
  simp only [divGuard_eq, divDividend_exact, Int32.toInt_toBitVec]
  have hs : (b.raw.toBitVec ^^^ a.raw.toBitVec).toInt < 0 ↔ (a.raw ^^^ b.raw) < 0 := by
    rw [BitVec.xor_comm]
    simp only [Int32.lt_iff_toInt_lt, Int32.toInt_zero]
    rfl
  simp only [hs]
  unfold Fixed.divChecked
  by_cases hg : (Fixed.absWrap a.raw >>> 14) < Fixed.absWrap b.raw
  · have hge : ¬ (Fixed.absWrap a.raw >>> 14) ≥ Fixed.absWrap b.raw := by
      rw [Int32.lt_iff_toInt_lt] at hg
      change ¬ Fixed.absWrap b.raw ≤ (Fixed.absWrap a.raw >>> 14)
      rw [Int32.le_iff_toInt_le]
      omega
    simp only [hg, hge, if_true, if_false]
    by_cases hz : b.raw = 0
    · simp [hz, divisionAnswer]
    · have hzi : b.raw.toInt ≠ 0 := by
        intro h; apply hz; exact Int32.toInt_inj.mp h
      simp only [beq_iff_eq, hz, hzi, if_false]
      split <;> simp_all [divisionAnswer, -Int.not_lt]
  · have hge : (Fixed.absWrap a.raw >>> 14) ≥ Fixed.absWrap b.raw := by
      rw [Int32.lt_iff_toInt_lt] at hg
      change Fixed.absWrap b.raw ≤ (Fixed.absWrap a.raw >>> 14)
      rw [Int32.le_iff_toInt_le]
      omega
    simp only [hg, hge, if_true, if_false, divisionAnswer]
    split <;> rfl

theorem divProgram_sound (pc : Nat) (h : divProgram pc ≠ none) :
    X86ValueRoutine.decode (Doom19.fixedDivBytes.drop pc) = divProgram pc := by
  have bound : pc < 65 := by
    unfold divProgram at h
    split at h <;> simp_all <;> omega
  exact div_decode_at ⟨pc, bound⟩ h

/-- All 2^64 operand pairs: equal result bits OR the same IDIV fault cause.
The complete original routine is decoded, including guard and both returns. -/
theorem fixed_div_matches_doom19 (a b : Fixed) :
    resultWord (X86ValueRoutine.run Doom19.fixedDivBytes 40 (divisionInputs a b)) =
      some (divisionAnswer (Fixed.divChecked a b)) := by
  have hp := div_program_matches a b
  have hv : runProgram divProgram 40 (divisionInputs a b) ≠ .unsupported := by
    intro h
    rw [h] at hp
    contradiction
  rw [runProgram_sound _ _ divProgram_sound _ _ hv]
  exact hp

example : Fixed.divChecked ⟨-2147483648⟩ ⟨65536⟩ = .ok ⟨-2147483648⟩ := by rfl
example : Fixed.divChecked ⟨-2147483648⟩ ⟨-65536⟩ = .error .quotientOverflow := by rfl
example : Fixed.divChecked ⟨-2147483648⟩ ⟨0⟩ = .error .divideByZero := by rfl
example : Fixed.divChecked ⟨0⟩ ⟨0⟩ = .ok ⟨2147483647⟩ := by rfl
example : Fixed.divChecked ⟨-2147483648⟩ ⟨-2147483648⟩ = .ok ⟨2147483647⟩ := by rfl

end Doom.Proofs
