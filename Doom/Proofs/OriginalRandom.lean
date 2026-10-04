import Doom.Random
import Doom.Proofs.OriginalDiv
import Init.Data.UInt.Lemmas

set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

namespace Doom.Proofs
open Verification X86 X86Routine

def rngProgram (addr : Nat) : Nat → Option (Op × Nat)
  | 0 => some (.loadEax addr, 5)
  | 5 => some (.inc eax, 1)
  | 6 => some (.andEax 255, 5)
  | 11 => some (.storeEax addr, 5)
  | 16 => some (.loadAl 0x1261c, 6)
  | 22 => some (.andEax 255, 5)
  | 27 => some (.ret, 1)
  | _ => none

def rngObserve : Result → Option (Word × Word × Word)
  | .returned s => some (s.regs eax, s.words 0x12720, s.words 0x1271c)
  | _ => none

def incrementIndex (index : Word) : Word := (index + 1) &&& 255

set_option maxRecDepth 4096 in
theorem rng_execution (addr : Nat) (words : Nat → Word) (bytes : Nat → BitVec 8) :
    rngObserve (runProgram (rngProgram addr) 7 { words, bytes }) =
      some ((bytes (0x1261c + (incrementIndex (words addr)).toNat)).setWidth 32,
        (if 0x12720 = addr then incrementIndex (words addr) else words 0x12720),
        (if 0x1271c = addr then incrementIndex (words addr) else words 0x1271c)) := by
  iterate 7 (rw [runProgram.eq_def]; simp [rngProgram, X86Routine.execute, put, putWord, write, eax])
  simp only [rngObserve, write, eax, if_true]
  rw [lowByte_mask]
  rfl

theorem incrementIndex_byte (i : UInt8) :
    incrementIndex (BitVec.ofNat 32 i.toNat) = BitVec.ofNat 32 (i+1).toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [incrementIndex, BitVec.toNat_and, BitVec.toNat_add, BitVec.toNat_ofNat,
    UInt8.toNat_add, UInt8.toNat_one]
  change ((i.toNat % 4294967296 + 1 % 4294967296) % 4294967296) &&& (2^8-1) =
    ((i.toNat + 1) % 256) % 4294967296
  rw [Nat.and_two_pow_sub_one_eq_mod]
  have := i.toNat_lt
  omega

/-- This literal table is extracted from DOOM.EXE, independently of the engine table. -/
def originalRandomAt (i : UInt8) : UInt8 := Doom19.randomTableBytes.toArray[i.toNat]!

set_option maxRecDepth 4096 in
theorem original_table_matches : ∀ i : Fin 256,
    (Doom19.randomTableBytes.toArray[i.val]!).toNat = randomAt (UInt8.ofNat i.val) := by decide

theorem byte_word_nat (i : UInt8) : (BitVec.ofNat 32 i.toNat).toNat = i.toNat := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  have := i.toNat_lt
  omega

theorem original_table_word (i : UInt8) :
    (Doom19.randomTableBytes.toArray[i.toNat]!).toBitVec.setWidth 32 = BitVec.ofNat 32 (randomAt i) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, UInt8.toNat_toBitVec, BitVec.toNat_ofNat]
  have ht := original_table_matches ⟨i.toNat, i.toNat_lt⟩
  simpa only [UInt8.ofNat_toNat] using congrArg (fun n => n % 4294967296) ht

theorem randomAt_word_bound (i : UInt8) : randomAt i < 4294967296 := by
  have ht := original_table_matches ⟨i.toNat, i.toNat_lt⟩
  simp only [UInt8.ofNat_toNat] at ht
  rw [← ht]
  have := (Doom19.randomTableBytes.toArray[i.toNat]!).toNat_lt
  omega

def rngInputs (r : DoomRandom) (table : List UInt8 := Doom19.randomTableBytes) : State :=
  { words := fun addr => if addr = 0x12720 then BitVec.ofNat 32 r.play.toNat
      else if addr = 0x1271c then BitVec.ofNat 32 r.misc.toNat else 0
    bytes := fun addr => (table.toArray[addr - 0x1261c]!).toBitVec }

def rngAnswer (r : Nat × DoomRandom) : Word × Word × Word :=
  (BitVec.ofNat 32 r.1, BitVec.ofNat 32 r.2.play.toNat, BitVec.ofNat 32 r.2.misc.toNat)

set_option maxRecDepth 4096 in
theorem play_program_matches (r : DoomRandom) :
    rngObserve (runProgram (rngProgram 0x12720) 7 (rngInputs r)) = some (rngAnswer r.nextPlay) := by
  unfold rngInputs
  rw [rng_execution]
  simp only [↓reduceIte, incrementIndex_byte, rngAnswer, DoomRandom.nextPlay]
  simp only [byte_word_nat, Nat.add_sub_cancel_left, original_table_word,
    show ¬(75548 : Nat) = 75552 by decide, if_false]

set_option maxRecDepth 4096 in
theorem misc_program_matches (r : DoomRandom) :
    rngObserve (runProgram (rngProgram 0x1271c) 7 (rngInputs r)) = some (rngAnswer r.nextMisc) := by
  unfold rngInputs
  rw [rng_execution]
  simp only [↓reduceIte, incrementIndex_byte, rngAnswer, DoomRandom.nextMisc]
  simp only [byte_word_nat, Nat.add_sub_cancel_left, original_table_word,
    show ¬(75552 : Nat) = 75548 by decide, show ¬(75548 : Nat) = 75552 by decide,
    if_false, incrementIndex_byte, byte_word_nat, original_table_word]

def clearProgram : Nat → Option (Op × Nat)
  | 0 => some (.push edx, 1)
  | 1 => some (.xor edx edx, 2)
  | 3 => some (.store edx 0x12720, 6)
  | 9 => some (.store edx 0x1271c, 6)
  | 15 => some (.pop edx, 1)
  | 16 => some (.ret, 1)
  | _ => none

theorem clear_program_matches (r : DoomRandom) :
    rngObserve (runProgram clearProgram 6 (rngInputs r)) = some (0, 0, 0) := by
  unfold rngInputs
  iterate 6 (rw [runProgram.eq_def]; simp [clearProgram, X86Routine.execute, put, putWord, write, eax, edx])
  simp [rngObserve, write, eax]

set_option maxRecDepth 4096 in
private theorem rng_decode_play : ∀ pc : Fin 28, rngProgram 0x12720 pc.val ≠ none →
    X86Routine.decode (Doom19.playRandomBytes.drop pc.val) = rngProgram 0x12720 pc.val := by decide
set_option maxRecDepth 4096 in
private theorem rng_decode_misc : ∀ pc : Fin 28, rngProgram 0x1271c pc.val ≠ none →
    X86Routine.decode (Doom19.miscRandomBytes.drop pc.val) = rngProgram 0x1271c pc.val := by decide
set_option maxRecDepth 4096 in
private theorem rng_decode_clear : ∀ pc : Fin 17, clearProgram pc.val ≠ none →
    X86Routine.decode (Doom19.clearRandomBytes.drop pc.val) = clearProgram pc.val := by decide

private theorem rng_bounded (addr pc : Nat) (h : rngProgram addr pc ≠ none) : pc < 28 := by
  unfold rngProgram at h
  split at h <;> simp_all <;> omega

theorem play_matches_doom19 (r : DoomRandom) :
    rngObserve (X86Routine.run Doom19.playRandomBytes 7 (rngInputs r)) = some (rngAnswer r.nextPlay) := by
  have hp := play_program_matches r
  rw [runProgram_sound _ (rngProgram 0x12720) (fun pc h => rng_decode_play ⟨pc, rng_bounded _ _ h⟩ h)]
  · exact hp
  · intro h; rw [h] at hp; contradiction

theorem misc_matches_doom19 (r : DoomRandom) :
    rngObserve (X86Routine.run Doom19.miscRandomBytes 7 (rngInputs r)) = some (rngAnswer r.nextMisc) := by
  have hp := misc_program_matches r
  rw [runProgram_sound _ (rngProgram 0x1271c) (fun pc h => rng_decode_misc ⟨pc, rng_bounded _ _ h⟩ h)]
  · exact hp
  · intro h; rw [h] at hp; contradiction

theorem clear_matches_doom19 (r : DoomRandom) :
    rngObserve (X86Routine.run Doom19.clearRandomBytes 6 (rngInputs r)) = some (0, 0, 0) := by
  have hp := clear_program_matches r
  have sound : ∀ pc, clearProgram pc ≠ none →
      X86Routine.decode (Doom19.clearRandomBytes.drop pc) = clearProgram pc := by
    intro pc h
    have bound : pc < 17 := by
      unfold clearProgram at h
      split at h <;> simp_all <;> omega
    exact rng_decode_clear ⟨pc, bound⟩ h
  rw [runProgram_sound _ _ sound]
  · exact hp
  · intro h; rw [h] at hp; contradiction

inductive RandomCall where
  | play | misc | clear
  deriving DecidableEq, Repr

def randomCode : RandomCall → List UInt8
  | .play => Doom19.playRandomBytes
  | .misc => Doom19.miscRandomBytes
  | .clear => Doom19.clearRandomBytes

def randomFuel : RandomCall → Nat
  | .clear => 6
  | _ => 7

def decodeRngAnswer (call : RandomCall) (answer : Word × Word × Word) : Option Nat × DoomRandom :=
  (if call = .clear then none else some answer.1.toNat,
    ⟨UInt8.ofNat answer.2.1.toNat, UInt8.ofNat answer.2.2.toNat⟩)

def binaryRandomStep (code : RandomCall → List UInt8) (table : List UInt8)
    (call : RandomCall) (r : DoomRandom) : Option (Option Nat × DoomRandom) :=
  (rngObserve (X86Routine.run (code call) (randomFuel call) (rngInputs r table))).map (decodeRngAnswer call)

def engineRandomStep (call : RandomCall) (r : DoomRandom) : Option Nat × DoomRandom :=
  match call with
  | .play => let (value, next) := r.nextPlay; (some value, next)
  | .misc => let (value, next) := r.nextMisc; (some value, next)
  | .clear => (none, r.clear)

theorem random_step_matches_doom19 (call : RandomCall) (r : DoomRandom) :
    binaryRandomStep randomCode Doom19.randomTableBytes call r = some (engineRandomStep call r) := by
  cases call <;> simp only [binaryRandomStep, randomCode, randomFuel,
    play_matches_doom19, misc_matches_doom19, clear_matches_doom19, Option.map_some]
  all_goals
    simp only [decodeRngAnswer, rngAnswer, engineRandomStep, DoomRandom.nextPlay,
      DoomRandom.nextMisc, DoomRandom.clear, byte_word_nat,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (randomAt_word_bound _), UInt8.ofNat_toNat]
    try simp only [Nat.mod_eq_of_lt (show (r.play + 1).toNat < 4294967296 by have := (r.play+1).toNat_lt; omega),
      Nat.mod_eq_of_lt (show (r.misc + 1).toNat < 4294967296 by have := (r.misc+1).toNat_lt; omega),
      Nat.mod_eq_of_lt (show r.play.toNat < 4294967296 by have := r.play.toNat_lt; omega),
      Nat.mod_eq_of_lt (show r.misc.toNat < 4294967296 by have := r.misc.toNat_lt; omega), UInt8.ofNat_toNat]
    rfl

def binaryRandomTrace (code : RandomCall → List UInt8) (table : List UInt8) :
    List RandomCall → DoomRandom → Option (List (Option Nat) × DoomRandom)
  | [], r => some ([], r)
  | call :: rest, r => do
      let (value, next) ← binaryRandomStep code table call r
      let (values, last) ← binaryRandomTrace code table rest next
      pure (value :: values, last)

def engineRandomTrace : List RandomCall → DoomRandom → List (Option Nat) × DoomRandom
  | [], r => ([], r)
  | call :: rest, r =>
      let (value, next) := engineRandomStep call r
      let (values, last) := engineRandomTrace rest next
      (value :: values, last)

/-- Any finite sequence of gameplay draws, miscellaneous draws, and resets:
all returned values and both final indices agree. No bound on trace length. -/
theorem random_trace_matches_doom19 (calls : List RandomCall) (r : DoomRandom) :
    binaryRandomTrace randomCode Doom19.randomTableBytes calls r = some (engineRandomTrace calls r) := by
  induction calls generalizing r with
  | nil => rfl
  | cons call rest ih =>
      simp [binaryRandomTrace, random_step_matches_doom19, ih, engineRandomTrace]

end Doom.Proofs
