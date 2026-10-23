import Doom.Motion
import Doom.Proofs.BlockSummary

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

namespace Doom.Proofs
open Verification X86 X86Memory X86Block BlockSummary

/-- Lifted by the Lean byte decoder; no hand-authored instruction listing. -/
def thrustOps : List X86Block.Op :=
  (decodeBlock 17 Doom19.playerThrustBytes).getD []

theorem thrust_decoded : decodeBlock 17 Doom19.playerThrustBytes = some thrustOps := by rfl

/-- The literal memory effect, preserving the original read/write ordering.
No disjointness or table-content assumptions are needed for this summary. -/
def thrustMemory (s : State) : Memory :=
  let index := (s.regs edx >>> 19) <<< 2
  let obj := load32 s.memory (s.regs eax)
  let cosine := load32 s.memory (index + load32 s.memory 0x13584)
  let mx := load32 s.memory (obj + 72) + mulWord (s.regs ebx) cosine
  let m := store32 s.memory (obj + 72) mx
  let sine := load32 m (index + 0x5a84)
  let obj' := load32 m (s.regs eax)
  store32 m (obj' + 76) (load32 m (obj' + 76) + mulWord (s.regs ebx) sine)

theorem original_thrust_memory (s : State) :
    (X86Block.run 17 Doom19.playerThrustBytes s).map (·.memory) = some (thrustMemory s) := by
  rw [certified _ _ _ thrust_decoded]
  dsimp only [thrustMemory]
  summarize_x86 thrustOps

theorem mulWord_fixed (a b : Fixed) :
    mulWord a.raw.toBitVec b.raw.toBitVec = (a * b).raw.toBitVec := by
  simp only [mulWord, Int32.ofBitVec_toBitVec]
  rfl

/-- The original SHR/LEA combination selects exactly the engine's fine angle,
for all 32-bit angles (not just demo-format angles). -/
theorem thrust_table_index (angle : Angle) :
    angle.raw.toBitVec >>> 19 <<< 2 = BitVec.ofNat 32 (angle.fineIndex.val * 4) := by
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  change (angle.raw.toBitVec >>> 19) * BitVec.ofNat 32 4 = _
  rw [BitVec.ofNat_mul]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [Angle.fineIndex, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    UInt32.toNat_toBitVec, Nat.mod_eq_of_lt (show angle.raw.toNat / 524288 < 2^32 by
      have h := angle.raw.toNat_lt; omega)]

/-- Only the two momentum fields may be changed. -/
def thrustResultMemory (s : State) (body : Motion) (angle : Angle) (move : Fixed) : Memory :=
  let obj := load32 s.memory (s.regs eax)
  let result := body.thrust angle move
  store32 (store32 s.memory (obj + 72) result.momx.raw.toBitVec)
    (obj + 76) result.momy.raw.toBitVec

/-- A relation between actual binary inputs and the real engine inputs.
The table assumptions refer to the selected entries; the extraction checker
also checks the complete 10240-entry original table. The two separation clauses
prevent the first write from corrupting the subsequent pointer and sine reads. -/
structure ThrustInputs (s : State) (body : Motion) (angle : Angle) (move : Fixed) : Prop where
  angleReg : s.regs edx = angle.raw.toBitVec
  moveReg : s.regs ebx = move.raw.toBitVec
  cosine : load32 s.memory (((s.regs edx >>> 19) <<< 2) + load32 s.memory 0x13584) =
    angle.fineCosine.raw.toBitVec
  sine : load32 s.memory (((s.regs edx >>> 19) <<< 2) + 0x5a84) =
    angle.fineSine.raw.toBitVec
  momx : load32 s.memory (load32 s.memory (s.regs eax) + 72) = body.momx.raw.toBitVec
  momy : load32 s.memory (load32 s.memory (s.regs eax) + 76) = body.momy.raw.toBitVec
  playerApart : Apart (s.regs eax) (load32 s.memory (s.regs eax) + 72)
  sineApart : Apart (((s.regs edx >>> 19) <<< 2) + 0x5a84)
    (load32 s.memory (s.regs eax) + 72)

/-- Initialization obligation kept separate from instruction semantics. -/
structure ThrustTables (memory : Memory) : Prop where
  cosinePointer : load32 memory 0x13584 = 0x7a84
  entries : ∀ i : Fin 10240, load32 memory (0x5a84 + BitVec.ofNat 32 (i.val * 4)) =
    (Tables.fineSine.get i).toBitVec

theorem thrust_selected_tables (memory : Memory) (angle : Angle)
    (tables : ThrustTables memory) :
    load32 memory ((angle.raw.toBitVec >>> 19 <<< 2) + load32 memory 0x13584) =
      angle.fineCosine.raw.toBitVec ∧
    load32 memory ((angle.raw.toBitVec >>> 19 <<< 2) + 0x5a84) =
      angle.fineSine.raw.toBitVec := by
  rw [thrust_table_index, tables.cosinePointer]
  have sine := tables.entries ⟨angle.fineIndex.val, by have := angle.fineIndex.isLt; omega⟩
  have cosine := tables.entries ⟨angle.fineIndex.val + 2048, by have := angle.fineIndex.isLt; omega⟩
  have address (n : Nat) : BitVec.ofNat 32 (n * 4) + 0x7a84 =
      0x5a84 + BitVec.ofNat 32 ((n + 2048) * 4) := by
    rw [Nat.add_mul, BitVec.ofNat_add]
    bv_decide
  constructor
  · rw [address]; exact cosine
  · rw [BitVec.add_comm]; exact sine

/-- Construct the input relation from a shared full-table invariant. The
selected lookup obligations need not be discharged anew for every angle. -/
theorem ThrustInputs.of_tables (s : State) (body : Motion) (angle : Angle) (move : Fixed)
    (tables : ThrustTables s.memory)
    (ha : s.regs edx = angle.raw.toBitVec) (hm : s.regs ebx = move.raw.toBitVec)
    (hx : load32 s.memory (load32 s.memory (s.regs eax) + 72) = body.momx.raw.toBitVec)
    (hy : load32 s.memory (load32 s.memory (s.regs eax) + 76) = body.momy.raw.toBitVec)
    (hp : Apart (s.regs eax) (load32 s.memory (s.regs eax) + 72))
    (hs : Apart (((s.regs edx >>> 19) <<< 2) + 0x5a84)
      (load32 s.memory (s.regs eax) + 72)) : ThrustInputs s body angle move := by
  have lookups := thrust_selected_tables s.memory angle tables
  exact ⟨ha, hm, by simpa only [ha] using lookups.1,
    by simpa only [ha] using lookups.2, hx, hy, hp, hs⟩

theorem momentum_apart (obj : Word) : Apart (obj + 76) (obj + 72) := by
  intro i j
  have hi := i.isLt; have hj := j.isLt
  have hi : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by omega
  have hj : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 := by omega
  rcases hi with hi | hi | hi | hi <;> rcases hj with hj | hj | hj | hj <;>
    simp only [hi, hj] <;> bv_decide

theorem thrust_memory_matches_engine (s : State) (body : Motion) (angle : Angle)
    (move : Fixed) (h : ThrustInputs s body angle move) :
    thrustMemory s = thrustResultMemory s body angle move := by
  dsimp only [thrustMemory]
  rw [load_store_apart _ _ _ _ h.playerApart,
      load_store_apart _ _ _ _ h.sineApart,
      load_store_apart _ _ _ _ (momentum_apart _)]
  rw [h.moveReg, h.cosine, h.sine, h.momx, h.momy]
  change store32 (store32 s.memory (load32 s.memory (s.regs eax) + 72)
    (body.momx.raw.toBitVec + mulWord move.raw.toBitVec angle.fineCosine.raw.toBitVec))
    (load32 s.memory (s.regs eax) + 76)
    (body.momy.raw.toBitVec + mulWord move.raw.toBitVec angle.fineSine.raw.toBitVec) =
    store32 (store32 s.memory (load32 s.memory (s.regs eax) + 72)
      (body.momx.raw + (move * angle.fineCosine).raw).toBitVec)
      (load32 s.memory (s.regs eax) + 76)
      (body.momy.raw + (move * angle.fineSine).raw).toBitVec
  simp only [Int32.toBitVec_add, mulWord_fixed]

/-- Universal binary-to-engine momentum correspondence; not a complete player
tic or a claim about arbitrary malformed/aliased game memory. -/
theorem player_thrust_matches_doom19 (s : State) (body : Motion) (angle : Angle)
    (move : Fixed) (h : ThrustInputs s body angle move) :
    (X86Block.run 17 Doom19.playerThrustBytes s).map (·.memory) =
      some (thrustResultMemory s body angle move) := by
  rw [original_thrust_memory, thrust_memory_matches_engine s body angle move h]

/-- The final two momentum words, explicitly projected from the full memory
correspondence theorem. -/
theorem player_thrust_momentum (s : State) (body : Motion) (angle : Angle)
    (move : Fixed) (h : ThrustInputs s body angle move) :
    (X86Block.run 17 Doom19.playerThrustBytes s).map
      (fun t => (load32 t.memory (load32 s.memory (s.regs eax) + 72),
                 load32 t.memory (load32 s.memory (s.regs eax) + 76))) =
    some ((body.thrust angle move).momx.raw.toBitVec,
          (body.thrust angle move).momy.raw.toBitVec) := by
  have hm := player_thrust_matches_doom19 s body angle move h
  have apart : Apart (load32 s.memory (s.regs eax) + 72)
      (load32 s.memory (s.regs eax) + 76) := by
    intro i j
    exact fun he => momentum_apart (load32 s.memory (s.regs eax)) j i he.symm
  have result := congrArg (Option.map (fun m =>
    (load32 m (load32 s.memory (s.regs eax) + 72),
     load32 m (load32 s.memory (s.regs eax) + 76)))) hm
  simpa only [Option.map_map, Function.comp_def, Option.map_some, thrustResultMemory,
    load_store_apart _ _ _ _ apart, load_store] using result

end Doom.Proofs
