import Doom.Proofs.OriginalForwardSide
import Doom.Verification.X86Paths

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 3200000
namespace Doom.Proofs
open Verification X86 X86Memory X86Control BlockSummary

def forwardGuardCore (s : X86Memory.State) : X86Memory.State :=
  { regs := write (write (write s.regs 3 (load32 s.memory (load32 s.memory (s.regs 1) + (20#32))))
      0 (if groundFlag s then 1 else 0)) 2
      ((s.regs 2 &&& (0xffffff00#32)) ||| (s.memory (s.regs 6)).zeroExtend 32)
    memory := store32 s.memory 0x2cf90 (if groundFlag s then 1 else 0) }

def forwardGuardEnd (s : X86Memory.State) : X86Control.State :=
  ⟨forwardGuardCore s,
    some (if s.memory (s.regs 6) = 0 then logical8 0 else logical32 (if groundFlag s then 1 else 0)),
    forwardGuardResult s⟩

theorem forward_guard_full (s : X86Memory.State) (flags : Option Flags) :
    runProgram forwardGuardProgram [31,103] 11 ⟨s,flags,0⟩ = some (forwardGuardEnd s) := by
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
      setle_false_mask, setle_true_mask, write_low_read, low_mask_zero, forwardGuardEnd, forwardGuardCore, forwardGuardResult, groundFlag, hf, hg,
      eax]
  all_goals dsimp only [Word] at *
  all_goals simp_all only [hm0, hm1, cmp32_signed_le, BitVec.setWidth_zero, BitVec.or_zero]
  all_goals simp_all (config := { maxSteps := 300000 }) [write]

  all_goals
    funext r
    by_cases h2 : r = 2 <;> by_cases h0 : r = 0 <;> by_cases h3 : r = 3 <;> simp_all [write]

def moveEntryEnd (s : X86Memory.State) : X86Control.State :=
  shiftState 17 (forwardGuardEnd (turnEndCore s))

theorem move_entry_full (s : X86Memory.State) (flags : Option Flags) :
    runProgram moveEntryProgram [48,120] 17 ⟨s,flags,0⟩ = some (moveEntryEnd s) := by
  rw [show 17 = 6 + 11 by rfl, (move_entry_turn_prefix s flags).run 11]
  have shifted := runProgram_shift forwardGuardProgram forward_guard_forward 17 [31,103] 11
    ⟨turnEndCore s,none,0⟩
  have validShift : runProgram (shiftProgram 17 forwardGuardProgram) [48,120] 11
      ⟨turnEndCore s,none,17⟩ ≠ none := by
    change runProgram (shiftProgram 17 forwardGuardProgram) (List.map (17 + ·) [31,103]) 11
      (shiftState 17 ⟨turnEndCore s,none,0⟩) ≠ none
    rw [shifted,forward_guard_full]
    simp
  rw [runProgram_extend _ _ move_entry_contains_guard _ _ _ validShift]
  change runProgram (shiftProgram 17 forwardGuardProgram) (List.map (17 + ·) [31,103]) 11
    (shiftState 17 ⟨turnEndCore s,none,0⟩) = _
  rw [shifted,forward_guard_full]
  rfl


def entryObject (s : X86Memory.State) : Word := load32 s.memory (s.regs 0)
def entryAngleAddress (s : X86Memory.State) : Word := entryObject s + (32#32)

/-- All data and separation assumptions are about memory before turning. The
whole table is protected, so the turned angle need not be predicted at a seam. -/
structure MoveJoinInputs (s : X86Memory.State) (body : Motion) (cmd : Ticcmd) : Prop
    extends MoveEntryInputs s body cmd where
  tables : ThrustTables s.memory
  momx : load32 s.memory (entryObject s + (72#32)) = body.momx.raw.toBitVec
  momy : load32 s.memory (entryObject s + (76#32)) = body.momy.raw.toBitVec
  side : s.memory (s.regs 0 + (9#32)) = cmd.sideMove.toBitVec
  angleScratch : Apart (entryAngleAddress s) (s.regs 4)
  angleMomx : Apart (entryAngleAddress s) (entryObject s + (72#32))
  angleMomy : Apart (entryAngleAddress s) (entryObject s + (76#32))
  readsProtected : ∀ a, a ∈ [s.regs 0, s.regs 0 + (9#32), entryObject s + (72#32),
      entryObject s + (76#32), (0x13584#32)] →
    Apart a (entryAngleAddress s) ∧ Apart a 0x2cf90
  tableProtected : ∀ i : Fin 10240,
    Apart (0x5a84 + BitVec.ofNat 32 (i.val * 4)) (entryAngleAddress s) ∧
    Apart (0x5a84 + BitVec.ofNat 32 (i.val * 4)) 0x2cf90
  scratchProtected : ∀ a, a ∈ [s.regs 0, (0x13584#32), entryObject s + (72#32),
      entryObject s + (76#32), (0x2cf90#32), s.regs 0 + (9#32)] → Apart a (s.regs 4)
  tableScratch : ∀ i : Fin 10240, Apart (0x5a84 + BitVec.ofNat 32 (i.val * 4)) (s.regs 4)
  tableMomx : ∀ i : Fin 10240, Apart (0x5a84 + BitVec.ofNat 32 (i.val * 4)) (entryObject s + (72#32))
  momxProtected : ∀ a, a ∈ [s.regs 0, (0x2cf90#32), s.regs 0 + (9#32)] → Apart a (entryObject s + (72#32))
  momyProtected : ∀ a, a ∈ [(0x2cf90#32), s.regs 0 + (9#32)] → Apart a (entryObject s + (76#32))

theorem entry_memory (s : X86Memory.State) (body : Motion) (cmd : Ticcmd)
    (h : MoveEntryInputs s body cmd) :
    (moveEntryEnd s).core.memory = moveEntryResultMemory s body cmd := by
  have ⟨hz,hf,_⟩ := turn_establishes_guard_inputs s body cmd h
  have hg := ground_flag_matches_engine (turnEndCore s) body hz hf
  dsimp only [moveEntryEnd,shiftState,forwardGuardEnd,forwardGuardCore]
  rw [hg]
  simp only [turnEndCore,h.angle,h.turn,turn_shift_matches_engine,decide_eq_true_eq,moveEntryResultMemory]

theorem entry_pointers (s : X86Memory.State) :
    (moveEntryEnd s).core.regs 1 = s.regs 0 ∧
    (moveEntryEnd s).core.regs 6 = s.regs 0 + (8#32) ∧
    (moveEntryEnd s).core.regs 4 = s.regs 4 := by
  simp [moveEntryEnd,shiftState,forwardGuardEnd,forwardGuardCore,turnEndCore,write,eax,ebx,ecx,esi]

theorem entry_command (s : X86Memory.State) (body : Motion) (cmd : Ticcmd)
    (h : MoveEntryInputs s body cmd) :
    inlineCommand (moveEntryEnd s).core false = cmd.forwardMove.toBitVec := by
  have hc := (turn_establishes_guard_inputs s body cmd h).2.2
  simp only [inlineCommand,moveEntryEnd,shiftState,forwardGuardEnd,forwardGuardCore]
  change ((s.regs 2 &&& (0xffffff00#32)) ||| ((turnEndCore s).memory ((turnEndCore s).regs 6)).zeroExtend 32).extractLsb' 0 8 = _
  rw [write_low_read,hc]

theorem entry_load (s : X86Memory.State) (body : Motion) (cmd : Ticcmd) (a : Word)
    (ha : Apart a (entryAngleAddress s)) (hg : Apart a 0x2cf90) :
    load32 (moveEntryResultMemory s body cmd) a = load32 s.memory a := by
  unfold moveEntryResultMemory
  dsimp only [entryAngleAddress,entryObject] at ha
  rw [load_store_apart _ _ _ _ hg,load_store_apart _ _ _ _ ha]

theorem entry_byte (s : X86Memory.State) (body : Motion) (cmd : Ticcmd) (a : Word)
    (ha : Apart a (entryAngleAddress s)) (hg : Apart a 0x2cf90) :
    moveEntryResultMemory s body cmd a = s.memory a := by
  unfold moveEntryResultMemory
  dsimp only [entryAngleAddress,entryObject] at ha
  rw [byte_store_apart _ _ _ _ hg,byte_store_apart _ _ _ _ ha]

/-- Derive the original table invariant after both entry writes. -/
theorem entry_tables (s : X86Memory.State) (body : Motion) (cmd : Ticcmd)
    (h : MoveJoinInputs s body cmd) : ThrustTables (moveEntryResultMemory s body cmd) := by
  constructor
  · have hp := h.readsProtected 0x13584 (by simp)
    rw [entry_load s body cmd _ hp.1 hp.2]
    exact h.tables.cosinePointer
  · intro i
    have hp := h.tableProtected i
    rw [entry_load s body cmd _ hp.1 hp.2]
    exact h.tables.entries i


theorem table_separation (angle : Angle) (b : Word)
    (h : ∀ i : Fin 10240, Apart (0x5a84 + BitVec.ofNat 32 (i.val*4)) b) :
    Apart ((angle.raw.toBitVec >>> 19 <<< 2) + 0x7a84) b ∧
    Apart ((angle.raw.toBitVec >>> 19 <<< 2) + 0x5a84) b := by
  rw [thrust_table_index]
  have hs := h ⟨angle.fineIndex.val,by have := angle.fineIndex.isLt; omega⟩
  have hc := h ⟨angle.fineIndex.val+2048,by have := angle.fineIndex.isLt; omega⟩
  have address (n : Nat) : BitVec.ofNat 32 (n*4) + 0x7a84 =
      0x5a84 + BitVec.ofNat 32 ((n+2048)*4) := by
    rw [Nat.add_mul,BitVec.ofNat_add]
    bv_decide
  exact ⟨by rw [address]; exact hc, by rw [BitVec.add_comm]; exact hs⟩

/-- The complete downstream relation follows from initial data and layout;
there are no new assumptions about the intermediate machine state. -/
theorem entry_establishes_forward_side (s : X86Memory.State) (body : Motion) (cmd : Ticcmd)
    (h : MoveJoinInputs s body cmd) :
    ForwardSideInputs (moveEntryEnd s).core (body.turn cmd.angleTurn) cmd := by
  have pointers := entry_pointers s
  have hm := entry_memory s body cmd h.toMoveEntryInputs
  have hp := h.readsProtected (s.regs 0) (by simp)
  have hx := h.readsProtected (entryObject s + (72#32)) (by simp)
  have hy := h.readsProtected (entryObject s + (76#32)) (by simp)
  have hc := h.readsProtected (s.regs 0 + (9#32)) (by simp)
  have obj : load32 (moveEntryEnd s).core.memory ((moveEntryEnd s).core.regs 1) = entryObject s := by
    rw [pointers.1,hm,entry_load s body cmd _ hp.1 hp.2]
    rfl
  have angle : load32 (moveEntryEnd s).core.memory
      (load32 (moveEntryEnd s).core.memory ((moveEntryEnd s).core.regs 1) + (32#32)) =
      (body.turn cmd.angleTurn).angle.raw.toBitVec := by
    rw [obj,hm]
    unfold moveEntryResultMemory
    dsimp only [entryObject]
    rw [load_store_apart _ _ _ _ h.groundApartAngle,load_store]
  have index : inlineIndex (moveEntryEnd s).core false =
      (body.turn cmd.angleTurn).angle.raw.toBitVec >>> 19 <<< 2 := by
    unfold inlineIndex inlineAngle
    simp only [Bool.false_eq_true, ↓reduceIte]
    change (load32 (moveEntryEnd s).core.memory
      (load32 (moveEntryEnd s).core.memory ((moveEntryEnd s).core.regs 1) + (32#32)) >>> 19 <<< 2) = _
    rw [angle]
  have tableStack := table_separation (body.turn cmd.angleTurn).angle (s.regs 4) h.tableScratch
  have tableX := table_separation (body.turn cmd.angleTurn).angle (entryObject s + (72#32)) h.tableMomx
  refine {
    angle := angle
    command := entry_command s body cmd h.toMoveEntryInputs
    tables := by rw [hm]; exact entry_tables s body cmd h
    momx := ?_, momy := ?_
    scratchPlayer := ?_, scratchPointer := ?_, scratchCosine := ?_, scratchSine := ?_
    scratchMomx := ?_, scratchMomy := ?_, playerApart := ?_, sineApart := ?_
    ground := ?_, side := ?_
    groundScratch := ?_, groundMomx := ?_, groundMomy := ?_
    sideScratch := ?_, sideMomx := ?_, sideMomy := ?_ }
  · rw [obj,hm]
    change load32 (moveEntryResultMemory s body cmd) (entryObject s + (72#32)) = body.momx.raw.toBitVec
    rw [entry_load s body cmd _ hx.1 hx.2]; exact h.momx
  · rw [obj,hm]
    change load32 (moveEntryResultMemory s body cmd) (entryObject s + (76#32)) = body.momy.raw.toBitVec
    rw [entry_load s body cmd _ hy.1 hy.2]; exact h.momy
  · rw [pointers.1,pointers.2.2]; exact h.scratchProtected _ (by simp)
  · rw [pointers.2.2]; exact h.scratchProtected _ (by simp)
  · rw [index,pointers.2.2]; exact tableStack.1
  · rw [index,pointers.2.2]; exact tableStack.2
  · rw [obj,pointers.2.2]; exact h.scratchProtected _ (by simp)
  · rw [obj,pointers.2.2]; exact h.scratchProtected _ (by simp)
  · rw [obj,pointers.1]; exact h.momxProtected _ (by simp)
  · rw [obj,index]; exact tableX.2
  · rw [hm]; unfold moveEntryResultMemory; rw [load_store]; rfl
  · rw [pointers.2.1,hm]
    rw [show s.regs 0 + (8#32) + (1#32) = s.regs 0 + (9#32) by rw [BitVec.add_assoc]; rfl]
    rw [entry_byte s body cmd _ hc.1 hc.2]; exact h.side
  · rw [pointers.2.2]; exact h.scratchProtected _ (by simp)
  · rw [obj]; exact h.momxProtected _ (by simp)
  · rw [obj]; exact h.momyProtected _ (by simp)
  · rw [pointers.2.1,pointers.2.2]
    simp only [BitVec.add_assoc]; exact h.scratchProtected _ (by simp)
  · rw [pointers.2.1,obj]
    simp only [BitVec.add_assoc]; exact h.momxProtected _ (by simp)
  · rw [pointers.2.1,obj]
    simp only [BitVec.add_assoc]; exact h.momyProtected _ (by simp)


def moveJoinBytes := moveEntryBytes ++ forwardSideBytes

theorem join_contains_entry (pc : Nat) (h : moveEntryProgram pc ≠ none) :
    decodeAt moveJoinBytes pc = moveEntryProgram pc := by
  fun_cases moveEntryProgram pc <;> simp_all [moveEntryProgram] <;> rfl

theorem join_entry_active (pc : Nat) (h : moveEntryProgram pc ≠ none) :
    pc ∉ [136,213] := by
  fun_cases moveEntryProgram pc <;> simp_all [moveEntryProgram]

theorem join_contains_suffix (pc : Nat) (h : shiftProgram 48 (decodeAt forwardSideBytes) pc ≠ none) :
    decodeAt moveJoinBytes pc = shiftProgram 48 (decodeAt forwardSideBytes) pc := by
  have hp : 48 ≤ pc := by
    by_cases hp : 48 ≤ pc
    · exact hp
    · simp [shiftProgram,hp] at h
  simp only [shiftProgram,hp,↓reduceIte]
  have eq : pc = 48 + (pc-48) := by omega
  conv => lhs; rw [eq]
  exact decodeAt_append moveEntryBytes forwardSideBytes (pc-48)

private theorem map_valid {α β : Type} {v : Option α} {f : α → β} {b : β}
    (h : v.map f = some b) : v ≠ none := by cases v <;> simp_all

theorem join_suffix (fuel : Nat) (s : X86Control.State)
    (valid : X86Control.run forwardSideBytes [88,165] fuel s ≠ none) :
    X86Control.run moveJoinBytes [136,213] fuel (shiftState 48 s) =
      (X86Control.run forwardSideBytes [88,165] fuel s).map (shiftState 48) := by
  have forward := decoded_forward forwardSideBytes (by decide)
  have shifted := runProgram_shift (decodeAt forwardSideBytes) forward 48 [88,165] fuel s
  have validShift : runProgram (shiftProgram 48 (decodeAt forwardSideBytes)) [136,213] fuel
      (shiftState 48 s) ≠ none := by
    change runProgram (shiftProgram 48 (decodeAt forwardSideBytes)) (List.map (48 + ·) [88,165]) fuel
      (shiftState 48 s) ≠ none
    rw [shifted]
    simpa [X86Control.run] using valid
  unfold X86Control.run
  rw [runProgram_extend _ _ join_contains_suffix _ _ _ validShift]
  exact shifted

theorem entry_pc (s : X86Memory.State) (body : Motion) (cmd : Ticcmd)
    (h : MoveEntryInputs s body cmd) :
    (moveEntryEnd s).pc = if body.onGround ∧ cmd.forwardMove ≠ 0 then 48 else 120 := by
  have ⟨hz,hf,hc⟩ := turn_establishes_guard_inputs s body cmd h
  change 17 + forwardGuardResult (turnEndCore s) = _
  rw [forward_guard_matches_engine _ body cmd hz hf hc]
  by_cases takeForward : body.onGround ∧ cmd.forwardMove ≠ 0 <;> simp [takeForward]

def moveJoinResultMemory (s : X86Memory.State) (body : Motion) (cmd : Ticcmd) : Memory :=
  if body.onGround ∧ cmd.forwardMove ≠ 0 then
    inlineThrustResult (moveEntryEnd s).core (body.turn cmd.angleTurn) false cmd.forwardMove
  else moveEntryResultMemory s body cmd

theorem joined_suffix_engine (s : X86Memory.State) (body : Motion) (cmd : Ticcmd)
    (h : MoveJoinInputs s body cmd) :
    (X86Control.run moveJoinBytes [136,213] 28 (moveEntryEnd s)).map
      (fun t => (t.pc,t.core.memory)) =
      some (if body.onGround ∧ cmd.sideMove ≠ 0 then 136 else 213, moveJoinResultMemory s body cmd) := by
  have relation := entry_establishes_forward_side s body cmd h
  have hp := entry_pc s body cmd h.toMoveEntryInputs
  have shift_eq (pc : Nat) (he : (moveEntryEnd s).pc = 48 + pc) :
      moveEntryEnd s = shiftState 48 ⟨(moveEntryEnd s).core,(moveEntryEnd s).flags,pc⟩ := by
    cases hh : moveEntryEnd s
    simp_all [shiftState]
  by_cases takeForward : body.onGround ∧ cmd.forwardMove ≠ 0
  · have localResult := forward_side_matches_engine (moveEntryEnd s).core (moveEntryEnd s).flags
      (body.turn cmd.angleTurn) cmd relation
    rw [shift_eq 0 (by simpa [takeForward] using hp),join_suffix _ _ (map_valid localResult)]
    have shifted := congrArg (Option.map (fun p : Nat × Memory => (48+p.1,p.2))) localResult
    simp only [moveJoinResultMemory,if_pos takeForward]
    by_cases grounded : body.onGround <;> by_cases sideZero : cmd.sideMove = 0 <;>
      simpa [Option.map_map,Function.comp_def,shiftState,grounded,sideZero,
      show (body.turn cmd.angleTurn).onGround ↔ body.onGround from Iff.rfl] using shifted
  · have localResult := skip_forward_side_matches_engine (moveEntryEnd s).core (moveEntryEnd s).flags
      (body.turn cmd.angleTurn) cmd relation.ground relation.side
    have extended := runProgram_map_mono localResult 23
    rw [shift_eq 72 (by simpa [takeForward] using hp),join_suffix _ _ (map_valid extended)]
    have shifted := congrArg (Option.map (fun p : Nat × Memory => (48+p.1,p.2))) extended
    have hm := entry_memory s body cmd h.toMoveEntryInputs
    simp only [moveJoinResultMemory,if_neg takeForward]
    by_cases grounded : body.onGround <;> by_cases sideZero : cmd.sideMove = 0 <;>
      simpa [X86Control.run,Option.map_map,Function.comp_def,shiftState,grounded,sideZero,hm,
      show (body.turn cmd.angleTurn).onGround ↔ body.onGround from Iff.rfl] using shifted

/-- One entry relation, one uninterrupted original-byte execution: turn, choose
and optionally perform forward thrust, then choose the side-thrust branch. -/
theorem move_join_matches_engine (s : X86Memory.State) (flags : Option Flags)
    (body : Motion) (cmd : Ticcmd) (h : MoveJoinInputs s body cmd) :
    (X86Control.run moveJoinBytes [136,213] 45 ⟨s,flags,0⟩).map
      (fun t => (t.pc,t.core.memory)) =
      some (if body.onGround ∧ cmd.sideMove ≠ 0 then 136 else 213, moveJoinResultMemory s body cmd) := by
  obtain ⟨k,hk,path,_⟩ := runProgram_path (move_entry_full s flags)
  have joined := path.transfer (decodeAt moveJoinBytes) [136,213] join_contains_entry join_entry_active
  exact joined.finish_map (joined_suffix_engine s body cmd h) 45 (by omega)


def forwardMotion (body : Motion) (cmd : Ticcmd) : Motion :=
  let turned := body.turn cmd.angleTurn
  if body.onGround ∧ cmd.forwardMove ≠ 0 then
    turned.thrust turned.angle (commandThrust cmd.forwardMove)
  else turned

theorem joined_memory_fields (s : X86Memory.State) (body : Motion) (cmd : Ticcmd)
    (h : MoveJoinInputs s body cmd) :
    (load32 (moveJoinResultMemory s body cmd) (entryAngleAddress s),
     load32 (moveJoinResultMemory s body cmd) (entryObject s + (72#32)),
     load32 (moveJoinResultMemory s body cmd) (entryObject s + (76#32))) =
    ((forwardMotion body cmd).angle.raw.toBitVec,
     (forwardMotion body cmd).momx.raw.toBitVec,
     (forwardMotion body cmd).momy.raw.toBitVec) := by
  have hm := entry_memory s body cmd h.toMoveEntryInputs
  have pointers := entry_pointers s
  have hp := h.readsProtected (s.regs 0) (by simp)
  have hx := h.readsProtected (entryObject s + (72#32)) (by simp)
  have hy := h.readsProtected (entryObject s + (76#32)) (by simp)
  have obj : load32 (moveEntryEnd s).core.memory ((moveEntryEnd s).core.regs 1) = entryObject s := by
    rw [pointers.1,hm,entry_load s body cmd _ hp.1 hp.2]; rfl
  have angle : load32 (moveEntryResultMemory s body cmd) (entryAngleAddress s) =
      (body.turn cmd.angleTurn).angle.raw.toBitVec := by
    unfold moveEntryResultMemory
    dsimp only [entryAngleAddress,entryObject]
    rw [load_store_apart _ _ _ _ h.groundApartAngle,load_store]
  have xy : Apart (entryObject s + (72#32)) (entryObject s + (76#32)) := by
    intro i j; exact fun eq => momentum_apart (entryObject s) j i eq.symm
  by_cases takeForward : body.onGround ∧ cmd.forwardMove ≠ 0
  · simp only [moveJoinResultMemory,forwardMotion,if_pos takeForward]
    dsimp only [inlineThrustResult,inlineScratch,inlineAim]
    rw [obj,pointers.2.2]
    let result := (body.turn cmd.angleTurn).thrust (body.turn cmd.angleTurn).angle (commandThrust cmd.forwardMove)
    let memory := store32 (store32
      (store32 (moveEntryEnd s).core.memory (s.regs 4) (inlineIndex (moveEntryEnd s).core false))
      (entryObject s + (72#32)) result.momx.raw.toBitVec) (entryObject s + (76#32)) result.momy.raw.toBitVec
    change (load32 memory (entryAngleAddress s),load32 memory (entryObject s + (72#32)),
      load32 memory (entryObject s + (76#32))) = _
    dsimp only [memory]
    rw [load_store_apart _ _ _ _ h.angleMomy,load_store_apart _ _ _ _ h.angleMomx,
      load_store_apart _ _ _ _ h.angleScratch,hm,angle,
      load_store_apart _ _ _ _ xy,load_store,load_store]
    rfl
  · simp only [moveJoinResultMemory,forwardMotion,if_neg takeForward]
    rw [angle,entry_load s body cmd _ hx.1 hx.2,entry_load s body cmd _ hy.1 hy.2,h.momx,h.momy]
    rfl

/-- Observable angle and momentum at the side-thrust decision, from one
initial-state relation and the same uninterrupted original-byte run. -/
theorem move_join_observation (s : X86Memory.State) (flags : Option Flags)
    (body : Motion) (cmd : Ticcmd) (h : MoveJoinInputs s body cmd) :
    (X86Control.run moveJoinBytes [136,213] 45 ⟨s,flags,0⟩).map (fun t =>
      (t.pc,load32 t.core.memory (entryAngleAddress s),
        load32 t.core.memory (entryObject s + (72#32)),
        load32 t.core.memory (entryObject s + (76#32)))) =
      some (if body.onGround ∧ cmd.sideMove ≠ 0 then 136 else 213,
        (forwardMotion body cmd).angle.raw.toBitVec,
        (forwardMotion body cmd).momx.raw.toBitVec,
        (forwardMotion body cmd).momy.raw.toBitVec) := by
  have result := congrArg (Option.map (fun p : Nat × Memory =>
    (p.1,load32 p.2 (entryAngleAddress s),load32 p.2 (entryObject s + (72#32)),
      load32 p.2 (entryObject s + (76#32))))) (move_join_matches_engine s flags body cmd h)
  simpa only [Option.map_map,Function.comp_def,Option.map_some,joined_memory_fields s body cmd h] using result

theorem forwardMotion_engine_projection (body : Motion) (cmd : Ticcmd) :
    ((body.movePlayer {cmd with sideMove := 0}).angle,
     (body.movePlayer {cmd with sideMove := 0}).momx,
     (body.movePlayer {cmd with sideMove := 0}).momy) =
    ((forwardMotion body cmd).angle,(forwardMotion body cmd).momx,(forwardMotion body cmd).momy) := by
  by_cases hg : body.z.raw ≤ body.floorz.raw <;> by_cases hf : cmd.forwardMove = 0 <;>
    by_cases hr : body.frame = 0 <;>
    simp [Motion.movePlayer,forwardMotion,commandThrust,Motion.turn,Motion.thrust,Motion.onGround,hg,hf,hr]

theorem move_join_player_observation (s : X86Memory.State) (flags : Option Flags)
    (body : Motion) (cmd : Ticcmd) (h : MoveJoinInputs s body cmd) :
    (X86Control.run moveJoinBytes [136,213] 45 ⟨s,flags,0⟩).map (fun t =>
      (t.pc,load32 t.core.memory (entryAngleAddress s),
        load32 t.core.memory (entryObject s + (72#32)),
        load32 t.core.memory (entryObject s + (76#32)))) =
      some (if body.onGround ∧ cmd.sideMove ≠ 0 then 136 else 213,
        (body.movePlayer {cmd with sideMove := 0}).angle.raw.toBitVec,
        (body.movePlayer {cmd with sideMove := 0}).momx.raw.toBitVec,
        (body.movePlayer {cmd with sideMove := 0}).momy.raw.toBitVec) := by
  have fields := congrArg (fun p : Angle × Fixed × Fixed =>
    (p.1.raw.toBitVec,p.2.1.raw.toBitVec,p.2.2.raw.toBitVec)) (forwardMotion_engine_projection body cmd)
  change ((body.movePlayer {cmd with sideMove := 0}).angle.raw.toBitVec,
    (body.movePlayer {cmd with sideMove := 0}).momx.raw.toBitVec,
    (body.movePlayer {cmd with sideMove := 0}).momy.raw.toBitVec) =
    ((forwardMotion body cmd).angle.raw.toBitVec,(forwardMotion body cmd).momx.raw.toBitVec,
      (forwardMotion body cmd).momy.raw.toBitVec) at fields
  rw [fields]
  exact move_join_observation s flags body cmd h

end Doom.Proofs

