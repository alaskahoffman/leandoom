import Doom.Proofs.OriginalMoveJoin

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 3200000
namespace Doom.Proofs
open Verification X86 X86Memory X86Control BlockSummary

def moveMotionBytes := moveJoinBytes ++ Doom19.sideThrustBytes

def sideGuardCore (s : X86Memory.State) : X86Memory.State :=
  { s with
    regs := write s.regs 2
      ((s.regs 2 &&& (0xffff00ff#32)) ||| ((s.memory (s.regs 6 + (1#32))).zeroExtend 32 <<< 8)) }

def sideGuardEnd (s : X86Memory.State) : X86Control.State :=
  ⟨sideGuardCore s,
   some (if s.memory (s.regs 6 + (1#32)) = 0 then logical8 0
     else compare32 (load32 s.memory 0x2cf90) 0), sideGuardResult s⟩

theorem side_guard_full (s : X86Memory.State) (flags : Option Flags) :
    runProgram sideGuardProgram [16,93] 5 ⟨s,flags,0⟩ = some (sideGuardEnd s) := by
  have hv6 : (6 : Reg).val = 6 := rfl
  have hl := high_mask_zero (s.regs 2)
  have hw := write_high_read (s.regs 2) (s.memory (s.regs 6 + (1#32)))
  by_cases hc : s.memory (s.regs 6 + (1#32)) = 0 <;>
    by_cases hg : load32 s.memory (0x2cf90#32) = 0 <;>
    simp [runProgram,sideGuardProgram,X86Control.execute,X86Block.Address.eval,
      putByte,readByte,byteReg,put,write,logical8,sideGuardEnd,sideGuardCore,
      sideGuardResult,hc,hg,hl,hw,hv6]
  all_goals try dsimp only [Word] at *
  all_goals simp_all [write,cmp32_zero]

def sidePackets := (decodePackets 24 Doom19.sideThrustBytes).getD []
def sideEnd (s : X86Memory.State) := X86Block.eval sideThrustOps s

theorem side_linear_motion (s : X86Memory.State) (flags : Option Flags) :
    Prefix (decodeAt moveMotionBytes) [213] 24 ⟨s,flags,136⟩ ⟨sideEnd s,none,213⟩ := by
  have fits : LinearFits (decodeAt moveMotionBytes) [213] 136 sidePackets := by decide
  have path := linear_prefix sidePackets (decodeAt moveMotionBytes) [213] ⟨s,flags,136⟩ fits
  rw [linear_state] at path
  exact path

theorem side_end_memory (s : X86Memory.State) :
    (sideEnd s).memory = inlineThrustMemory s true := by
  have h := original_side_thrust_memory s
  simpa only [X86Block.run,side_thrust_decoded,Option.map_some,Option.some.injEq,sideEnd] using h

theorem motion_contains_guard (pc : Nat) (h : shiftProgram 120 sideGuardProgram pc ≠ none) :
    decodeAt moveMotionBytes pc = shiftProgram 120 sideGuardProgram pc := by
  have hp : 120 ≤ pc := by
    by_cases hp : 120 ≤ pc
    · exact hp
    · simp [shiftProgram,hp] at h
  have cases : pc = 120 ∨ pc = 123 ∨ pc = 125 ∨ pc = 127 ∨ pc = 134 := by
    simp only [shiftProgram,hp,↓reduceIte] at h
    generalize he : pc - 120 = localPC at h
    fun_cases sideGuardProgram localPC <;> simp_all [sideGuardProgram] <;> omega
  rcases cases with h | h | h | h | h <;> subst pc <;> rfl

theorem motion_guard_active (pc : Nat) (h : shiftProgram 120 sideGuardProgram pc ≠ none) :
    pc ∉ [213] := by
  simp only [List.mem_singleton]
  intro eq; subst pc
  contradiction

def sideResultMemory (s : X86Memory.State) : Memory :=
  if sideGuardResult s = 16 then inlineThrustMemory (sideGuardCore s) true else s.memory

/-- The guard and side body share the actual DH register and unchanged memory. -/
theorem motion_side_run (s : X86Memory.State) (flags : Option Flags) :
    (runProgram (decodeAt moveMotionBytes) [213] 29 ⟨s,flags,120⟩).map
      (fun t => (t.pc,t.core.memory)) = some (213,sideResultMemory s) := by
  have shifted := runProgram_shift sideGuardProgram side_guard_forward 120 [16,93] 5 ⟨s,flags,0⟩
  rw [side_guard_full] at shifted
  obtain ⟨k,hk,path,_⟩ := runProgram_path shifted
  have path := path.transfer (decodeAt moveMotionBytes) [213] motion_contains_guard motion_guard_active
  have tail : (runProgram (decodeAt moveMotionBytes) [213] 24 (shiftState 120 (sideGuardEnd s))).map
      (fun t => (t.pc,t.core.memory)) = some (213,sideResultMemory s) := by
    by_cases hs : sideGuardResult s = 16
    · have eq : shiftState 120 (sideGuardEnd s) =
          ⟨sideGuardCore s,(sideGuardEnd s).flags,136⟩ := by simp [shiftState,sideGuardEnd,hs]
      rw [eq,show 24 = 24 + 0 by rfl,(side_linear_motion _ _).run 0]
      simp [runProgram,sideResultMemory,hs,side_end_memory]
    · have he : sideGuardResult s = 93 := by
        unfold sideGuardResult at *; split at * <;> simp_all
      simp [shiftState,sideGuardEnd,he,runProgram,sideResultMemory,sideGuardCore]
  exact path.finish_map tail 29 (by omega)

def afterForward (s : X86Memory.State) (body : Motion) (cmd : Ticcmd) : X86Memory.State :=
  if body.onGround ∧ cmd.forwardMove ≠ 0 then forwardEnd (moveEntryEnd s).core else (moveEntryEnd s).core

theorem motion_contains_entry (pc : Nat) (h : moveEntryProgram pc ≠ none) :
    decodeAt moveMotionBytes pc = moveEntryProgram pc := by
  fun_cases moveEntryProgram pc <;> simp_all [moveEntryProgram] <;> rfl

theorem motion_entry_active (pc : Nat) (h : moveEntryProgram pc ≠ none) : pc ∉ [213] := by
  fun_cases moveEntryProgram pc <;> simp_all [moveEntryProgram]

theorem forward_linear_motion (s : X86Memory.State) (flags : Option Flags) :
    Prefix (decodeAt moveMotionBytes) [213] 23 ⟨s,flags,48⟩ ⟨forwardEnd s,none,120⟩ := by
  have fits : LinearFits (decodeAt moveMotionBytes) [213] 48 forwardPackets := by decide
  have path := linear_prefix forwardPackets (decodeAt moveMotionBytes) [213] ⟨s,flags,48⟩ fits
  rw [linear_state,forward_packets_ops] at path
  exact path

theorem motion_raw_run (s : X86Memory.State) (flags : Option Flags) (body : Motion) (cmd : Ticcmd)
    (h : MoveEntryInputs s body cmd) :
    (X86Control.run moveMotionBytes [213] 69 ⟨s,flags,0⟩).map
      (fun t => (t.pc,t.core.memory)) = some (213,sideResultMemory (afterForward s body cmd)) := by
  obtain ⟨k,hk,path,_⟩ := runProgram_path (move_entry_full s flags)
  have path := path.transfer (decodeAt moveMotionBytes) [213] motion_contains_entry motion_entry_active
  have hp := entry_pc s body cmd h
  have tail : (runProgram (decodeAt moveMotionBytes) [213] 52 (moveEntryEnd s)).map
      (fun t => (t.pc,t.core.memory)) = some (213,sideResultMemory (afterForward s body cmd)) := by
    by_cases hf : body.onGround ∧ cmd.forwardMove ≠ 0
    · rw [if_pos hf] at hp
      have eq : moveEntryEnd s = ⟨(moveEntryEnd s).core,(moveEntryEnd s).flags,48⟩ := by rw [←hp]
      rw [eq,show 52 = 23 + 29 by rfl,(forward_linear_motion _ _).run 29,motion_side_run]
      simp [afterForward,hf]
    · rw [if_neg hf] at hp
      have eq : moveEntryEnd s = ⟨(moveEntryEnd s).core,(moveEntryEnd s).flags,120⟩ := by rw [←hp]
      rw [eq]
      simpa [afterForward,hf] using runProgram_map_mono (motion_side_run (moveEntryEnd s).core (moveEntryEnd s).flags) 23
  exact path.finish_map tail 69 (by omega)

/-- Additional initial layout facts needed to read the tables again after the
forward writes. No assumptions are made about an intermediate state. -/
structure MoveMotionInputs (s : X86Memory.State) (body : Motion) (cmd : Ticcmd) : Prop
    extends MoveJoinInputs s body cmd where
  playerMomy : Apart (s.regs 0) (entryObject s + (76#32))
  pointerMomx : Apart (0x13584#32) (entryObject s + (72#32))
  pointerMomy : Apart (0x13584#32) (entryObject s + (76#32))
  tableMomy : ∀ i : Fin 10240, Apart (0x5a84 + BitVec.ofNat 32 (i.val * 4)) (entryObject s + (76#32))

theorem forward_end_stack (s : X86Memory.State) : (forwardEnd s).regs 4 = s.regs 4 := by
  simp only [forwardEnd,summarized_correct]
  conv => lhs; pattern (forwardThrustOps); reduce
  simp [summarized,X86Block.execute,X86Memory.execute,X86.execute,
    X86Block.Address.eval,put,multiply,write,eax,ebx,edx]

theorem after_forward_pointers (s : X86Memory.State) (body : Motion) (cmd : Ticcmd) :
    (afterForward s body cmd).regs 1 = s.regs 0 ∧
    (afterForward s body cmd).regs 6 = s.regs 0 + (8#32) ∧
    (afterForward s body cmd).regs 4 = s.regs 4 := by
  unfold afterForward; split <;> simp only [forward_end_pointers,forward_end_stack,entry_pointers,and_self]

theorem after_forward_memory (s : X86Memory.State) (body : Motion) (cmd : Ticcmd)
    (h : MoveJoinInputs s body cmd) :
    (afterForward s body cmd).memory = moveJoinResultMemory s body cmd := by
  have hf := entry_establishes_forward_side s body cmd h
  unfold afterForward moveJoinResultMemory
  split
  · rw [forward_end_memory,inline_thrust_matches_engine _ _ _ _ hf.toInlineThrustInputs]
  · exact entry_memory s body cmd h.toMoveEntryInputs

theorem joined_load (s : X86Memory.State) (body : Motion) (cmd : Ticcmd)
    (h : MoveJoinInputs s body cmd) (a : Word)
    (ha : Apart a (entryAngleAddress s)) (hg : Apart a 0x2cf90)
    (hs : Apart a (s.regs 4)) (hx : Apart a (entryObject s + (72#32)))
    (hy : Apart a (entryObject s + (76#32))) :
    load32 (moveJoinResultMemory s body cmd) a = load32 s.memory a := by
  have hp := h.readsProtected (s.regs 0) (by simp)
  have obj : load32 (moveEntryEnd s).core.memory ((moveEntryEnd s).core.regs 1) = entryObject s := by
    rw [(entry_pointers s).1,entry_memory s body cmd h.toMoveEntryInputs,entry_load s body cmd _ hp.1 hp.2]; rfl
  unfold moveJoinResultMemory
  split
  · dsimp only [inlineThrustResult,inlineScratch]
    rw [obj,(entry_pointers s).2.2]
    change load32 (store32 (store32 (store32 (moveEntryEnd s).core.memory (s.regs 4) _)
      (entryObject s + (72#32)) _) (entryObject s + (76#32)) _) a = _
    rw [load_store_apart _ _ _ _ hy,load_store_apart _ _ _ _ hx,load_store_apart _ _ _ _ hs,
      entry_memory s body cmd h.toMoveEntryInputs,entry_load s body cmd _ ha hg]
  · exact entry_load s body cmd a ha hg

theorem joined_tables (s : X86Memory.State) (body : Motion) (cmd : Ticcmd)
    (h : MoveMotionInputs s body cmd) : ThrustTables (moveJoinResultMemory s body cmd) := by
  constructor
  · have hp := h.readsProtected 0x13584 (by simp)
    rw [joined_load s body cmd h.toMoveJoinInputs _ hp.1 hp.2
      (h.scratchProtected _ (by simp)) h.pointerMomx h.pointerMomy]
    exact h.tables.cosinePointer
  · intro i
    have hp := h.tableProtected i
    rw [joined_load s body cmd h.toMoveJoinInputs _ hp.1 hp.2 (h.tableScratch i) (h.tableMomx i) (h.tableMomy i)]
    exact h.tables.entries i

theorem after_forward_guard (s : X86Memory.State) (body : Motion) (cmd : Ticcmd)
    (h : MoveJoinInputs s body cmd) :
    load32 (afterForward s body cmd).memory 0x2cf90 = (if body.onGround then 1 else 0) ∧
    (afterForward s body cmd).memory ((afterForward s body cmd).regs 6 + (1#32)) = cmd.sideMove.toBitVec := by
  have hf := entry_establishes_forward_side s body cmd h
  unfold afterForward
  split
  · exact forward_establishes_side_inputs _ (body.turn cmd.angleTurn) cmd hf
  · exact ⟨hf.ground,hf.side⟩

theorem after_forward_side_pc (s : X86Memory.State) (body : Motion) (cmd : Ticcmd)
    (h : MoveJoinInputs s body cmd) :
    sideGuardResult (afterForward s body cmd) = if body.onGround ∧ cmd.sideMove ≠ 0 then 16 else 93 := by
  have ⟨hg,hc⟩ := after_forward_guard s body cmd h
  exact side_guard_matches_engine _ body cmd hg hc

def sideEntry (s : X86Memory.State) (body : Motion) (cmd : Ticcmd) : X86Memory.State :=
  sideGuardCore (afterForward s body cmd)

theorem side_entry_pointers (s : X86Memory.State) (body : Motion) (cmd : Ticcmd) :
    (sideEntry s body cmd).regs 1 = s.regs 0 ∧ (sideEntry s body cmd).regs 4 = s.regs 4 := by
  simp only [sideEntry,sideGuardCore,write,show (1 : Reg) ≠ 2 by decide,
    show (4 : Reg) ≠ 2 by decide,↓reduceIte]
  exact ⟨(after_forward_pointers s body cmd).1,(after_forward_pointers s body cmd).2.2⟩

theorem side_entry_object (s : X86Memory.State) (body : Motion) (cmd : Ticcmd)
    (h : MoveMotionInputs s body cmd) :
    load32 (sideEntry s body cmd).memory ((sideEntry s body cmd).regs 1) = entryObject s := by
  rw [(side_entry_pointers s body cmd).1]
  change load32 (afterForward s body cmd).memory (s.regs 0) = _
  rw [after_forward_memory s body cmd h.toMoveJoinInputs]
  have hp := h.readsProtected (s.regs 0) (by simp)
  rw [joined_load s body cmd h.toMoveJoinInputs _ hp.1 hp.2
    (h.scratchProtected _ (by simp)) (h.momxProtected _ (by simp)) h.playerMomy]
  rfl

/-- Both thrusts now use a relation derived from the same pre-turn state. -/
theorem motion_establishes_side (s : X86Memory.State) (body : Motion) (cmd : Ticcmd)
    (h : MoveMotionInputs s body cmd) :
    InlineThrustInputs (sideEntry s body cmd) (forwardMotion body cmd) true cmd.sideMove := by
  have hp := side_entry_pointers s body cmd
  have obj := side_entry_object s body cmd h
  have hm : (sideEntry s body cmd).memory = moveJoinResultMemory s body cmd :=
    after_forward_memory s body cmd h.toMoveJoinInputs
  have fields := joined_memory_fields s body cmd h.toMoveJoinInputs
  have angle := congrArg Prod.fst fields
  have mx := congrArg (fun p => p.2.1) fields
  have my := congrArg (fun p => p.2.2) fields
  dsimp only at angle mx my
  have index : inlineIndex (sideEntry s body cmd) true =
      (inlineAim (forwardMotion body cmd) true).raw.toBitVec >>> 19 <<< 2 := by
    unfold inlineIndex inlineAngle
    simp only [↓reduceIte]
    change ((load32 (sideEntry s body cmd).memory
      (load32 (sideEntry s body cmd).memory ((sideEntry s body cmd).regs 1) + (32#32)) - (0x40000000#32)) >>> 19 <<< 2) = _
    rw [obj,hm]
    change ((load32 (moveJoinResultMemory s body cmd) (entryAngleAddress s) - (0x40000000#32)) >>> 19 <<< 2) = _
    rw [angle]; rfl
  have ts := table_separation (inlineAim (forwardMotion body cmd) true) (s.regs 4) h.tableScratch
  have tx := table_separation (inlineAim (forwardMotion body cmd) true) (entryObject s + (72#32)) h.tableMomx
  refine {
    angle := ?_, command := ?_, tables := ?_, momx := ?_, momy := ?_
    scratchPlayer := ?_, scratchPointer := ?_, scratchCosine := ?_, scratchSine := ?_
    scratchMomx := ?_, scratchMomy := ?_, playerApart := ?_, sineApart := ?_ }
  · rw [obj,hm]; exact angle
  · change ((sideGuardCore (afterForward s body cmd)).regs 2).extractLsb' 8 8 = _
    simp only [sideGuardCore,write,↓reduceIte,write_high_read]
    exact (after_forward_guard s body cmd h.toMoveJoinInputs).2
  · rw [hm]; exact joined_tables s body cmd h
  · rw [obj,hm]; exact mx
  · rw [obj,hm]; exact my
  · rw [hp.1,hp.2]; exact h.scratchProtected _ (by simp)
  · rw [hp.2]; exact h.scratchProtected _ (by simp)
  · rw [index,hp.2]; exact ts.1
  · rw [index,hp.2]; exact ts.2
  · rw [obj,hp.2]; exact h.scratchProtected _ (by simp)
  · rw [obj,hp.2]; exact h.scratchProtected _ (by simp)
  · rw [obj,hp.1]; exact h.momxProtected _ (by simp)
  · rw [index,obj]; exact tx.2

def moveMotionResultMemory (s : X86Memory.State) (body : Motion) (cmd : Ticcmd) : Memory :=
  if body.onGround ∧ cmd.sideMove ≠ 0 then
    inlineThrustResult (sideEntry s body cmd) (forwardMotion body cmd) true cmd.sideMove
  else moveJoinResultMemory s body cmd

theorem move_motion_matches_engine (s : X86Memory.State) (flags : Option Flags)
    (body : Motion) (cmd : Ticcmd) (h : MoveMotionInputs s body cmd) :
    (X86Control.run moveMotionBytes [213] 69 ⟨s,flags,0⟩).map
      (fun t => (t.pc,t.core.memory)) = some (213,moveMotionResultMemory s body cmd) := by
  rw [motion_raw_run s flags body cmd h.toMoveEntryInputs]
  unfold sideResultMemory
  rw [after_forward_side_pc s body cmd h.toMoveJoinInputs]
  by_cases hs : body.onGround ∧ cmd.sideMove ≠ 0
  · simp only [if_pos hs,↓reduceIte,moveMotionResultMemory]
    change some (213,inlineThrustMemory (sideEntry s body cmd) true) = _
    rw [inline_thrust_matches_engine _ _ _ _ (motion_establishes_side s body cmd h)]
  · simp only [if_neg hs,show (93 : Nat) ≠ 16 by decide,↓reduceIte,moveMotionResultMemory]
    rw [after_forward_memory s body cmd h.toMoveJoinInputs]

def completeMotion (body : Motion) (cmd : Ticcmd) : Motion :=
  let front := forwardMotion body cmd
  if body.onGround ∧ cmd.sideMove ≠ 0 then
    front.thrust (inlineAim front true) (commandThrust cmd.sideMove)
  else front

theorem motion_memory_fields (s : X86Memory.State) (body : Motion) (cmd : Ticcmd)
    (h : MoveMotionInputs s body cmd) :
    (load32 (moveMotionResultMemory s body cmd) (entryAngleAddress s),
     load32 (moveMotionResultMemory s body cmd) (entryObject s + (72#32)),
     load32 (moveMotionResultMemory s body cmd) (entryObject s + (76#32))) =
    ((completeMotion body cmd).angle.raw.toBitVec,
     (completeMotion body cmd).momx.raw.toBitVec,(completeMotion body cmd).momy.raw.toBitVec) := by
  have hm : (sideEntry s body cmd).memory = moveJoinResultMemory s body cmd :=
    after_forward_memory s body cmd h.toMoveJoinInputs
  have fields := joined_memory_fields s body cmd h.toMoveJoinInputs
  have angle := congrArg Prod.fst fields
  dsimp only at angle
  have xy : Apart (entryObject s + (72#32)) (entryObject s + (76#32)) := by
    intro i j; exact fun eq => momentum_apart (entryObject s) j i eq.symm
  by_cases hs : body.onGround ∧ cmd.sideMove ≠ 0
  · simp only [moveMotionResultMemory,completeMotion,if_pos hs]
    dsimp only [inlineThrustResult,inlineScratch]
    rw [side_entry_object s body cmd h,(side_entry_pointers s body cmd).2]
    change (load32 (store32 (store32 (store32 (sideEntry s body cmd).memory (s.regs 4) _)
      (entryObject s + (72#32)) _) (entryObject s + (76#32)) _) (entryAngleAddress s),
      load32 (store32 (store32 (store32 (sideEntry s body cmd).memory (s.regs 4) _)
      (entryObject s + (72#32)) _) (entryObject s + (76#32)) _) (entryObject s + (72#32)),
      load32 (store32 (store32 (store32 (sideEntry s body cmd).memory (s.regs 4) _)
      (entryObject s + (72#32)) _) (entryObject s + (76#32)) _) (entryObject s + (76#32))) = _
    rw [load_store_apart _ _ _ _ h.angleMomy,load_store_apart _ _ _ _ h.angleMomx,
      load_store_apart _ _ _ _ h.angleScratch,hm,angle,
      load_store_apart _ _ _ _ xy,load_store,load_store]
    rfl
  · simp only [moveMotionResultMemory,completeMotion,if_neg hs]
    exact fields

/-- Projection of the actual engine update, including both animation branches. -/
theorem completeMotion_engine_projection (body : Motion) (cmd : Ticcmd) :
    ((body.movePlayer cmd).angle,(body.movePlayer cmd).momx,(body.movePlayer cmd).momy) =
    ((completeMotion body cmd).angle,(completeMotion body cmd).momx,(completeMotion body cmd).momy) := by
  by_cases hg : body.z.raw ≤ body.floorz.raw <;> by_cases hf : cmd.forwardMove = 0 <;>
    by_cases hs : cmd.sideMove = 0 <;> by_cases hr : body.frame = 0 <;>
    simp [Motion.movePlayer,completeMotion,forwardMotion,inlineAim,commandThrust,
      Motion.turn,Motion.thrust,Motion.onGround,hg,hf,hs,hr]

/-- Universal angle/momentum correspondence for the entire original motion
region. The command is passed unchanged to the actual Lean player update. -/
theorem move_motion_player_observation (s : X86Memory.State) (flags : Option Flags)
    (body : Motion) (cmd : Ticcmd) (h : MoveMotionInputs s body cmd) :
    (X86Control.run moveMotionBytes [213] 69 ⟨s,flags,0⟩).map (fun t =>
      (t.pc,load32 t.core.memory (entryAngleAddress s),
        load32 t.core.memory (entryObject s + (72#32)),
        load32 t.core.memory (entryObject s + (76#32)))) =
      some (213,(body.movePlayer cmd).angle.raw.toBitVec,
        (body.movePlayer cmd).momx.raw.toBitVec,(body.movePlayer cmd).momy.raw.toBitVec) := by
  have observed := congrArg (Option.map (fun p : Nat × Memory =>
    (p.1,load32 p.2 (entryAngleAddress s),load32 p.2 (entryObject s + (72#32)),
      load32 p.2 (entryObject s + (76#32))))) (move_motion_matches_engine s flags body cmd h)
  simp only [Option.map_map,Function.comp_def,Option.map_some,motion_memory_fields s body cmd h] at observed
  have fields := congrArg (fun p : Angle × Fixed × Fixed =>
    (p.1.raw.toBitVec,p.2.1.raw.toBitVec,p.2.2.raw.toBitVec)) (completeMotion_engine_projection body cmd)
  dsimp only at fields
  rw [fields]
  exact observed

end Doom.Proofs
