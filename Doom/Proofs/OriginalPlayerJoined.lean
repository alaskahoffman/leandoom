import Doom.Proofs.OriginalMotionState
import Doom.Proofs.OriginalPlayerAnimation
import Doom.Verification.X86RoutineBridge

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 6400000
namespace Doom.Proofs
open Verification X86 X86Memory X86Control BlockSummary
namespace PlayerJoined

def callerBytes := moveMotionBytes ++ Doom19.playerAnimationBytes

/-- Absolute DOS code-object offsets, including actual saved CALL return words. -/
def bytesProgram (caller callee : List UInt8) : X86Routine.Program := fun pc =>
  if 0x33169 ≤ pc ∧ pc < 0x33169 + caller.length then X86Routine.decodeAt caller (pc-0x33169)
  else if 0x30ea0 ≤ pc ∧ pc < 0x30ea0+callee.length then X86Routine.decodeAt callee (pc-0x30ea0) else none

def program := bytesProgram callerBytes Doom19.setMobjStateBytes

theorem motion_decoded (pc : Nat) (op : X86Control.Op) (len : Nat)
    (h : X86Control.decodeAt moveMotionBytes pc = some (op,len)) :
    program (0x33169+pc) = some (.control op,len) := by
  have bound := X86Routine.control_decode_bound moveMotionBytes pc (by simp [h])
  change pc < 213 at bound
  have checked : ∀ i : Fin 213, (X86Control.decodeAt moveMotionBytes i.val).isSome →
      X86Routine.decodeAt callerBytes i.val =
        (X86Control.decodeAt moveMotionBytes i.val).map (fun (op,len) => (.control op,len)) := by decide
  have hc := checked ⟨pc,bound⟩ (by simp [h])
  rw [h] at hc
  unfold program bytesProgram
  rw [if_pos (show 0x33169 ≤ 0x33169+pc ∧ 0x33169+pc < 0x33169+callerBytes.length by change _ ∧ _ < 0x33169+245; omega)]
  simpa using hc

theorem motion_active (pc : Nat) (h : X86Control.decodeAt moveMotionBytes pc ≠ none) :
    0x33169+pc ∉ [0x3325e] := by
  have bound := X86Routine.control_decode_bound moveMotionBytes pc h
  change pc < 213 at bound
  simp only [List.mem_singleton]; omega

theorem contains_animation (pc : Nat) (h : PlayerAnimation.program pc ≠ none) :
    program pc = PlayerAnimation.program pc := by
  by_cases hp : 0x3323e ≤ pc
  · simp only [PlayerAnimation.program,hp,↓reduceIte] at h ⊢
    have bound := PlayerAnimation.caller_bound _ h
    unfold program bytesProgram
    rw [if_pos (show 0x33169 ≤ pc ∧ pc < 0x33169+callerBytes.length by change _ ∧ pc < 0x33169+245; omega)]
    have eq : pc-0x33169 = 213+(pc-0x3323e) := by omega
    rw [eq]
    change X86Routine.decodeAt (moveMotionBytes ++ Doom19.playerAnimationBytes)
      (moveMotionBytes.length+(pc-0x3323e)) = _
    rw [X86Routine.decodeAt_append]
    exact PlayerAnimation.caller_decoded _ h
  · by_cases hn : 0x30ea0 ≤ pc
    · simp only [PlayerAnimation.program,hp,hn,↓reduceIte] at h ⊢
      have bound := PlayerAnimation.callee_bound _ h
      unfold program bytesProgram
      rw [if_neg (by omega),if_pos (show 0x30ea0 ≤ pc ∧ pc < 0x30ea0+Doom19.setMobjStateBytes.length by change _ ∧ pc < 0x30ea0+91; omega)]
      exact PlayerAnimation.callee_decoded _ h
    · simp [PlayerAnimation.program,hp,hn] at h

def motionWrites (s : X86Memory.State) : List Word :=
  [entryAngleAddress s,0x2cf90,s.regs 4,entryObject s+(72#32),entryObject s+(76#32)]

theorem motion_load (s : X86Memory.State) (body : Motion) (cmd : Ticcmd)
    (h : MoveMotionInputs s body cmd) (a : Word)
    (safe : ∀ b, b ∈ motionWrites s → Apart a b) :
    load32 (moveMotionResultMemory s body cmd) a = load32 s.memory a := by
  have ha := safe (entryAngleAddress s) (by simp [motionWrites])
  have hg := safe 0x2cf90 (by simp [motionWrites])
  have hs := safe (s.regs 4) (by simp [motionWrites])
  have hx := safe (entryObject s+(72#32)) (by simp [motionWrites])
  have hy := safe (entryObject s+(76#32)) (by simp [motionWrites])
  unfold moveMotionResultMemory
  split
  · dsimp only [inlineThrustResult,inlineScratch]
    rw [side_entry_object s body cmd h,(side_entry_pointers s body cmd).2]
    change load32 (store32 (store32 (store32 (sideEntry s body cmd).memory (s.regs 4) _)
      (entryObject s+(72#32)) _) (entryObject s+(76#32)) _) a = _
    rw [load_store_apart _ _ _ _ hy,load_store_apart _ _ _ _ hx,load_store_apart _ _ _ _ hs]
    change load32 (afterForward s body cmd).memory a = _
    rw [after_forward_memory s body cmd h.toMoveJoinInputs]
    exact joined_load s body cmd h.toMoveJoinInputs a ha hg hs hx hy
  · exact joined_load s body cmd h.toMoveJoinInputs a ha hg hs hx hy

theorem motion_byte (s : X86Memory.State) (body : Motion) (cmd : Ticcmd)
    (h : MoveMotionInputs s body cmd) (a : Word)
    (safe : ∀ b, b ∈ motionWrites s → Apart a b) :
    moveMotionResultMemory s body cmd a = s.memory a := by
  have h := congrArg (fun v : Word => v.extractLsb' 0 8) (motion_load s body cmd h a safe)
  have low (a b c d : BitVec 8) : ((d ++ c) ++ (b ++ a)).extractLsb' 0 8 = a := by bv_decide
  simpa only [load32,low] using h

def animationReads (s : X86Memory.State) : List Word :=
  PlayerAnimation.tableWords ++ [s.regs 0,s.regs 0+(8#32),s.regs 0+(9#32),
    entryObject s+(100#32),entryObject s+(96#32)]

def animationWrites (s : X86Memory.State) : List Word :=
  PlayerAnimation.fields (entryObject s) ++ [s.regs 4-(4#32),s.regs 4-(8#32),s.regs 4-(12#32)]

/-- Every data/layout premise is about the state before turning. No animation
or callee relation is supplied at an intermediate boundary. -/
structure Inputs (s : X86Memory.State) (body : Motion) (anim : PlayerAnim.State) (cmd : Ticcmd) : Prop
    extends MoveMotionInputs s body cmd where
  animationTable : PlayerAnimation.RunTable s.memory
  animationFrame : load32 s.memory (entryObject s+(100#32)) = PlayerAnimation.statePointer anim.frame
  frameBound : anim.frame < 65536
  animationTics : load32 s.memory (entryObject s+(96#32)) = anim.tics.toBitVec
  readsSafe : ∀ a, a ∈ animationReads s → ∀ b, b ∈ motionWrites s → Apart a b
  animationTableSafe : ∀ a, a ∈ PlayerAnimation.tableWords → ∀ b, b ∈ animationWrites s → Apart a b
  stackSafe : ∀ a, a ∈ [s.regs 4-(4#32),s.regs 4-(8#32),s.regs 4-(12#32)] →
    ∀ b, b ∈ PlayerAnimation.fields (entryObject s) → Apart a b
  motionSafe : ∀ a, a ∈ [entryAngleAddress s,entryObject s+(72#32),entryObject s+(76#32)] →
    ∀ b, b ∈ animationWrites s → Apart a b

theorem end_load (s : X86Memory.State) (body : Motion) (anim : PlayerAnim.State) (cmd : Ticcmd)
    (h : Inputs s body anim cmd) (a : Word) (ha : a ∈ animationReads s) :
    load32 (motionEnd s body cmd).core.memory a = load32 s.memory a := by
  rw [(motion_end_memory_pc s none body cmd h.toMoveMotionInputs).2]
  exact motion_load s body cmd h.toMoveMotionInputs a (h.readsSafe a ha)

theorem end_object (s : X86Memory.State) (body : Motion) (anim : PlayerAnim.State) (cmd : Ticcmd)
    (h : Inputs s body anim cmd) : PlayerAnimation.object (motionEnd s body cmd).core = entryObject s := by
  unfold PlayerAnimation.object
  rw [(motion_end_pointers s body cmd).1,end_load s body anim cmd h _ (by simp [animationReads])]
  rfl

theorem establishes_animation (s : X86Memory.State) (body : Motion) (anim : PlayerAnim.State) (cmd : Ticcmd)
    (h : Inputs s body anim cmd) : PlayerAnimation.EngineInputs (motionEnd s body cmd).core anim cmd := by
  have ptr := motion_end_pointers s body cmd
  have obj := end_object s body anim cmd h
  have mem := (motion_end_memory_pc s none body cmd h.toMoveMotionInputs).2
  constructor
  · constructor
    · constructor
      · rw [end_load s body anim cmd h _ (by simp [animationReads,PlayerAnimation.tableWords])]; exact h.animationTable.sprite
      · rw [end_load s body anim cmd h _ (by simp [animationReads,PlayerAnimation.tableWords])]; exact h.animationTable.frame
      · rw [end_load s body anim cmd h _ (by simp [animationReads,PlayerAnimation.tableWords])]; exact h.animationTable.tics
      · rw [end_load s body anim cmd h _ (by simp [animationReads,PlayerAnimation.tableWords])]; exact h.animationTable.action
      · rw [end_load s body anim cmd h _ (by simp [animationReads,PlayerAnimation.tableWords])]; exact h.animationTable.next
    · intro a ha b hb
      rw [obj,ptr.2.2] at hb
      exact h.animationTableSafe a ha b hb
    · intro a ha b hb
      rw [ptr.2.2] at ha; rw [obj] at hb
      exact h.stackSafe a ha b hb
  · rw [ptr.2.1,mem,motion_byte s body cmd h.toMoveMotionInputs _ (h.readsSafe _ (by simp [animationReads]))]
    exact h.forward
  · rw [ptr.2.1,mem]
    rw [show s.regs 0+(8#32)+(1#32) = s.regs 0+(9#32) by rw [BitVec.add_assoc]; rfl]
    rw [motion_byte s body cmd h.toMoveMotionInputs _ (h.readsSafe _ (by simp [animationReads]))]
    exact h.side
  · rw [obj,end_load s body anim cmd h _ (by simp [animationReads])]; exact h.animationFrame
  · exact h.frameBound
  · rw [obj,end_load s body anim cmd h _ (by simp [animationReads])]; exact h.animationTics

/-- One continuous original-byte run, including both thrust branches and the
actual state-setting call when selected. All premises describe the pre-turn state. -/
theorem joined_execution (s : X86Memory.State) (flags : Option Flags)
    (body : Motion) (anim : PlayerAnim.State) (cmd : Ticcmd) (h : Inputs s body anim cmd) :
    X86Routine.run program [0x3325e] 102 ⟨s,flags,0x33169⟩ =
      some (PlayerAnimation.result (motionEnd s body cmd).core) := by
  obtain ⟨k,hk,path,_⟩ := runProgram_path (motion_full_run s flags body cmd h.toMoveEntryInputs)
  have path := X86Routine.lift_control_prefix path program [0x3325e] 0x33169
    motion_decoded motion_active (decoded_forward moveMotionBytes (by decide))
  have ha := establishes_animation s body anim cmd h
  have tail : X86Routine.run program [0x3325e] 33 (shiftState 0x33169 (motionEnd s body cmd)) =
      some (PlayerAnimation.result (motionEnd s body cmd).core) := by
    have pc := (motion_end_memory_pc s flags body cmd h.toMoveMotionInputs).1
    have eq : shiftState 0x33169 (motionEnd s body cmd) =
        ⟨(motionEnd s body cmd).core,(motionEnd s body cmd).flags,0x3323e⟩ := by
      simp [shiftState,pc]
    rw [eq,X86Routine.run_sound _ PlayerAnimation.program contains_animation _ _ _
      (by rw [PlayerAnimation.animation_program _ _ ha.toInputs]; simp)]
    exact PlayerAnimation.animation_program _ _ ha.toInputs
  exact path.finish tail 102 (by omega)

/-- The animation suffix preserves any word separated from its actual stack
and object writes. This is independent of which branch it takes. -/
theorem animation_load (s : X86Memory.State) (a : Word)
    (safe : ∀ b, b ∈ PlayerAnimation.fields (PlayerAnimation.object s) ++
      [s.regs 4-(4#32),s.regs 4-(8#32),s.regs 4-(12#32)] → Apart a b) :
    load32 (PlayerAnimation.result s).core.memory a = load32 s.memory a := by
  have keep (m : Memory) (b v : Word)
      (hb : b ∈ PlayerAnimation.fields (PlayerAnimation.object s) ++
        [s.regs 4-(4#32),s.regs 4-(8#32),s.regs 4-(12#32)]) := load_store_apart m b a v (safe b hb)
  by_cases hm : PlayerAnimation.moving s <;> by_cases hs : PlayerAnimation.standing s <;>
    simp [PlayerAnimation.result,PlayerAnimation.selectedEnd,hm,hs,PlayerAnimation.setterEnd,
      PlayerAnimation.entryMemory,PlayerAnimation.savedMemory,PlayerAnimation.callCore,
      X86Routine.pushWord,put,write,BitVec.sub_sub,keep,PlayerAnimation.fields]

theorem final_motion_fields (s : X86Memory.State) (flags : Option Flags)
    (body : Motion) (anim : PlayerAnim.State) (cmd : Ticcmd) (h : Inputs s body anim cmd) :
    (load32 (PlayerAnimation.result (motionEnd s body cmd).core).core.memory (entryAngleAddress s),
     load32 (PlayerAnimation.result (motionEnd s body cmd).core).core.memory (entryObject s+(72#32)),
     load32 (PlayerAnimation.result (motionEnd s body cmd).core).core.memory (entryObject s+(76#32))) =
    ((body.movePlayer cmd).angle.raw.toBitVec,(body.movePlayer cmd).momx.raw.toBitVec,
      (body.movePlayer cmd).momy.raw.toBitVec) := by
  have keep (a : Word) (ha : a ∈ [entryAngleAddress s,entryObject s+(72#32),entryObject s+(76#32)]) :
      load32 (PlayerAnimation.result (motionEnd s body cmd).core).core.memory a =
        load32 (motionEnd s body cmd).core.memory a := by
    apply animation_load
    intro b hb
    rw [end_object s body anim cmd h,(motion_end_pointers s body cmd).2.2] at hb
    exact h.motionSafe a ha b hb
  rw [keep _ (by simp),keep _ (by simp),keep _ (by simp)]
  have before := move_motion_player_observation s flags body cmd h.toMoveMotionInputs
  rw [motion_full_run s flags body cmd h.toMoveEntryInputs] at before
  have fields := congrArg Prod.snd (Option.some.inj before)
  exact fields

/-- Final observable angle, momenta, animation state/timer and stack pointer,
from a single pre-turn relation and the uninterrupted original instructions. -/
theorem joined_observation (s : X86Memory.State) (flags : Option Flags)
    (body : Motion) (anim : PlayerAnim.State) (cmd : Ticcmd) (h : Inputs s body anim cmd) :
    (X86Routine.run program [0x3325e] 102 ⟨s,flags,0x33169⟩).map (fun t =>
      (t.pc,(load32 t.core.memory (entryAngleAddress s),load32 t.core.memory (entryObject s+(72#32)),
        load32 t.core.memory (entryObject s+(76#32))),
        load32 t.core.memory (entryObject s+(100#32)),load32 t.core.memory (entryObject s+(96#32)),t.core.regs 4)) =
      some (0x3325e,((body.movePlayer cmd).angle.raw.toBitVec,(body.movePlayer cmd).momx.raw.toBitVec,
        (body.movePlayer cmd).momy.raw.toBitVec),PlayerAnimation.statePointer (anim.startWalking cmd).frame,
        (anim.startWalking cmd).tics.toBitVec,s.regs 4) := by
  rw [joined_execution s flags body anim cmd h]
  simp only [Option.map_some,final_motion_fields s flags body anim cmd h]
  have ha := establishes_animation s body anim cmd h
  have fields := PlayerAnimation.result_fields _ anim cmd ha
  rw [end_object s body anim cmd h,(motion_end_pointers s body cmd).2.2] at fields
  have pc : (PlayerAnimation.result (motionEnd s body cmd).core).pc = 0x3325e := by
    obtain ⟨_,_,_,done⟩ := X86Routine.run_path
      (PlayerAnimation.animation_program (motionEnd s body cmd).core none ha.toInputs)
    simpa only [List.mem_singleton] using done
  rw [pc,fields]

end PlayerJoined
end Doom.Proofs
