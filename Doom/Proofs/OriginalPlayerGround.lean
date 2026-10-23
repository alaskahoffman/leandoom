import Doom.Proofs.OriginalPlayerReaction

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace Doom.Proofs.PlayerGround
open Verification X86 X86Memory X86Control BlockSummary

/-- Extra separation needed to observe the global cached-ground word after
thrust scratch writes and walking-state changes. All addresses are entry data. -/
def Safe (s : X86Memory.State) : Prop :=
  ∀ b, b ∈ PlayerJoined.animationWrites (PlayerCaller.layout s) ++
    [(PlayerCaller.layout s).regs 4,PlayerCaller.object s+(72#32),PlayerCaller.object s+(76#32)] →
    Apart 0x2cf90 b

theorem motion_ground (s : X86Memory.State) (body : Motion) (cmd : Ticcmd)
    (h : MoveMotionInputs s body cmd)
    (safe : ∀ b, b ∈ [s.regs 4,entryObject s+(72#32),entryObject s+(76#32)] → Apart 0x2cf90 b) :
    load32 (moveMotionResultMemory s body cmd) 0x2cf90 = if body.onGround then 1 else 0 := by
  have ground := (after_forward_guard s body cmd h.toMoveJoinInputs).1
  unfold moveMotionResultMemory
  split
  · dsimp only [inlineThrustResult,inlineScratch]
    rw [side_entry_object s body cmd h,(side_entry_pointers s body cmd).2]
    change load32 (store32 (store32 (store32 (sideEntry s body cmd).memory (s.regs 4) _)
      (entryObject s+(72#32)) _) (entryObject s+(76#32)) _) 0x2cf90 = _
    rw [load_store_apart _ _ _ _ (safe _ (by simp)),
      load_store_apart _ _ _ _ (safe _ (by simp)),load_store_apart _ _ _ _ (safe _ (by simp))]
    exact ground
  · rw [after_forward_memory s body cmd h.toMoveJoinInputs] at ground
    exact ground

theorem caller_ground (s : X86Memory.State) (body : Motion) (anim : PlayerAnim.State) (cmd : Ticcmd)
    (h : PlayerCaller.Inputs s body anim cmd) (safe : Safe s) :
    load32 (PlayerCaller.result s body cmd).core.memory 0x2cf90 = if body.onGround then 1 else 0 := by
  have hi := PlayerCaller.establishes_function s body anim cmd h
  have hb := PlayerFunction.establishes_body _ body anim cmd hi
  have obj := PlayerFunction.enter_object _ body anim cmd hi
  rw [PlayerCaller.entry_object s body anim cmd h] at obj
  have layoutObj : entryObject (PlayerCaller.layout s) = PlayerCaller.object s := rfl
  rw [layoutObj] at obj
  have stack : (PlayerFunction.enter (PlayerCaller.callEntry s)).regs 4 =
      (PlayerCaller.layout s).regs 4 := rfl
  change load32 (PlayerAnimation.result (motionEnd (PlayerFunction.enter (PlayerCaller.callEntry s)) body cmd).core).core.memory 0x2cf90 = _
  rw [PlayerJoined.animation_load _ _ (by
    intro b hh
    rw [PlayerJoined.end_object _ body anim cmd hb,(motion_end_pointers _ body cmd).2.2] at hh
    change b ∈ PlayerJoined.animationWrites (PlayerFunction.enter (PlayerCaller.callEntry s)) at hh
    simp only [PlayerJoined.animationWrites,obj,stack] at hh
    apply safe b
    apply List.mem_append_left
    simpa only [PlayerJoined.animationWrites,layoutObj] using hh)]
  rw [(motion_end_memory_pc _ none body cmd hb.toMoveMotionInputs).2]
  apply motion_ground _ body cmd hb.toMoveMotionInputs
  intro b hh
  rw [obj,stack] at hh
  exact safe b (List.mem_append_right _ hh)

/-- Runtime preparePlayerPhysics refreshes grounding only on the movement
branch. A nonzero reaction timer retains the previous cached flag. -/
def ground (body : Motion) (timer : Int32) (cached : Bool) : Bool :=
  if timer = 0 then decide body.onGround else cached

theorem reaction_ground (s : X86Memory.State) (body : Motion) (anim : PlayerAnim.State)
    (cmd : Ticcmd) (timer : Int32) (cached : Bool)
    (h : PlayerReactionProof.Inputs s body anim cmd timer)
    (safe : Safe s) (timerSafe : Apart 0x2cf90 (PlayerReactionProof.timerAddress s))
    (initial : (load32 s.memory 0x2cf90 != (0#32)) = cached) :
    (load32 (PlayerReactionProof.result s body cmd).core.memory 0x2cf90 != (0#32)) =
      ground body timer cached := by
  by_cases hz : PlayerReactionProof.timerWord s = (0#32)
  · have ht := (PlayerReactionProof.zero_iff s body anim cmd timer h).mp hz
    rw [PlayerReactionProof.result,if_pos hz]
    have hi := PlayerReactionProof.establishes_caller s body anim cmd timer h
    have safe' : Safe (PlayerReactionProof.guardCore s) := by
      simpa [Safe,PlayerReactionProof.guardCore,PlayerCaller.layout,PlayerCaller.beforePush,
        PlayerCaller.argument,PlayerCaller.object,PlayerFunction.frameView,PlayerJoined.animationWrites,
        entryObject,put,write] using safe
    rw [caller_ground _ body anim cmd hi safe']
    simp only [ground,ht,↓reduceIte]
    by_cases hg : body.onGround <;> simp [hg]
  · have ht : timer ≠ 0 := by
      intro ht; exact hz ((PlayerReactionProof.zero_iff s body anim cmd timer h).mpr ht)
    rw [PlayerReactionProof.result,if_neg hz]
    change (load32 (store32 s.memory (PlayerReactionProof.timerAddress s) _) 0x2cf90 != (0#32)) = _
    rw [load_store_apart _ _ _ _ timerSafe,initial]
    simp [ground,ht]

end Doom.Proofs.PlayerGround
