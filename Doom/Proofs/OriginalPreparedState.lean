import Doom.Proofs.OriginalPlayerPreparation

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace Doom.Proofs.PreparedState
open Verification X86 X86Memory X86Control BlockSummary PlayerHeight

/-- Gameplay words already established before the height call. -/
def retainedReads (s : X86Memory.State) : List Word :=
  [PlayerCaller.object s+(32#32),PlayerCaller.object s+(72#32),PlayerCaller.object s+(76#32),
   PlayerCaller.object s+(100#32),PlayerCaller.object s+(96#32),PlayerReactionProof.timerAddress s,0x2cf90]

theorem layout_object (s : X86Memory.State) : entryObject (PlayerCaller.layout s) = PlayerCaller.object s := rfl

theorem retained_written (s : X86Memory.State) (a : Word) (ha : a ∈ retainedReads s) :
    a ∈ PlayerHeightJoin.writes s := by
  simp only [retainedReads,List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp [PlayerHeightJoin.writes,PlayerJoined.motionWrites,PlayerJoined.animationWrites,
      PlayerAnimation.fields,entryAngleAddress,layout_object]

theorem retained_reader (s : X86Memory.State) (a : Word) (ha : a ∈ retainedReads s) :
    PlayerFunction.Reads (PlayerCaller.layout s) a ∨ a = PlayerReactionProof.timerAddress s ∨ a = 0x2cf90 := by
  simp only [retainedReads,List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp [PlayerFunction.Reads,layout_object]

/-- The existing initial contracts already protect every prepared gameplay
word from the height call's view writes and seven stack stores. No new
nonaliasing premise or intermediate-state assumption is introduced. -/
theorem retained_safe (s : X86Memory.State) (body : Motion) (anim : PlayerAnim.State) (cmd : Ticcmd)
    (timer : Int32) (v : ViewState) (time : Int32) (cached live : Bool)
    (h : PlayerHeightJoin.Inputs s body anim cmd timer v time cached live)
    (a : Word) (ha : a ∈ retainedReads s) (b : Word) (hb : b ∈ PlayerPreparation.heightWrites s) :
    Apart a b := by
  have inWrites := retained_written s a ha
  simp only [PlayerPreparation.heightWrites,List.mem_append,List.mem_singleton] at hb
  rcases hb with (view | pushes) | call
  · intro i j eq
    exact h.readsSafe b (Or.inr view) a inWrites j i eq.symm
  · rcases retained_reader s a ha with reader | timerField | ground
    · exact h.reaction.pushesSafe a reader b pushes
    · subst a
      apply h.reaction.timerSafe b
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inr pushes))
    · subst a
      exact h.height.pushesSafe _ (Or.inl (by simp [contextReads])) b pushes
  · subst b
    rcases retained_reader s a ha with reader | timerField | ground
    · exact h.reaction.callSafe a reader
    · subst a
      exact h.reaction.timerSafe _ (by simp)
    · subst a
      exact h.height.callSafe _ (Or.inl (by simp [contextReads]))

/-- Encoded preparation fields; this is not the complete Player record or
the later mobj-physics result. Grounding relates a DOS word to a Lean Bool. -/
structure Words where
  angle : Word
  momx : Word
  momy : Word
  animation : Word
  animationTics : Word
  reaction : Word
  height : Word
  delta : Word
  z : Word
  bob : Word
  grounded : Bool
  deriving DecidableEq, Repr

def read (p obj : Word) (m : Memory) : Words :=
  ⟨load32 m (obj+(32#32)),load32 m (obj+(72#32)),load32 m (obj+(76#32)),
   load32 m (obj+(100#32)),load32 m (obj+(96#32)),load32 m (obj+(124#32)),
   load32 m (p+(20#32)),load32 m (p+(24#32)),load32 m (p+(16#32)),load32 m (p+(28#32)),
   load32 m 0x2cf90 != (0#32)⟩

def expected (body : Motion) (anim : PlayerAnim.State) (cmd : Ticcmd) (timer : Int32)
    (v : ViewState) (time : Int32) (cached live : Bool) : Words :=
  let moved := PlayerReaction.move body timer cmd
  let walking := PlayerReaction.animate anim timer cmd
  let grounded := PlayerGround.ground body timer cached
  let view := v.calcHeight moved time grounded live
  ⟨moved.angle.raw.toBitVec,moved.momx.raw.toBitVec,moved.momy.raw.toBitVec,
   PlayerAnimation.statePointer walking.frame,walking.tics.toBitVec,(PlayerReaction.remaining timer).toBitVec,
   view.height.raw.toBitVec,view.delta.raw.toBitVec,view.z.raw.toBitVec,view.bob.raw.toBitVec,grounded⟩

/-- All eleven preparation fields hold after the complete uninterrupted run.
The frame relates final memory to the original entry memory, across both phases. -/
theorem execution (s : X86Memory.State) (flags : Option Flags)
    (body : Motion) (anim : PlayerAnim.State) (cmd : Ticcmd) (timer : Int32)
    (v : ViewState) (time : Int32) (cached live : Bool)
    (h : PlayerHeightJoin.Inputs s body anim cmd timer v time cached live) :
    ∃ t, X86Routine.run PlayerPreparation.program [0x333d0] 225 ⟨s,flags,0x333b1⟩ = some t ∧
      t.pc = 0x333d0 ∧
      read (s.regs 2) (PlayerCaller.object s) t.core.memory = expected body anim cmd timer v time cached live ∧
      t.core.regs 4 = s.regs 4 ∧
      Frame s.memory t.core.memory (PlayerHeightJoin.writes s ++ PlayerPreparation.heightWrites s) := by
  obtain ⟨t,run,pc,view,z,stack,frame⟩ := PlayerPreparation.execution s flags body anim cmd timer v time cached live h
  have keep (a : Word) (ha : a ∈ retainedReads s) := frame a (retained_safe s body anim cmd timer v time cached live h a ha)
  have old := PlayerReactionProof.observation s flags body anim cmd timer h.reaction
  rw [PlayerReactionProof.execution s flags body anim cmd timer h.reaction] at old
  simp only [Option.map_some,Option.some.injEq,Prod.mk.injEq] at old
  obtain ⟨_,⟨angle,mx,my⟩,animation,tics,reaction,_,_⟩ := old
  change load32 (PlayerReactionProof.result s body cmd).core.memory (PlayerCaller.object s+(124#32)) = _ at reaction
  have ground := PlayerGround.reaction_ground s body anim cmd timer cached h.reaction
    h.groundSafe h.groundTimer h.height.context.grounded
  refine ⟨t,run,pc,?_,stack,?_⟩
  · simp only [read,expected,
      keep _ (show PlayerCaller.object s+(32#32) ∈ retainedReads s by simp [retainedReads]),
      keep _ (show PlayerCaller.object s+(72#32) ∈ retainedReads s by simp [retainedReads]),
      keep _ (show PlayerCaller.object s+(76#32) ∈ retainedReads s by simp [retainedReads]),
      keep _ (show PlayerCaller.object s+(100#32) ∈ retainedReads s by simp [retainedReads]),
      keep _ (show PlayerCaller.object s+(96#32) ∈ retainedReads s by simp [retainedReads]),
      keep _ (show PlayerCaller.object s+(124#32) ∈ retainedReads s by simp [retainedReads,PlayerReactionProof.timerAddress]),
      keep _ (show (0x2cf90 : Word) ∈ retainedReads s by simp [retainedReads]),
      angle,mx,my,animation,tics,reaction,ground,view.height,view.delta,view.bob,z]
  · intro a ha
    exact (frame a (fun b hb => ha b (List.mem_append_right _ hb))).trans
      (PlayerHeightJoin.reaction_load s body anim cmd timer h.reaction a
        (fun b hb => ha b (List.mem_append_left _ hb)))

def observe (p obj : Word) (s : X86Control.State) := (s.pc,read p obj s.core.memory,s.core.regs 4)

theorem observation (s : X86Memory.State) (flags : Option Flags)
    (body : Motion) (anim : PlayerAnim.State) (cmd : Ticcmd) (timer : Int32)
    (v : ViewState) (time : Int32) (cached live : Bool)
    (h : PlayerHeightJoin.Inputs s body anim cmd timer v time cached live) :
    (X86Routine.run PlayerPreparation.program [0x333d0] 225 ⟨s,flags,0x333b1⟩).map
      (observe (s.regs 2) (PlayerCaller.object s)) =
      some (0x333d0,expected body anim cmd timer v time cached live,s.regs 4) := by
  obtain ⟨t,run,pc,words,stack,_⟩ := execution s flags body anim cmd timer v time cached live h
  rw [run]
  simp only [Option.map_some,observe,pc,words,stack]

end Doom.Proofs.PreparedState
