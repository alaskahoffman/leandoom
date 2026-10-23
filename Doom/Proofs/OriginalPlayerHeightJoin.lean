import Doom.Proofs.OriginalPlayerGround
import Doom.Proofs.OriginalHeightCaller

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
namespace Doom.Proofs.PlayerHeightJoin
open Verification X86 X86Memory X86Control BlockSummary PlayerHeight

def writes (s : X86Memory.State) : List Word :=
  [s.regs 4-(4#32)] ++ PlayerFunction.pushSlots (PlayerCaller.beforePush s) ++
    PlayerJoined.motionWrites (PlayerCaller.layout s) ++ PlayerJoined.animationWrites (PlayerCaller.layout s) ++
    [PlayerReactionProof.timerAddress s]

theorem reaction_load (s : X86Memory.State) (body : Motion) (anim : PlayerAnim.State)
    (cmd : Ticcmd) (timer : Int32) (h : PlayerReactionProof.Inputs s body anim cmd timer)
    (a : Word) (safe : ∀ b, b ∈ writes s → Apart a b) :
    load32 (PlayerReactionProof.result s body cmd).core.memory a = load32 s.memory a := by
  unfold PlayerReactionProof.result
  split
  · apply PlayerReactionProof.caller_load _ body anim cmd
      (PlayerReactionProof.establishes_caller s body anim cmd timer h)
    intro b hb
    apply safe b
    apply List.mem_append_left
    simpa [PlayerReactionProof.guardCore,PlayerCaller.layout,PlayerCaller.beforePush,PlayerCaller.argument,
      PlayerFunction.frameView,entryObject,entryAngleAddress,PlayerJoined.motionWrites,PlayerJoined.animationWrites,
      PlayerFunction.pushSlots,PlayerFunction.savedSlots,put,write] using hb
  · exact load_store_apart _ _ _ _ (safe _ (by simp [writes]))

def stableReads (p obj a : Word) : Prop :=
  a ∈ [p,p+(4#32),p+(196#32),obj+(20#32),obj+(60#32),184192,0x13584] ∨
  ∃ i : Fin 10240, a = 0x5a84 + BitVec.ofNat 32 (i.val*4)

/-- Every premise is about the initial reaction-branch state. No height-entry
memory relation is assumed after movement or the reaction decrement. -/
structure Inputs (s : X86Memory.State) (body : Motion) (anim : PlayerAnim.State) (cmd : Ticcmd)
    (timer : Int32) (v : ViewState) (time : Int32) (cached live : Bool) : Prop where
  reaction : PlayerReactionProof.Inputs s body anim cmd timer
  height : Caller.Inputs (PlayerCaller.argument s) body v time cached live
  readsSafe : ∀ a, stableReads (s.regs 2) (PlayerCaller.object s) a ∨ a ∈ viewWrites (s.regs 2) →
    ∀ b, b ∈ writes s → Apart a b
  groundSafe : PlayerGround.Safe s
  groundTimer : Apart 0x2cf90 (PlayerReactionProof.timerAddress s)

theorem unchanged (body : Motion) (timer : Int32) (cmd : Ticcmd) :
    (PlayerReaction.move body timer cmd).z = body.z ∧
    (PlayerReaction.move body timer cmd).ceilingz = body.ceilingz ∧
    (PlayerReaction.move body timer cmd).noMomentum = body.noMomentum := by
  by_cases ht : timer = 0 <;> by_cases hg : body.z.raw ≤ body.floorz.raw <;>
    by_cases hf : cmd.forwardMove = 0 <;> by_cases hs : cmd.sideMove = 0 <;>
    by_cases hr : body.frame = 0 <;>
    simp [PlayerReaction.move,Motion.movePlayer,Motion.turn,Motion.thrust,Motion.onGround,ht,hg,hf,hs,hr]

/-- Movement's actual output memory supplies the height call's updated momenta
and cached ground; all other reads are transported using the memory frame. -/
theorem establishes_height (s : X86Memory.State) (body : Motion) (anim : PlayerAnim.State) (cmd : Ticcmd)
    (timer : Int32) (v : ViewState) (time : Int32) (cached live : Bool)
    (h : Inputs s body anim cmd timer v time cached live) :
    Caller.Inputs (PlayerReactionProof.result s body cmd).core (PlayerReaction.move body timer cmd)
      v time (PlayerGround.ground body timer cached) live := by
  have obs := PlayerReactionProof.observation s none body anim cmd timer h.reaction
  rw [PlayerReactionProof.execution s none body anim cmd timer h.reaction] at obs
  simp only [Option.map_some,Option.some.injEq,Prod.mk.injEq] at obs
  obtain ⟨pc,⟨angle,mx,my⟩,frm,tics,remaining,sp,arg⟩ := obs
  have keep (a : Word) (ha : stableReads (s.regs 2) (PlayerCaller.object s) a ∨ a ∈ viewWrites (s.regs 2)) :=
    reaction_load s body anim cmd timer h.reaction a (h.readsSafe a ha)
  have obj : Function.object (PlayerReactionProof.result s body cmd).core = PlayerCaller.object s := by
    unfold Function.object
    rw [arg,keep _ (Or.inl (by simp [stableReads]))]
    rfl
  have oldObj : Function.object (PlayerCaller.argument s) = PlayerCaller.object s := rfl
  have oldSp : (PlayerCaller.argument s).regs 4 = s.regs 4 := rfl
  have oldArg : (PlayerCaller.argument s).regs 0 = s.regs 2 := rfl
  have fields := unchanged body timer cmd
  have byteKeep : (PlayerReactionProof.result s body cmd).core.memory (s.regs 2+(196#32)) =
      s.memory (s.regs 2+(196#32)) := by
    have eq := congrArg (fun w : Word => w.extractLsb' 0 8)
      (keep (s.regs 2+(196#32)) (Or.inl (by simp [stableReads])))
    simpa only [load_byte] using eq
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rw [arg,obj]
    refine ⟨?_,?_,?_,mx,my,?_,?_,?_,?_,?_⟩
    · exact keep _ (Or.inl (by simp [stableReads]))
    · rw [keep _ (Or.inl (by simp [stableReads])),fields.1]
      exact h.height.context.z
    · rw [keep _ (Or.inl (by simp [stableReads])),fields.2.1]
      exact h.height.context.ceiling
    · rw [keep _ (Or.inl (by simp [stableReads]))]
      exact h.height.context.tic
    · exact PlayerGround.reaction_ground s body anim cmd timer cached h.reaction
        h.groundSafe h.groundTimer h.height.context.grounded
    · rw [byteKeep,fields.2.2]; exact h.height.context.noMomentum
    · rw [keep _ (Or.inl (by simp [stableReads]))]; exact h.height.context.alive
    · constructor
      · rw [keep _ (Or.inl (by simp [stableReads]))]; exact h.height.context.tables.cosinePointer
      · intro i
        rw [keep _ (Or.inl (Or.inr ⟨i,rfl⟩))]; exact h.height.context.tables.entries i
  · rw [arg]
    constructor
    · exact (keep _ (Or.inr (by simp [viewWrites]))).trans h.height.words.height
    · exact (keep _ (Or.inr (by simp [viewWrites]))).trans h.height.words.delta
    · exact (keep _ (Or.inr (by simp [viewWrites]))).trans h.height.words.bob
  · simpa only [arg,obj,oldArg,oldObj] using h.height.aliases
  · simpa only [Caller.reads,arg,obj,sp,oldSp,oldArg,oldObj] using h.height.callSafe
  · simpa only [Caller.reads,Caller.beforePush,Function.pushSlots,Function.savedSlots,
      put,write,arg,obj,sp,oldSp,oldArg,oldObj] using h.height.pushesSafe
  · simpa only [Caller.beforePush,Function.savedSlots,put,write,arg,sp,oldSp,oldArg] using h.height.savedSafe

/-- Compositional observation with the two existing region-local PC conventions
made explicit. The seam is the same original address, 0x333cb; all memory,
registers and flags pass through unchanged. A single shared-origin program
execution theorem is provided by OriginalPlayerPreparation. -/
theorem observation (s : X86Memory.State) (flags : Option Flags)
    (body : Motion) (anim : PlayerAnim.State) (cmd : Ticcmd) (timer : Int32)
    (v : ViewState) (time : Int32) (cached live : Bool)
    (h : Inputs s body anim cmd timer v time cached live) :
    ∃ middle, X86Routine.run PlayerReactionProof.program [0x333cb] 124 ⟨s,flags,0x333b1⟩ = some middle ∧
      middle.pc = 0x33030 + 0x39b ∧
      (X86Routine.run Caller.program [0x3a0] 101 ⟨middle.core,middle.flags,0x39b⟩).map
        (Function.observe (s.regs 2)) =
        some (0x3a0,
          (v.calcHeight (PlayerReaction.move body timer cmd) time (PlayerGround.ground body timer cached) live).height.raw.toBitVec,
          (v.calcHeight (PlayerReaction.move body timer cmd) time (PlayerGround.ground body timer cached) live).delta.raw.toBitVec,
          (v.calcHeight (PlayerReaction.move body timer cmd) time (PlayerGround.ground body timer cached) live).z.raw.toBitVec,
          (v.calcHeight (PlayerReaction.move body timer cmd) time (PlayerGround.ground body timer cached) live).bob.raw.toBitVec,
          Function.preservedRegisters middle.core) := by
  let middle := PlayerReactionProof.result s body cmd
  have obs := PlayerReactionProof.observation s flags body anim cmd timer h.reaction
  rw [PlayerReactionProof.execution s flags body anim cmd timer h.reaction] at obs
  simp only [Option.map_some,Option.some.injEq,Prod.mk.injEq] at obs
  obtain ⟨pc,_,_,_,_,_,arg⟩ := obs
  refine ⟨middle,PlayerReactionProof.execution s flags body anim cmd timer h.reaction,?_,?_⟩
  · change (PlayerReactionProof.result s body cmd).pc = _
    rw [pc]
  · have height := Caller.observation middle.core middle.flags (PlayerReaction.move body timer cmd)
      v time (PlayerGround.ground body timer cached) live
      (establishes_height s body anim cmd timer v time cached live h)
    simpa only [middle,arg] using height

end Doom.Proofs.PlayerHeightJoin
