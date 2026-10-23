import Doom.Proofs.OriginalPlayerHeightJoin
import Doom.Proofs.OriginalHeightShared

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
namespace Doom.Proofs.PlayerPreparation
open Verification X86 X86Memory X86Control BlockSummary PlayerHeight

/-- All five original regions use absolute DOS code-object offsets. Height's actual CALL now
stores 0x333d0, alongside movement's 0x333c9 and its nested animation return. -/
def bytesProgram (reaction movement setter heightCaller height : List UInt8) : X86Routine.Program := fun pc =>
  match Shared.bytesProgram heightCaller height pc with
  | some instruction => some instruction
  | none => PlayerReactionProof.bytesProgram reaction movement setter pc
def program := bytesProgram PlayerReactionProof.callerBytes PlayerFunction.functionBytes
  Doom19.setMobjStateBytes Caller.callBytes code

def heightWrites (s : X86Memory.State) : List Word :=
  viewWrites (s.regs 2) ++ Function.pushSlots (Shared.beforePush (PlayerCaller.argument s)) ++
    [s.regs 4-(4#32)]

theorem reaction_region (pc : Nat) (h : PlayerReactionProof.program pc ≠ none) :
    (0x30ea0 ≤ pc ∧ pc < 0x30ea0+91) ∨ (0x33160 ≤ pc ∧ pc < 0x33268) ∨ (0x333b1 ≤ pc ∧ pc < 0x333cb) := by
  unfold PlayerReactionProof.program PlayerReactionProof.bytesProgram PlayerFunction.bytesProgram at h
  split at h
  next hr => change _ ∧ pc < 0x333b1+26 at hr; omega
  next hr =>
    split at h
    next hm => change _ ∧ pc < 0x33160+264 at hm; omega
    next hm =>
      split at h
      next hs => change 0x30ea0 ≤ pc ∧ pc < 0x30ea0+91 at hs; omega
      next hs => simp_all

theorem contains_reaction (pc : Nat) (h : PlayerReactionProof.program pc ≠ none) :
    program pc = PlayerReactionProof.program pc := by
  have bounds := reaction_region pc h
  have hn : Shared.program pc = none := by
    unfold Shared.program Shared.bytesProgram
    rw [if_neg (by omega),if_neg (by change ¬ (0x33030 ≤ pc ∧ pc < 0x33030+302); omega)]
  change (match Shared.program pc with | some instruction => some instruction | none => PlayerReactionProof.program pc) = _
  rw [hn]

theorem contains_height (pc : Nat) (h : Shared.program pc ≠ none) :
    program pc = Shared.program pc := by
  change (match Shared.program pc with | some instruction => some instruction | none => PlayerReactionProof.program pc) = _
  cases hp : Shared.program pc with
  | none => exact False.elim (h hp)
  | some instruction => rfl

/-- The reaction branch preserves the player pointer in EDX on both paths. -/
theorem reaction_player (s : X86Memory.State) (body : Motion) (anim : PlayerAnim.State)
    (cmd : Ticcmd) (timer : Int32) (h : PlayerReactionProof.Inputs s body anim cmd timer) :
    (PlayerReactionProof.result s body cmd).core.regs 2 = s.regs 2 := by
  unfold PlayerReactionProof.result
  split
  · have caller := PlayerReactionProof.establishes_caller s body anim cmd timer h
    have regs := PlayerFunction.result_registers (PlayerCaller.callEntry (PlayerReactionProof.guardCore s))
      body anim cmd (PlayerCaller.establishes_function _ body anim cmd caller)
    have edx := congrArg (fun p => p.2.2.1) regs
    simpa [PlayerCaller.result,PlayerCaller.resume,PlayerFunction.preservedRegisters,
      PlayerCaller.callEntry,PlayerCaller.argument,PlayerReactionProof.guardCore,
      X86Routine.pushWord,put,write] using edx
  · simp [PlayerReactionProof.skipped,PlayerReactionProof.guardCore,put,write]

/-- The command pointer in EBX also survives both reaction paths. -/
theorem reaction_command (s : X86Memory.State) (body : Motion) (anim : PlayerAnim.State)
    (cmd : Ticcmd) (timer : Int32) (h : PlayerReactionProof.Inputs s body anim cmd timer) :
    (PlayerReactionProof.result s body cmd).core.regs 3 = s.regs 3 := by
  unfold PlayerReactionProof.result
  split
  · have caller := PlayerReactionProof.establishes_caller s body anim cmd timer h
    have regs := PlayerFunction.result_registers (PlayerCaller.callEntry (PlayerReactionProof.guardCore s))
      body anim cmd (PlayerCaller.establishes_function _ body anim cmd caller)
    have edx := congrArg (fun p => p.1) regs
    simpa [PlayerCaller.result,PlayerCaller.resume,PlayerFunction.preservedRegisters,
      PlayerCaller.callEntry,PlayerCaller.argument,PlayerReactionProof.guardCore,
      X86Routine.pushWord,put,write] using edx
  · simp [PlayerReactionProof.skipped,PlayerReactionProof.guardCore,put,write]

/-- A single uninterrupted original-byte run, using only initial-state
contracts. No PC rebasing, memory reset, or assumed intermediate relation. -/
theorem execution_preserved (s : X86Memory.State) (flags : Option Flags)
    (body : Motion) (anim : PlayerAnim.State) (cmd : Ticcmd) (timer : Int32)
    (v : ViewState) (time : Int32) (cached live : Bool)
    (h : PlayerHeightJoin.Inputs s body anim cmd timer v time cached live) :
    ∃ t, X86Routine.run program [0x333d0] 225 ⟨s,flags,0x333b1⟩ = some t ∧
      t.pc = 0x333d0 ∧
      Words (s.regs 2) t.core.memory
        (v.calcHeight (PlayerReaction.move body timer cmd) time (PlayerGround.ground body timer cached) live) ∧
      load32 t.core.memory (s.regs 2+(16#32)) =
        (v.calcHeight (PlayerReaction.move body timer cmd) time (PlayerGround.ground body timer cached) live).z.raw.toBitVec ∧
      t.core.regs 4 = s.regs 4 ∧
      Frame (PlayerReactionProof.result s body cmd).core.memory t.core.memory (heightWrites s) ∧
      t.core.regs 2 = s.regs 2 := by
  let middle := PlayerReactionProof.result s body cmd
  have run := PlayerReactionProof.execution s flags body anim cmd timer h.reaction
  have obs := PlayerReactionProof.observation s flags body anim cmd timer h.reaction
  rw [run] at obs
  simp only [Option.map_some,Option.some.injEq,Prod.mk.injEq] at obs
  obtain ⟨pc,_,_,_,_,sp,arg⟩ := obs
  obtain ⟨n,bound,path,_⟩ := X86Routine.run_path run
  have firstPath := path.transfer program [0x333d0] contains_reaction (by
    intro pc hd; have hr := reaction_region pc hd; simp only [List.mem_singleton]; omega)
  have hi := PlayerHeightJoin.establishes_height s body anim cmd timer v time cached live h
  obtain ⟨t,tail,ret,words,z,regs,frame⟩ := Shared.execution middle.core middle.flags
    (PlayerReaction.move body timer cmd) v time (PlayerGround.ground body timer cached) live hi
  have tail' : X86Routine.run program [0x333d0] 101 middle = some t := by
    have atpc : middle = ⟨middle.core,middle.flags,0x333cb⟩ := by
      dsimp only [middle]; rw [← pc]
    rw [atpc]
    rw [X86Routine.run_sound program Shared.program contains_height _ _ _ (by rw [tail]; simp),tail]
  refine ⟨t,firstPath.finish tail' 225 (by omega),ret,?_,?_,?_,?_,?_⟩
  · simpa only [middle,arg] using words
  · simpa only [middle,arg] using z
  · have stack := congrArg (fun p => p.2.2.2.2.2.2) regs
    exact stack.trans sp
  · simpa [heightWrites,Function.pushSlots,Function.savedSlots,Shared.beforePush,
      PlayerCaller.argument,put,write,middle,arg,sp] using frame
  · exact (congrArg (fun p => p.2.2.1) regs).trans (reaction_player s body anim cmd timer h.reaction)

theorem execution_command (s : X86Memory.State) (flags : Option Flags)
    (body : Motion) (anim : PlayerAnim.State) (cmd : Ticcmd) (timer : Int32)
    (v : ViewState) (time : Int32) (cached live : Bool)
    (h : PlayerHeightJoin.Inputs s body anim cmd timer v time cached live) :
    ∃ t, X86Routine.run program [0x333d0] 225 ⟨s,flags,0x333b1⟩ = some t ∧
      t.core.regs 3 = s.regs 3 := by
  let middle := PlayerReactionProof.result s body cmd
  have run := PlayerReactionProof.execution s flags body anim cmd timer h.reaction
  have obs := PlayerReactionProof.observation s flags body anim cmd timer h.reaction
  rw [run] at obs
  simp only [Option.map_some,Option.some.injEq,Prod.mk.injEq] at obs
  obtain ⟨pc,_,_,_,_,sp,arg⟩ := obs
  obtain ⟨n,bound,path,_⟩ := X86Routine.run_path run
  have firstPath := path.transfer program [0x333d0] contains_reaction (by
    intro pc hd; have hr := reaction_region pc hd; simp only [List.mem_singleton]; omega)
  have hi := PlayerHeightJoin.establishes_height s body anim cmd timer v time cached live h
  obtain ⟨t,tail,ret,words,z,regs,frame⟩ := Shared.execution middle.core middle.flags
    (PlayerReaction.move body timer cmd) v time (PlayerGround.ground body timer cached) live hi
  have tail' : X86Routine.run program [0x333d0] 101 middle = some t := by
    have atpc : middle = ⟨middle.core,middle.flags,0x333cb⟩ := by
      dsimp only [middle]; rw [← pc]
    rw [atpc]
    rw [X86Routine.run_sound program Shared.program contains_height _ _ _ (by rw [tail]; simp),tail]
  exact ⟨t,firstPath.finish tail' 225 (by omega),
    (congrArg (fun p => p.1) regs).trans (reaction_command s body anim cmd timer h.reaction)⟩

/-- Compatibility projection of the strengthened execution result. -/
theorem execution (s : X86Memory.State) (flags : Option Flags)
    (body : Motion) (anim : PlayerAnim.State) (cmd : Ticcmd) (timer : Int32)
    (v : ViewState) (time : Int32) (cached live : Bool)
    (h : PlayerHeightJoin.Inputs s body anim cmd timer v time cached live) :
    ∃ t, X86Routine.run program [0x333d0] 225 ⟨s,flags,0x333b1⟩ = some t ∧
      t.pc = 0x333d0 ∧
      Words (s.regs 2) t.core.memory
        (v.calcHeight (PlayerReaction.move body timer cmd) time (PlayerGround.ground body timer cached) live) ∧
      load32 t.core.memory (s.regs 2+(16#32)) =
        (v.calcHeight (PlayerReaction.move body timer cmd) time (PlayerGround.ground body timer cached) live).z.raw.toBitVec ∧
      t.core.regs 4 = s.regs 4 ∧
      Frame (PlayerReactionProof.result s body cmd).core.memory t.core.memory (heightWrites s) := by
  obtain ⟨t,run,pc,words,z,sp,frame,_⟩ := execution_preserved s flags body anim cmd timer v time cached live h
  exact ⟨t,run,pc,words,z,sp,frame⟩

def observe (p : Word) (t : X86Control.State) :=
  (t.pc,load32 t.core.memory (p+(20#32)),load32 t.core.memory (p+(24#32)),
    load32 t.core.memory (p+(16#32)),load32 t.core.memory (p+(28#32)),t.core.regs 4)

theorem observation (s : X86Memory.State) (flags : Option Flags)
    (body : Motion) (anim : PlayerAnim.State) (cmd : Ticcmd) (timer : Int32)
    (v : ViewState) (time : Int32) (cached live : Bool)
    (h : PlayerHeightJoin.Inputs s body anim cmd timer v time cached live) :
    (X86Routine.run program [0x333d0] 225 ⟨s,flags,0x333b1⟩).map (observe (s.regs 2)) =
      some (0x333d0,
        (v.calcHeight (PlayerReaction.move body timer cmd) time (PlayerGround.ground body timer cached) live).height.raw.toBitVec,
        (v.calcHeight (PlayerReaction.move body timer cmd) time (PlayerGround.ground body timer cached) live).delta.raw.toBitVec,
        (v.calcHeight (PlayerReaction.move body timer cmd) time (PlayerGround.ground body timer cached) live).z.raw.toBitVec,
        (v.calcHeight (PlayerReaction.move body timer cmd) time (PlayerGround.ground body timer cached) live).bob.raw.toBitVec,s.regs 4) := by
  obtain ⟨t,run,pc,words,z,stack,_⟩ := execution s flags body anim cmd timer v time cached live h
  rw [run]
  simp only [Option.map_some,observe,pc,words.height,words.delta,words.bob,z,stack]

end Doom.Proofs.PlayerPreparation
