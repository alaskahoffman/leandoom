import Doom.Proofs.OriginalPlayerCaller
import Doom.PlayerReaction

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 6400000
namespace Doom.Proofs
open Verification X86 X86Memory X86Control BlockSummary
namespace PlayerReactionProof

def guardBytes : List UInt8 := [0x8b,0x02,0x8b,0x70,0x7c,0x85,0xf6,0x74,0x08,0x8d,0x7e,0xff,0x89,0x78,0x7c,0xeb,0x07]
def callerBytes := guardBytes ++ PlayerCaller.callerBytes

def bytesProgram (caller function callee : List UInt8) : X86Routine.Program := fun pc =>
  if 0x333b1 ≤ pc ∧ pc < 0x333b1+caller.length then X86Routine.decodeAt caller (pc-0x333b1)
  else PlayerFunction.bytesProgram function callee pc

def program := bytesProgram callerBytes PlayerFunction.functionBytes Doom19.setMobjStateBytes

def timerAddress (s : X86Memory.State) := PlayerCaller.object s+(124#32)
def timerWord (s : X86Memory.State) := load32 s.memory (timerAddress s)
def guardCore (s : X86Memory.State) := put (put s 0 (PlayerCaller.object s)) 6 (timerWord s)
def guardEnd (s : X86Memory.State) : X86Control.State := ⟨guardCore s,some (logical32 (timerWord s)),0x333b8⟩
def skipped (s : X86Memory.State) : X86Control.State :=
  ⟨{ regs := write (write (guardCore s).regs 7 (timerWord s-(1#32))) 0 (s.regs 2)
     memory := store32 s.memory (timerAddress s) (timerWord s-(1#32)) },
     some (logical32 (timerWord s)),0x333cb⟩

def result (s : X86Memory.State) (body : Motion) (cmd : Ticcmd) :=
  if timerWord s = (0#32) then PlayerCaller.result (guardCore s) body cmd else skipped s

structure Inputs (s : X86Memory.State) (body : Motion) (anim : PlayerAnim.State)
    (cmd : Ticcmd) (timer : Int32) : Prop extends toCaller : PlayerCaller.Inputs s body anim cmd where
  timerValue : timerWord s = timer.toBitVec
  timerSafe : ∀ b, b ∈ [s.regs 4-(4#32)] ++ PlayerFunction.pushSlots (PlayerCaller.beforePush s) ++
      PlayerJoined.motionWrites (PlayerCaller.layout s) ++ PlayerJoined.animationWrites (PlayerCaller.layout s) →
    Apart (timerAddress s) b

theorem guard_prefix (s : X86Memory.State) (flags : Option Flags) :
    X86Routine.Prefix program [0x333cb] 3 ⟨s,flags,0x333b1⟩ (guardEnd s) := by
  have d0 : program 0x333b1 = some (.control (.block (.legacy (.load 0 2 0))),2) := by decide
  have d1 : program 0x333b3 = some (.control (.block (.legacy (.load 6 0 124))),3) := by decide
  have d2 : program 0x333b6 = some (.control (.testWord 6 6),2) := by decide
  apply X86Routine.Prefix.step (by simp) d0 (by rfl)
  apply X86Routine.Prefix.step (by simp) d1 (by rfl)
  apply X86Routine.Prefix.step (by simp) d2 (by rfl)
  simpa [guardEnd,guardCore,timerWord,timerAddress,PlayerCaller.object,X86Control.execute,
    X86Block.execute,X86Memory.execute,put,write,blockPreservesFlags] using
    (X86Routine.Prefix.nil (program := program) (exits := [0x333cb]) (guardEnd s))

theorem contains_caller (pc : Nat) (h : PlayerCaller.program pc ≠ none) :
    program pc = PlayerCaller.program pc := by
  by_cases hp : 0x333c2 ≤ pc ∧ pc < 0x333c2+9
  · unfold program bytesProgram PlayerCaller.program PlayerCaller.bytesProgram
    simp only [show PlayerCaller.callerBytes.length = 9 from rfl]
    rw [if_pos (by change _ ∧ pc < 0x333b1+26; omega),if_pos hp]
    rw [show pc-0x333b1 = guardBytes.length+(pc-0x333c2) by change _ = 17+_; omega]
    exact X86Routine.decodeAt_append guardBytes PlayerCaller.callerBytes _
  · have hf : PlayerFunction.program pc ≠ none := by
      change (if 0x333c2 ≤ pc ∧ pc < 0x333c2+9 then X86Routine.decodeAt PlayerCaller.callerBytes (pc-0x333c2)
        else PlayerFunction.program pc) ≠ none at h
      simpa only [if_neg hp] using h
    have bound : pc < 0x33268 := by
      unfold PlayerFunction.program PlayerFunction.bytesProgram at hf
      split at hf
      next hh => change _ ∧ pc < 0x33160+264 at hh; omega
      next hh => split at hf
                 next hc => change 0x30ea0 ≤ pc ∧ pc < 0x30ea0+91 at hc; omega
                 next hc => simp_all
    unfold program bytesProgram PlayerCaller.program PlayerCaller.bytesProgram
    simp only [show PlayerCaller.callerBytes.length = 9 from rfl]
    rw [if_neg (by omega),if_neg hp]

theorem take_zero (s : X86Memory.State) (hz : timerWord s = (0#32)) :
    X86Routine.Prefix program [0x333cb] 1 (guardEnd s)
      ⟨guardCore s,some (logical32 0),0x333c2⟩ := by
  have d : program 0x333b8 = some (.control (.jumpZero true 8),2) := by decide
  apply X86Routine.Prefix.step (by simp [guardEnd]) d ?_ (X86Routine.Prefix.nil _)
  simp [guardEnd,hz,X86Routine.execute,X86Control.execute,logical32]

theorem skip_nonzero (s : X86Memory.State) (hz : timerWord s ≠ (0#32)) :
    X86Routine.run program [0x333cb] 5 (guardEnd s) = some (skipped s) := by
  change timerWord s ≠ (0#32) at hz
  have d0 : program 0x333b8 = some (.control (.jumpZero true 8),2) := by decide
  have d1 : program 0x333ba = some (.control (.block (.legacy (.lea 7 6 (-1)))),3) := by decide
  have d2 : program 0x333bd = some (.control (.block (.store ⟨some 0,none,0,124⟩ 7)),3) := by decide
  have d3 : program 0x333c0 = some (.jump 7,2) := by decide
  have d4 : program 0x333c9 = some (.control (.block (.legacy (.mov 0 2))),2) := by decide
  simp [X86Routine.run,guardEnd,d0,d1,d2,d3,d4,X86Routine.execute,X86Control.execute,
    logical32,hz,X86Block.execute,X86Memory.execute,X86Block.Address.eval,guardCore,
    skipped,timerAddress,put,write,blockPreservesFlags,BitVec.sub_eq_add_neg]

/-- The guard only changes temporary EAX/ESI; the player in EDX, stack, commands
and game memory remain the same when the movement branch is selected. -/
theorem establishes_caller (s : X86Memory.State) (body : Motion) (anim : PlayerAnim.State)
    (cmd : Ticcmd) (timer : Int32) (h : Inputs s body anim cmd timer) :
    PlayerCaller.Inputs (guardCore s) body anim cmd := by
  refine {
    angle := ?_,
    turn := ?_,
    forward := ?_,
    height := ?_,
    floor := ?_,
    playerApart := ?_,
    heightApart := ?_,
    floorApart := ?_,
    commandsApart := ?_,
    groundApartAngle := ?_,
    tables := ?_,
    momx := ?_,
    momy := ?_,
    side := ?_,
    angleScratch := ?_,
    angleMomx := ?_,
    angleMomy := ?_,
    readsProtected := ?_,
    tableProtected := ?_,
    scratchProtected := ?_,
    tableScratch := ?_,
    tableMomx := ?_,
    momxProtected := ?_,
    momyProtected := ?_,
    playerMomy := ?_,
    pointerMomx := ?_,
    pointerMomy := ?_,
    tableMomy := ?_,
    animationTable := ?_,
    animationFrame := ?_,
    frameBound := ?_,
    animationTics := ?_,
    readsSafe := ?_,
    animationTableSafe := ?_,
    stackSafe := ?_,
    motionSafe := ?_,
    callSafe := ?_,
    pushesSafe := ?_,
    savedSafe := ?_ }
  · simpa [guardCore,PlayerCaller.layout,PlayerCaller.beforePush,PlayerCaller.argument,
      PlayerFunction.frameView,entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,PlayerFunction.Reads,
      PlayerFunction.pushSlots,PlayerFunction.savedSlots,put,write,eax] using h.angle
  · simpa [guardCore,PlayerCaller.layout,PlayerCaller.beforePush,PlayerCaller.argument,
      PlayerFunction.frameView,entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,PlayerFunction.Reads,
      PlayerFunction.pushSlots,PlayerFunction.savedSlots,put,write,eax] using h.turn
  · simpa [guardCore,PlayerCaller.layout,PlayerCaller.beforePush,PlayerCaller.argument,
      PlayerFunction.frameView,entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,PlayerFunction.Reads,
      PlayerFunction.pushSlots,PlayerFunction.savedSlots,put,write,eax] using h.forward
  · simpa [guardCore,PlayerCaller.layout,PlayerCaller.beforePush,PlayerCaller.argument,
      PlayerFunction.frameView,entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,PlayerFunction.Reads,
      PlayerFunction.pushSlots,PlayerFunction.savedSlots,put,write,eax] using h.height
  · simpa [guardCore,PlayerCaller.layout,PlayerCaller.beforePush,PlayerCaller.argument,
      PlayerFunction.frameView,entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,PlayerFunction.Reads,
      PlayerFunction.pushSlots,PlayerFunction.savedSlots,put,write,eax] using h.floor
  · simpa [guardCore,PlayerCaller.layout,PlayerCaller.beforePush,PlayerCaller.argument,
      PlayerFunction.frameView,entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,PlayerFunction.Reads,
      PlayerFunction.pushSlots,PlayerFunction.savedSlots,put,write,eax] using h.playerApart
  · simpa [guardCore,PlayerCaller.layout,PlayerCaller.beforePush,PlayerCaller.argument,
      PlayerFunction.frameView,entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,PlayerFunction.Reads,
      PlayerFunction.pushSlots,PlayerFunction.savedSlots,put,write,eax] using h.heightApart
  · simpa [guardCore,PlayerCaller.layout,PlayerCaller.beforePush,PlayerCaller.argument,
      PlayerFunction.frameView,entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,PlayerFunction.Reads,
      PlayerFunction.pushSlots,PlayerFunction.savedSlots,put,write,eax] using h.floorApart
  · simpa [guardCore,PlayerCaller.layout,PlayerCaller.beforePush,PlayerCaller.argument,
      PlayerFunction.frameView,entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,PlayerFunction.Reads,
      PlayerFunction.pushSlots,PlayerFunction.savedSlots,put,write,eax] using h.commandsApart
  · simpa [guardCore,PlayerCaller.layout,PlayerCaller.beforePush,PlayerCaller.argument,
      PlayerFunction.frameView,entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,PlayerFunction.Reads,
      PlayerFunction.pushSlots,PlayerFunction.savedSlots,put,write,eax] using h.groundApartAngle
  · simpa [guardCore,PlayerCaller.layout,PlayerCaller.beforePush,PlayerCaller.argument,
      PlayerFunction.frameView,entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,PlayerFunction.Reads,
      PlayerFunction.pushSlots,PlayerFunction.savedSlots,put,write,eax] using h.tables
  · simpa [guardCore,PlayerCaller.layout,PlayerCaller.beforePush,PlayerCaller.argument,
      PlayerFunction.frameView,entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,PlayerFunction.Reads,
      PlayerFunction.pushSlots,PlayerFunction.savedSlots,put,write,eax] using h.momx
  · simpa [guardCore,PlayerCaller.layout,PlayerCaller.beforePush,PlayerCaller.argument,
      PlayerFunction.frameView,entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,PlayerFunction.Reads,
      PlayerFunction.pushSlots,PlayerFunction.savedSlots,put,write,eax] using h.momy
  · simpa [guardCore,PlayerCaller.layout,PlayerCaller.beforePush,PlayerCaller.argument,
      PlayerFunction.frameView,entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,PlayerFunction.Reads,
      PlayerFunction.pushSlots,PlayerFunction.savedSlots,put,write,eax] using h.side
  · simpa [guardCore,PlayerCaller.layout,PlayerCaller.beforePush,PlayerCaller.argument,
      PlayerFunction.frameView,entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,PlayerFunction.Reads,
      PlayerFunction.pushSlots,PlayerFunction.savedSlots,put,write,eax] using h.angleScratch
  · simpa [guardCore,PlayerCaller.layout,PlayerCaller.beforePush,PlayerCaller.argument,
      PlayerFunction.frameView,entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,PlayerFunction.Reads,
      PlayerFunction.pushSlots,PlayerFunction.savedSlots,put,write,eax] using h.angleMomx
  · simpa [guardCore,PlayerCaller.layout,PlayerCaller.beforePush,PlayerCaller.argument,
      PlayerFunction.frameView,entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,PlayerFunction.Reads,
      PlayerFunction.pushSlots,PlayerFunction.savedSlots,put,write,eax] using h.angleMomy
  · simpa [guardCore,PlayerCaller.layout,PlayerCaller.beforePush,PlayerCaller.argument,
      PlayerFunction.frameView,entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,PlayerFunction.Reads,
      PlayerFunction.pushSlots,PlayerFunction.savedSlots,put,write,eax] using h.readsProtected
  · simpa [guardCore,PlayerCaller.layout,PlayerCaller.beforePush,PlayerCaller.argument,
      PlayerFunction.frameView,entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,PlayerFunction.Reads,
      PlayerFunction.pushSlots,PlayerFunction.savedSlots,put,write,eax] using h.tableProtected
  · simpa [guardCore,PlayerCaller.layout,PlayerCaller.beforePush,PlayerCaller.argument,
      PlayerFunction.frameView,entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,PlayerFunction.Reads,
      PlayerFunction.pushSlots,PlayerFunction.savedSlots,put,write,eax] using h.scratchProtected
  · simpa [guardCore,PlayerCaller.layout,PlayerCaller.beforePush,PlayerCaller.argument,
      PlayerFunction.frameView,entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,PlayerFunction.Reads,
      PlayerFunction.pushSlots,PlayerFunction.savedSlots,put,write,eax] using h.tableScratch
  · simpa [guardCore,PlayerCaller.layout,PlayerCaller.beforePush,PlayerCaller.argument,
      PlayerFunction.frameView,entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,PlayerFunction.Reads,
      PlayerFunction.pushSlots,PlayerFunction.savedSlots,put,write,eax] using h.tableMomx
  · simpa [guardCore,PlayerCaller.layout,PlayerCaller.beforePush,PlayerCaller.argument,
      PlayerFunction.frameView,entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,PlayerFunction.Reads,
      PlayerFunction.pushSlots,PlayerFunction.savedSlots,put,write,eax] using h.momxProtected
  · simpa [guardCore,PlayerCaller.layout,PlayerCaller.beforePush,PlayerCaller.argument,
      PlayerFunction.frameView,entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,PlayerFunction.Reads,
      PlayerFunction.pushSlots,PlayerFunction.savedSlots,put,write,eax] using h.momyProtected
  · simpa [guardCore,PlayerCaller.layout,PlayerCaller.beforePush,PlayerCaller.argument,
      PlayerFunction.frameView,entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,PlayerFunction.Reads,
      PlayerFunction.pushSlots,PlayerFunction.savedSlots,put,write,eax] using h.playerMomy
  · simpa [guardCore,PlayerCaller.layout,PlayerCaller.beforePush,PlayerCaller.argument,
      PlayerFunction.frameView,entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,PlayerFunction.Reads,
      PlayerFunction.pushSlots,PlayerFunction.savedSlots,put,write,eax] using h.pointerMomx
  · simpa [guardCore,PlayerCaller.layout,PlayerCaller.beforePush,PlayerCaller.argument,
      PlayerFunction.frameView,entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,PlayerFunction.Reads,
      PlayerFunction.pushSlots,PlayerFunction.savedSlots,put,write,eax] using h.pointerMomy
  · simpa [guardCore,PlayerCaller.layout,PlayerCaller.beforePush,PlayerCaller.argument,
      PlayerFunction.frameView,entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,PlayerFunction.Reads,
      PlayerFunction.pushSlots,PlayerFunction.savedSlots,put,write,eax] using h.tableMomy
  · simpa [guardCore,PlayerCaller.layout,PlayerCaller.beforePush,PlayerCaller.argument,
      PlayerFunction.frameView,entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,PlayerFunction.Reads,
      PlayerFunction.pushSlots,PlayerFunction.savedSlots,put,write,eax] using h.animationTable
  · simpa [guardCore,PlayerCaller.layout,PlayerCaller.beforePush,PlayerCaller.argument,
      PlayerFunction.frameView,entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,PlayerFunction.Reads,
      PlayerFunction.pushSlots,PlayerFunction.savedSlots,put,write,eax] using h.animationFrame
  · simpa [guardCore,PlayerCaller.layout,PlayerCaller.beforePush,PlayerCaller.argument,
      PlayerFunction.frameView,entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,PlayerFunction.Reads,
      PlayerFunction.pushSlots,PlayerFunction.savedSlots,put,write,eax] using h.frameBound
  · simpa [guardCore,PlayerCaller.layout,PlayerCaller.beforePush,PlayerCaller.argument,
      PlayerFunction.frameView,entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,PlayerFunction.Reads,
      PlayerFunction.pushSlots,PlayerFunction.savedSlots,put,write,eax] using h.animationTics
  · simpa [guardCore,PlayerCaller.layout,PlayerCaller.beforePush,PlayerCaller.argument,
      PlayerFunction.frameView,entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,PlayerFunction.Reads,
      PlayerFunction.pushSlots,PlayerFunction.savedSlots,put,write,eax] using h.readsSafe
  · simpa [guardCore,PlayerCaller.layout,PlayerCaller.beforePush,PlayerCaller.argument,
      PlayerFunction.frameView,entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,PlayerFunction.Reads,
      PlayerFunction.pushSlots,PlayerFunction.savedSlots,put,write,eax] using h.animationTableSafe
  · simpa [guardCore,PlayerCaller.layout,PlayerCaller.beforePush,PlayerCaller.argument,
      PlayerFunction.frameView,entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,PlayerFunction.Reads,
      PlayerFunction.pushSlots,PlayerFunction.savedSlots,put,write,eax] using h.stackSafe
  · simpa [guardCore,PlayerCaller.layout,PlayerCaller.beforePush,PlayerCaller.argument,
      PlayerFunction.frameView,entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,PlayerFunction.Reads,
      PlayerFunction.pushSlots,PlayerFunction.savedSlots,put,write,eax] using h.motionSafe
  · simpa [guardCore,PlayerCaller.layout,PlayerCaller.beforePush,PlayerCaller.argument,
      PlayerFunction.frameView,entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,PlayerFunction.Reads,
      PlayerFunction.pushSlots,PlayerFunction.savedSlots,put,write,eax] using h.callSafe
  · simpa [guardCore,PlayerCaller.layout,PlayerCaller.beforePush,PlayerCaller.argument,
      PlayerFunction.frameView,entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,PlayerFunction.Reads,
      PlayerFunction.pushSlots,PlayerFunction.savedSlots,put,write,eax] using h.pushesSafe
  · simpa [guardCore,PlayerCaller.layout,PlayerCaller.beforePush,PlayerCaller.argument,
      PlayerFunction.frameView,entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,PlayerFunction.Reads,
      PlayerFunction.pushSlots,PlayerFunction.savedSlots,put,write,eax] using h.savedSafe

theorem execution (s : X86Memory.State) (flags : Option Flags) (body : Motion)
    (anim : PlayerAnim.State) (cmd : Ticcmd) (timer : Int32) (h : Inputs s body anim cmd timer) :
    X86Routine.run program [0x333cb] 124 ⟨s,flags,0x333b1⟩ = some (result s body cmd) := by
  have hi := establishes_caller s body anim cmd timer h
  have tail : X86Routine.run program [0x333cb] 121 (guardEnd s) = some (result s body cmd) := by
    by_cases hz : timerWord s = (0#32)
    · have run := PlayerCaller.execution (guardCore s) (some (logical32 0)) body anim cmd hi
      have actual : X86Routine.run program [0x333cb] 120 ⟨guardCore s,some (logical32 0),0x333c2⟩ =
          some (PlayerCaller.result (guardCore s) body cmd) := by
        rw [X86Routine.run_sound program PlayerCaller.program contains_caller _ _ _ (by rw [run]; simp),run]
      have moved := (take_zero s hz).finish actual 121 (by omega)
      simpa [result,hz] using moved
    · have run := X86Routine.run_mono (skip_nonzero s hz) 116
      simpa [result,hz] using run
  exact (guard_prefix s flags).finish tail 124 (by omega)

/-- A frame rule for the complete caller/function sequence, reusable for fields
(such as reactiontime) that movement does not write. -/
theorem caller_load (s : X86Memory.State) (body : Motion) (anim : PlayerAnim.State) (cmd : Ticcmd)
    (h : PlayerCaller.Inputs s body anim cmd) (a : Word)
    (safe : ∀ b, b ∈ [s.regs 4-(4#32)] ++ PlayerFunction.pushSlots (PlayerCaller.beforePush s) ++
      PlayerJoined.motionWrites (PlayerCaller.layout s) ++ PlayerJoined.animationWrites (PlayerCaller.layout s) → Apart a b) :
    load32 (PlayerCaller.result s body cmd).core.memory a = load32 s.memory a := by
  have hi := PlayerCaller.establishes_function s body anim cmd h
  have hb := PlayerFunction.establishes_body _ body anim cmd hi
  have obj := PlayerFunction.enter_object _ body anim cmd hi
  rw [PlayerCaller.entry_object s body anim cmd h] at obj
  have motion : PlayerJoined.motionWrites (PlayerFunction.enter (PlayerCaller.callEntry s)) =
      PlayerJoined.motionWrites (PlayerCaller.layout s) := by
    simp only [PlayerJoined.motionWrites,entryAngleAddress,obj]
    rfl
  have anims : PlayerJoined.animationWrites (PlayerFunction.enter (PlayerCaller.callEntry s)) =
      PlayerJoined.animationWrites (PlayerCaller.layout s) := by
    simp only [PlayerJoined.animationWrites,obj]
    rfl
  change load32 (PlayerAnimation.result (motionEnd (PlayerFunction.enter (PlayerCaller.callEntry s)) body cmd).core).core.memory a = _
  rw [PlayerJoined.animation_load _ a (by
    intro b hh
    rw [PlayerJoined.end_object _ body anim cmd hb,(motion_end_pointers _ body cmd).2.2] at hh
    change b ∈ PlayerJoined.animationWrites (PlayerFunction.enter (PlayerCaller.callEntry s)) at hh
    rw [anims] at hh
    exact safe b (by simp only [List.mem_append]; exact Or.inr hh))]
  rw [(motion_end_memory_pc _ none body cmd hb.toMoveMotionInputs).2]
  rw [PlayerJoined.motion_load _ body cmd hb.toMoveMotionInputs a (by
    intro b hh; rw [motion] at hh
    exact safe b (by simp only [List.mem_append]; exact Or.inl (Or.inr hh)))]
  change load32 (PlayerFunction.saved (PlayerCaller.callEntry s)) a = _
  rw [PlayerFunction.saved_load _ a (by
    intro b hh
    exact safe b (by simp only [List.mem_append]; exact Or.inl (Or.inl (Or.inr hh))))]
  change load32 (store32 s.memory (s.regs 4-(4#32)) 0x333c9) a = _
  exact load_store_apart _ _ _ _ (safe _ (by simp))

theorem zero_iff (s : X86Memory.State) (body : Motion) (anim : PlayerAnim.State) (cmd : Ticcmd)
    (timer : Int32) (h : Inputs s body anim cmd timer) : timerWord s = (0#32) ↔ timer = 0 := by
  rw [h.timerValue]
  change timer.toBitVec = (0 : Int32).toBitVec ↔ timer = 0
  exact Int32.toBitVec_inj

theorem timer_result (s : X86Memory.State) (body : Motion) (anim : PlayerAnim.State) (cmd : Ticcmd)
    (timer : Int32) (h : Inputs s body anim cmd timer) :
    load32 (result s body cmd).core.memory (timerAddress s) = (PlayerReaction.remaining timer).toBitVec := by
  by_cases hz : timerWord s = (0#32)
  · have ht := (zero_iff s body anim cmd timer h).mp hz
    rw [result,if_pos hz]
    have keep := caller_load (guardCore s) body anim cmd (establishes_caller s body anim cmd timer h) (timerAddress s) (by
      intro b hb
      apply h.timerSafe b
      simpa [guardCore,PlayerCaller.layout,PlayerCaller.beforePush,PlayerCaller.argument,
        PlayerFunction.frameView,entryObject,entryAngleAddress,PlayerJoined.motionWrites,
        PlayerJoined.animationWrites,PlayerFunction.pushSlots,PlayerFunction.savedSlots,put,write,eax] using hb)
    rw [keep]
    change timerWord s = _
    simpa [PlayerReaction.remaining,ht] using hz
  · have ht : timer ≠ 0 := by intro ht; apply hz; exact (zero_iff s body anim cmd timer h).mpr ht
    rw [result,if_neg hz]
    simp [skipped,load_store,PlayerReaction.remaining,ht,h.timerValue,Int32.toBitVec_sub]

theorem field_apart (obj : Word) (offset : Word) (h : offset ∈ [(32#32),72,76,96,100]) :
    Apart (obj+offset) (obj+(124#32)) := by
  have checked : ∀ o : Word, o ∈ [(32#32),72,76,96,100] →
      ∀ i j : Fin 4, o+BitVec.ofNat 32 i.val ≠ (124#32)+BitVec.ofNat 32 j.val := by
    intro o ho
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
    rcases ho with h|h|h|h|h <;> subst o <;> decide
  intro i j eq
  apply checked offset h i j
  apply (BitVec.add_right_inj obj).mp
  simpa only [BitVec.add_assoc] using eq

/-- Runtime movement, walking animation and timer, on both branches. The height
calculation and later position integration remain outside this observation. -/
theorem observation (s : X86Memory.State) (flags : Option Flags) (body : Motion)
    (anim : PlayerAnim.State) (cmd : Ticcmd) (timer : Int32) (h : Inputs s body anim cmd timer) :
    (X86Routine.run program [0x333cb] 124 ⟨s,flags,0x333b1⟩).map (fun t =>
      (t.pc,(load32 t.core.memory (PlayerCaller.object s+(32#32)),
        load32 t.core.memory (PlayerCaller.object s+(72#32)),load32 t.core.memory (PlayerCaller.object s+(76#32))),
        load32 t.core.memory (PlayerCaller.object s+(100#32)),load32 t.core.memory (PlayerCaller.object s+(96#32)),
        load32 t.core.memory (timerAddress s),t.core.regs 4,t.core.regs 0)) =
      some (0x333cb,((PlayerReaction.move body timer cmd).angle.raw.toBitVec,
        (PlayerReaction.move body timer cmd).momx.raw.toBitVec,(PlayerReaction.move body timer cmd).momy.raw.toBitVec),
        PlayerAnimation.statePointer (PlayerReaction.animate anim timer cmd).frame,
        (PlayerReaction.animate anim timer cmd).tics.toBitVec,(PlayerReaction.remaining timer).toBitVec,s.regs 4,s.regs 2) := by
  rw [execution s flags body anim cmd timer h]
  simp only [Option.map_some,timer_result s body anim cmd timer h]
  by_cases hz : timerWord s = (0#32)
  · have ht := (zero_iff s body anim cmd timer h).mp hz
    have hi := establishes_caller s body anim cmd timer h
    have obs := PlayerCaller.observation (guardCore s) flags body anim cmd hi
    rw [PlayerCaller.execution _ _ _ _ _ hi] at obs
    simp only [Option.map_some,Option.some.injEq,Prod.mk.injEq] at obs
    have obj : PlayerCaller.object (guardCore s) = PlayerCaller.object s := by simp [PlayerCaller.object,guardCore,put,write]
    rw [obj] at obs
    have stack := congrArg (fun p => p.2.2.2.2.2.2) (PlayerCaller.result_registers _ body anim cmd hi)
    simp only [PlayerFunction.preservedRegisters] at stack
    simp only [result,if_pos hz]
    simp only [obs.1,obs.2.1,obs.2.2.1,obs.2.2.2.1,obs.2.2.2.2.2,stack]
    simpa [guardCore,PlayerCaller.object,put,write,PlayerReaction.move,PlayerReaction.animate,ht] using
      (show (some (0x333cb,((body.movePlayer cmd).angle.raw.toBitVec,(body.movePlayer cmd).momx.raw.toBitVec,
        (body.movePlayer cmd).momy.raw.toBitVec),PlayerAnimation.statePointer (anim.startWalking cmd).frame,
        (anim.startWalking cmd).tics.toBitVec,(PlayerReaction.remaining timer).toBitVec,s.regs 4,s.regs 2)) = _ from rfl)

  · have ht : timer ≠ 0 := by intro ht; apply hz; exact (zero_iff s body anim cmd timer h).mpr ht
    have keep (o : Word) (ho : o ∈ [(32#32),72,76,96,100]) :=
      load_store_apart s.memory (timerAddress s) (PlayerCaller.object s+o) (timerWord s-(1#32))
        (field_apart (PlayerCaller.object s) o ho)
    have angle : load32 s.memory (PlayerCaller.object s+(32#32)) = body.angle.raw.toBitVec := h.angle
    have mx : load32 s.memory (PlayerCaller.object s+(72#32)) = body.momx.raw.toBitVec := h.momx
    have my : load32 s.memory (PlayerCaller.object s+(76#32)) = body.momy.raw.toBitVec := h.momy
    have frame : load32 s.memory (PlayerCaller.object s+(100#32)) = PlayerAnimation.statePointer anim.frame := h.animationFrame
    have tics : load32 s.memory (PlayerCaller.object s+(96#32)) = anim.tics.toBitVec := h.animationTics
    simp [result,hz,skipped,keep (32#32) (by simp),keep (72#32) (by simp),keep (76#32) (by simp),
      keep (100#32) (by simp),keep (96#32) (by simp),angle,mx,my,frame,tics,guardCore,put,write,
      PlayerReaction.move,PlayerReaction.animate,ht]

end PlayerReactionProof
end Doom.Proofs
