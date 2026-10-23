import Doom.Proofs.OriginalPlayerFunction

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 6400000
namespace Doom.Proofs
open Verification X86 X86Memory X86Control BlockSummary
namespace PlayerCaller

/-- P_PlayerThink's MOV EAX,EDX; CALL P_MovePlayer; MOV EAX,EDX.
The following call to P_CalcHeight is outside this region. -/
def callerBytes : List UInt8 := [0x89,0xd0,0xe8,0x97,0xfd,0xff,0xff,0x89,0xd0]
def bytesProgram (caller function callee : List UInt8) : X86Routine.Program := fun pc =>
  if 0x333c2 ≤ pc ∧ pc < 0x333c2+caller.length then X86Routine.decodeAt caller (pc-0x333c2)
  else PlayerFunction.bytesProgram function callee pc

def program := bytesProgram callerBytes PlayerFunction.functionBytes Doom19.setMobjStateBytes

/-- The player pointer is held in EDX by the caller. -/
def argument (s : X86Memory.State) : X86Memory.State := put s 0 (s.regs 2)
def beforePush (s : X86Memory.State) : X86Memory.State := put (argument s) 4 (s.regs 4-(4#32))
def layout (s : X86Memory.State) : X86Memory.State := PlayerFunction.frameView (beforePush s)
def callEntry (s : X86Memory.State) : X86Memory.State := X86Routine.pushWord (argument s) 0x333c9

theorem entry_frame (s : X86Memory.State) : PlayerFunction.frameView (callEntry s) =
    {layout s with memory := store32 s.memory (s.regs 4-(4#32)) 0x333c9} := by
  simp [PlayerFunction.frameView,callEntry,layout,beforePush,argument,X86Routine.pushWord,put,write]

theorem entry_return (s : X86Memory.State) : load32 (callEntry s).memory ((callEntry s).regs 4) = 0x333c9 := by
  simp [callEntry,argument,X86Routine.pushWord,put,write,load_store]

/-- Caller-state data and layout, before MOV or CALL. No callee-entry relation
or saved return address is assumed. The call's write has its own footprint. -/
structure Inputs (s : X86Memory.State) (body : Motion) (anim : PlayerAnim.State) (cmd : Ticcmd) : Prop
    extends PlayerJoined.Inputs (layout s) body anim cmd where
  callSafe : ∀ a, PlayerFunction.Reads (layout s) a → Apart a (s.regs 4-(4#32))
  pushesSafe : ∀ a, PlayerFunction.Reads (layout s) a →
    ∀ b, b ∈ PlayerFunction.pushSlots (beforePush s) → Apart a b
  savedSafe : ∀ a, a ∈ PlayerFunction.savedSlots (beforePush s) → ∀ b,
    b ∈ PlayerJoined.motionWrites (layout s) ++ PlayerJoined.animationWrites (layout s) → Apart a b

theorem entry_object (s : X86Memory.State) (body : Motion) (anim : PlayerAnim.State) (cmd : Ticcmd)
    (h : Inputs s body anim cmd) : entryObject (PlayerFunction.frameView (callEntry s)) = entryObject (layout s) := by
  rw [entry_frame]
  change load32 (store32 s.memory (s.regs 4-(4#32)) 0x333c9) ((layout s).regs 0) = _
  exact load_store_apart _ _ _ _ (h.callSafe _ (by simp [PlayerFunction.Reads]))

/-- The actual caller instructions establish every P_MovePlayer entry premise,
including the concrete return address and data surviving CALL's stack store. -/
theorem establishes_function (s : X86Memory.State) (body : Motion) (anim : PlayerAnim.State) (cmd : Ticcmd)
    (h : Inputs s body anim cmd) : PlayerFunction.Inputs (callEntry s) body anim cmd := by
  have obj := entry_object s body anim cmd h
  have stack : (PlayerFunction.frameView (callEntry s)).regs = (layout s).regs := by rw [entry_frame]
  constructor
  · rw [entry_frame]
    exact PlayerFunction.transport_inputs (layout s) _ body anim cmd h.toInputs
      (fun a ha => load_store_apart _ _ _ _ (h.callSafe a ha))
  · intro a ha b hb
    have reads : PlayerFunction.Reads (PlayerFunction.frameView (callEntry s)) a = PlayerFunction.Reads (layout s) a := by
      simp only [PlayerFunction.Reads,stack,obj]
    rw [reads] at ha
    exact h.pushesSafe a ha b hb
  · intro a ha b hb
    have writes : PlayerJoined.motionWrites (PlayerFunction.frameView (callEntry s)) ++
        PlayerJoined.animationWrites (PlayerFunction.frameView (callEntry s)) =
        PlayerJoined.motionWrites (layout s) ++ PlayerJoined.animationWrites (layout s) := by
      simp only [PlayerJoined.motionWrites,PlayerJoined.animationWrites,entryAngleAddress,stack,obj]
    rw [writes] at hb
    exact h.savedSafe a ha b hb
  · rw [entry_return]; decide

theorem call_prefix (s : X86Memory.State) (flags : Option Flags) :
    X86Routine.Prefix program [0x333cb] 2 ⟨s,flags,0x333c2⟩ ⟨callEntry s,flags,0x33160⟩ := by
  have mov : program 0x333c2 = some (.control (.block (.legacy (.mov 0 2))),2) := by decide
  have call : program 0x333c4 = some (.call (-617),5) := by decide
  apply X86Routine.Prefix.step (by simp) mov (by rfl)
  apply X86Routine.Prefix.step (by simp) call (by rfl)
  simpa [callEntry,argument,X86Control.execute,X86Control.blockPreservesFlags,X86Block.execute,X86Memory.execute,X86.execute] using
    (X86Routine.Prefix.nil (program := program) (exits := [0x333cb]) ⟨callEntry s,flags,0x33160⟩)

theorem contains_function (pc : Nat) (h : PlayerFunction.program pc ≠ none) :
    program pc = PlayerFunction.program pc := by
  have bound : pc < 0x33268 := by
    unfold PlayerFunction.program PlayerFunction.bytesProgram at h
    split at h
    next hp => change _ ∧ pc < 0x33160+264 at hp; omega
    next hp => split at h
               next hc => change 0x30ea0 ≤ pc ∧ pc < 0x30ea0+91 at hc; omega
               next hc => simp_all
  unfold program bytesProgram
  rw [if_neg (by omega)]
  rfl

theorem function_active (pc : Nat) (h : PlayerFunction.program pc ≠ none) : pc ∉ [0x333cb] := by
  intro hp
  simp only [List.mem_singleton] at hp
  subst pc
  contradiction

/-- P_PlayerThink reloads the preserved EDX player pointer into EAX for the
following height calculation. -/
def resume (t : X86Control.State) : X86Control.State :=
  ⟨put t.core 0 (t.core.regs 2),t.flags,0x333cb⟩
def result (s : X86Memory.State) (body : Motion) (cmd : Ticcmd) :=
  resume (PlayerFunction.result (callEntry s) body cmd)

theorem execution (s : X86Memory.State) (flags : Option Flags) (body : Motion)
    (anim : PlayerAnim.State) (cmd : Ticcmd) (h : Inputs s body anim cmd) :
    X86Routine.run program [0x333cb] 120 ⟨s,flags,0x333c2⟩ = some (result s body cmd) := by
  have hi := establishes_function s body anim cmd h
  have run := PlayerFunction.execution (callEntry s) flags body anim cmd hi
  rw [entry_return] at run
  obtain ⟨k,hk,path,_⟩ := X86Routine.run_path run
  have path := path.transfer program [0x333cb] contains_function function_active
  have ret := PlayerFunction.result_return (callEntry s) body anim cmd hi
  rw [entry_return] at ret
  change (PlayerFunction.result (callEntry s) body cmd).pc = 0x333c9 at ret
  have tail : X86Routine.run program [0x333cb] 1 (PlayerFunction.result (callEntry s) body cmd) =
      some (result s body cmd) := by
    have mov : program 0x333c9 = some (.control (.block (.legacy (.mov 0 2))),2) := by decide
    have state : PlayerFunction.result (callEntry s) body cmd =
        ⟨(PlayerFunction.result (callEntry s) body cmd).core,
         (PlayerFunction.result (callEntry s) body cmd).flags,0x333c9⟩ := by
      rw [← ret]
    rw [state]
    simp [X86Routine.run,mov,X86Routine.execute,X86Control.execute,X86Block.execute,
      X86Memory.execute,X86.execute,result,resume,blockPreservesFlags]
  have middle := path.finish tail 118 (by omega)
  exact (call_prefix s flags).finish middle 120 (by omega)

def object (s : X86Memory.State) : Word := load32 s.memory (s.regs 2)

theorem callee_object (s : X86Memory.State) (body : Motion) (anim : PlayerAnim.State) (cmd : Ticcmd)
    (h : Inputs s body anim cmd) : entryObject (callEntry s) = object s := by
  simpa [entryObject,PlayerFunction.frameView,layout,beforePush,argument,put,write,object]
    using entry_object s body anim cmd h

theorem function_registers (s : X86Memory.State) (body : Motion) (anim : PlayerAnim.State) (cmd : Ticcmd)
    (h : Inputs s body anim cmd) :
    PlayerFunction.preservedRegisters (PlayerFunction.result (callEntry s) body cmd).core =
      PlayerFunction.preservedRegisters s := by
  have eq := PlayerFunction.result_registers (callEntry s) body anim cmd (establishes_function s body anim cmd h)
  simpa [PlayerFunction.preservedRegisters,callEntry,argument,X86Routine.pushWord,put,write,
    BitVec.sub_add_cancel] using eq

theorem result_registers (s : X86Memory.State) (body : Motion) (anim : PlayerAnim.State) (cmd : Ticcmd)
    (h : Inputs s body anim cmd) : PlayerFunction.preservedRegisters (result s body cmd).core =
      PlayerFunction.preservedRegisters s := by
  simpa [PlayerFunction.preservedRegisters,result,resume,put,write] using function_registers s body anim cmd h

theorem result_argument (s : X86Memory.State) (body : Motion) (anim : PlayerAnim.State) (cmd : Ticcmd)
    (h : Inputs s body anim cmd) : (result s body cmd).core.regs 0 = s.regs 2 := by
  have eq := congrArg (fun p => p.2.2.1) (function_registers s body anim cmd h)
  simpa [PlayerFunction.preservedRegisters,result,resume,put,write] using eq

/-- Both nested calls execute from the caller's state, preserving its stack
pointer and saved registers and preparing the original player argument for
P_CalcHeight. Runtime field observations are about the caller's EDX object. -/
theorem observation (s : X86Memory.State) (flags : Option Flags) (body : Motion)
    (anim : PlayerAnim.State) (cmd : Ticcmd) (h : Inputs s body anim cmd) :
    (X86Routine.run program [0x333cb] 120 ⟨s,flags,0x333c2⟩).map (fun t =>
      (t.pc,(load32 t.core.memory (object s+(32#32)),load32 t.core.memory (object s+(72#32)),
        load32 t.core.memory (object s+(76#32))),
        load32 t.core.memory (object s+(100#32)),load32 t.core.memory (object s+(96#32)),
        PlayerFunction.preservedRegisters t.core,t.core.regs 0)) =
      some (0x333cb,((body.movePlayer cmd).angle.raw.toBitVec,(body.movePlayer cmd).momx.raw.toBitVec,
        (body.movePlayer cmd).momy.raw.toBitVec),PlayerAnimation.statePointer (anim.startWalking cmd).frame,
        (anim.startWalking cmd).tics.toBitVec,PlayerFunction.preservedRegisters s,s.regs 2) := by
  rw [execution s flags body anim cmd h]
  simp only [Option.map_some,result_registers s body anim cmd h,result_argument s body anim cmd h]
  have hi := establishes_function s body anim cmd h
  have obs := PlayerFunction.observation (callEntry s) flags body anim cmd hi
  rw [PlayerFunction.execution _ _ _ _ _ hi] at obs
  simp only [Option.map_some,Option.some.injEq,Prod.mk.injEq] at obs
  have obj := callee_object s body anim cmd h
  simp only [entryAngleAddress,obj] at obs
  simp only [result,resume,put,obs.2.1,obs.2.2.1,obs.2.2.2.1]

end PlayerCaller
end Doom.Proofs
