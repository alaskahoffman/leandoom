import Doom.Proofs.E1M1AimCallerRegisters
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimRetryRequest
open Verification X86 X86Memory X86Control BlockSummary Collision
attribute [local irreducible] load32 store32

/-- The exact caller-to-next-query instructions in the already authenticated
map. The target pointer, not the numerical slope, decides whether to retry. -/
theorem execution (second : Bool) (out : X86Control.State) (answer : AimResult)
    (related : E1M1BulletAim.ProbeResult out.core answer) (miss : answer.target=none)
    (resume : out.pc=if second then 0x2d7f8 else 0x2d7d5) :
    X86ReturnCleanup.Prefix FloorCaller.cm E1M1AimProgramLink.program [] (4+(if second then 4 else 5))
      out (E1M1BulletAim.nextQuery second out.core) := by
  have null : OriginalBulletSlope.target out.core=0 := by
    by_cases zero : OriginalBulletSlope.target out.core=0
    · exact zero
    · have present := related.presence.mp zero
      simp only [miss,Option.isSome_none,Bool.false_eq_true] at present
  have a := (E1M1AimTargetDecision.decision second out answer related resume).1
  have b := (X86ReturnCleanup.lift (X86CodeMemory.lift_success
    (OriginalBulletSlope.retry_execution second (OriginalBulletSlope.decision second out.core).core
      (OriginalBulletSlope.decision second out.core).flags) FloorCaller.cm)).transfer
        E1M1AimProgramLink.program E1M1AimTargetDecision.contains
  have atRetry : OriginalBulletSlope.decision second out.core=
      ⟨(OriginalBulletSlope.decision second out.core).core,(OriginalBulletSlope.decision second out.core).flags,
        if second then 0x2d807 else 0x2d7e4⟩ := by
    simp only [OriginalBulletSlope.decision,null,ite_true]
  rw [←atRetry] at b
  exact a.trans b

/-- Request encoding for the next probe, relative to the state before the
previous aim call. For the second retry ECX already contains the right angle. -/
structure Request (second : Bool) (s : X86Memory.State) (next : X86Control.State) : Prop where
  pc : next.pc=0x2bb80
  stack : next.core.regs 4=s.regs 4
  actor : next.core.regs 0=s.regs 6
  range : next.core.regs 3=0x04000000
  angle : next.core.regs 2=s.regs 1+(if second then 0xf8000000 else 0x04000000)
  savedActor : next.core.regs 6=s.regs 6
  savedAngle : next.core.regs 1=if second then s.regs 1 else s.regs 1+0x04000000
  returnWord : load32 next.core.memory (next.core.regs 4)=if second then 0x2d819 else 0x2d7f8

/-- The caller decision stores the slope, and the retry CALL writes its return
word. This exact image is useful for transporting protected data to the next call. -/
theorem memory (second : Bool) (out : X86Memory.State) :
    (E1M1BulletAim.nextQuery second out).core.memory=
      store32 (store32 out.memory 0x2c0c0 (out.regs 0)) (out.regs 4-4)
        (if second then 0x2d819 else 0x2d7f8) := by
  cases second <;> simp [E1M1BulletAim.nextQuery,OriginalBulletSlope.retryState,OriginalBulletSlope.retry,
    OriginalBulletSlope.decision,OriginalBulletSlope.stored,X86Routine.pushWord,put,write]

theorem request (second : Bool) (s : X86Memory.State) (out : X86Control.State)
    (restored : E1M1AimCallerRegisters.Restores s out) :
    Request second s (E1M1BulletAim.nextQuery second out.core) := by
  cases second <;> constructor
  all_goals simp [E1M1BulletAim.nextQuery,OriginalBulletSlope.retryState,OriginalBulletSlope.retry,
    OriginalBulletSlope.decision,OriginalBulletSlope.stored,X86Routine.pushWord,put,write,
    restored.stack,restored.si,restored.cx,
    BitVec.add_sub_cancel,load_store]

/-- Only the two caller writes need separation here. The preceding whole-query
memory frame is a distinct obligation, not implied by register restoration. -/
theorem frame (second : Bool) (out : X86Memory.State) (a : Word)
    (slopeSafe : Apart a 0x2c0c0) (returnSafe : Apart a (out.regs 4-4)) :
    load32 (E1M1BulletAim.nextQuery second out).core.memory a=load32 out.memory a := by
  rw [memory,load_store_apart _ _ _ _ returnSafe,load_store_apart _ _ _ _ slopeSafe]
end Doom.Proofs.E1M1AimRetryRequest
