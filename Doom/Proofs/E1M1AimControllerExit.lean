import Doom.Proofs.E1M1AimRetryPair
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimControllerExit
open Verification X86 X86Memory X86Control BlockSummary Collision
attribute [local irreducible] load32 store32

/-- A present target executes the original store, conditional branch, four pops
and RET in the same authenticated program. A zero slope remains a valid hit. -/
theorem accepted (second : Bool) (out : X86Control.State) (answer : AimResult)
    (related : E1M1BulletAim.ProbeResult out.core answer) (hit : answer.target.isSome=true)
    (resume : out.pc=if second then 0x2d7f8 else 0x2d7d5) :
    X86ReturnCleanup.Prefix FloorCaller.cm E1M1AimProgramLink.program [] 9 out
      (E1M1BulletAim.accepted second out.core) ∧
    load32 (E1M1BulletAim.accepted second out.core).core.memory 0x2c0c0=answer.slope.raw.toBitVec ∧
    (∀ a, Apart a 0x2c0c0 → load32 (E1M1BulletAim.accepted second out.core).core.memory a=
      load32 out.core.memory a) := by
  obtain ⟨run,slope,pc⟩ := E1M1AimTargetDecision.decision second out answer related resume
  have finish := (X86ReturnCleanup.lift (X86CodeMemory.lift_success
    (OriginalBulletSlope.finish_execution (OriginalBulletSlope.decision second out.core).core
      (OriginalBulletSlope.decision second out.core).flags) FloorCaller.cm)).transfer
        E1M1AimProgramLink.program E1M1AimTargetDecision.contains
  simp only [hit,ite_true] at pc
  rw [OriginalPathXStep.at_pc _ _ pc] at finish
  refine ⟨run.trans finish,(E1M1BulletAim.accepted_slope second out.core).trans related.slope,?_⟩
  intro a safe
  exact load_store_apart out.core.memory 0x2c0c0 a (out.core.regs 0) safe

/-- The final probe stores its return value and returns without another target
presence test. Source correspondence on an all-miss path additionally needs the
query's zero-on-miss property; this instruction theorem does not assume it. -/
theorem last (out : X86Control.State) (answer : AimResult)
    (related : E1M1BulletAim.ProbeResult out.core answer) (resume : out.pc=0x2d819) :
    ∃ n≤6, X86ReturnCleanup.Prefix FloorCaller.cm E1M1AimProgramLink.program [] n out
      (E1M1BulletAim.lastReturn out.core out.flags) ∧
    load32 (E1M1BulletAim.lastReturn out.core out.flags).core.memory 0x2c0c0=answer.slope.raw.toBitVec := by
  obtain ⟨n,hn,store,_⟩ := X86Routine.run_path (OriginalBulletSlope.last_store_execution out.core out.flags)
  have store := (X86ReturnCleanup.lift (X86CodeMemory.lift_success
    (store.transfer OriginalBulletSlope.program [] (by intros; rfl) (by simp)) FloorCaller.cm)).transfer
      E1M1AimProgramLink.program E1M1AimTargetDecision.contains
  have finish := (X86ReturnCleanup.lift (X86CodeMemory.lift_success
    (OriginalBulletSlope.finish_execution (OriginalBulletSlope.stored out.core) out.flags) FloorCaller.cm)).transfer
      E1M1AimProgramLink.program E1M1AimTargetDecision.contains
  rw [OriginalPathXStep.at_pc _ _ resume] at store
  exact ⟨n+5,by omega,store.trans finish,(E1M1BulletAim.last_slope out.core out.flags).trans related.slope⟩

/-- An executed center query closes the live production autoaim on its hit path. -/
theorem center (scene : Scene) (shooter : Nat) (angle : Angle)
    (out : X86Control.State) (answer : AimResult)
    (query : scene.aimLineAttack shooter angle (Fixed.ofInt 1024)=.ok answer)
    (related : E1M1BulletAim.ProbeResult out.core answer) (hit : answer.target.isSome=true)
    (resume : out.pc=0x2d7d5) :
    scene.bulletAim shooter angle=.ok (BulletAim.selection angle 0 answer) ∧
    X86ReturnCleanup.Prefix FloorCaller.cm E1M1AimProgramLink.program [] 9 out
      (E1M1BulletAim.accepted false out.core) ∧
    load32 (E1M1BulletAim.accepted false out.core).core.memory 0x2c0c0=
      (BulletAim.selection angle 0 answer).slope.raw.toBitVec := by
  have p0 : BulletAim.query scene shooter angle 0=.ok answer := by
    simpa only [BulletAim.query,UInt32.add_zero] using query
  have done := accepted false out answer related hit resume
  exact ⟨BulletAim.live_center scene shooter angle answer p0 hit,done.1,done.2.1⟩

/-- The next rightward hit closes live autoaim using both executed query answers. -/
theorem right (scene : Scene) (shooter : Nat) (angle : Angle) (first answer : AimResult)
    (out : X86Control.State)
    (p0 : scene.aimLineAttack shooter angle (Fixed.ofInt 1024)=.ok first)
    (p1 : scene.aimLineAttack shooter (E1M1AimRetryGeometry.nextAngle false angle) (Fixed.ofInt 1024)=.ok answer)
    (miss : first.target=none) (related : E1M1BulletAim.ProbeResult out.core answer)
    (hit : answer.target.isSome=true) (resume : out.pc=0x2d7f8) :
    scene.bulletAim shooter angle=.ok (BulletAim.selection angle 0x04000000 answer) ∧
    X86ReturnCleanup.Prefix FloorCaller.cm E1M1AimProgramLink.program [] 9 out
      (E1M1BulletAim.accepted true out.core) ∧
    load32 (E1M1BulletAim.accepted true out.core).core.memory 0x2c0c0=
      (BulletAim.selection angle 0x04000000 answer).slope.raw.toBitVec := by
  have centerQuery : BulletAim.query scene shooter angle 0=.ok first := by
    simpa only [BulletAim.query,UInt32.add_zero] using p0
  have done := accepted true out answer related hit resume
  exact ⟨BulletAim.live_right scene shooter angle first answer centerQuery p1
    (by rw [miss]; rfl) hit,done.1,done.2.1⟩
end Doom.Proofs.E1M1AimControllerExit
