import Doom.Proofs.E1M1AimLinkedQuery
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimReturnedTarget
open Verification X86 X86Memory X86Control BlockSummary Collision
attribute [local irreducible] load32 store32 E1M1AimCompletedReturn.result

/-- The returned target word represents the source target through a collected
record. No equality between a source ID and a machine pointer is assumed. The
slope global is meaningful only when a target exists, matching DOS behavior. -/
structure Image (initial : Array Intercept) (resolve : Intercept → Word)
    (out : X86Control.State) (answer : AimResult) : Prop where
  absent : answer.target=none → load32 out.core.memory 0x2b9f8=0
  selected : ∀ id, answer.target=some id → ∃ j<initial.size, initial[j]!.id=id ∧
    load32 out.core.memory 0x2b9f8=resolve initial[j]! ∧
    load32 out.core.memory 0x2b9b4=answer.slope.raw.toBitVec

/-- The entire return chain writes only the cursor. In particular, both the
selected pointer and its slope survive the real nested returns. -/
theorem word (s : X86Control.State) (a : Word) (safe : Apart a 0x2c028) :
    load32 (E1M1AimCompletedReturn.result s).core.memory a=load32 s.core.memory a := by
  rw [E1M1AimCompletedReturn.memory]
  exact load_store_apart _ _ _ _ safe

theorem returned (initial : Array Intercept) (resolve : Intercept → Word)
    (s : X86Control.State) (answer : AimResult)
    (exit : E1M1AimHitMemory.Exit initial resolve s answer) :
    Image initial resolve (E1M1AimCompletedReturn.result s) answer := by
  have target := word s 0x2b9f8 (by unfold Apart; decide)
  have slope := word s 0x2b9b4 (by unfold Apart; decide)
  refine ⟨fun absent => target.trans (exit.2 absent).1,?_⟩
  intro id selected
  obtain ⟨j,inside,identity,pointer,value⟩ := exit.1.2 id selected
  exact ⟨j,inside,identity,target.trans pointer,slope.trans value⟩

/-- Derive the existing controller's complete probe interface from execution's
return image. Non-null pointer encoding is still a source representation premise. -/
theorem probe (initial : Array Intercept) (resolve : Intercept → Word)
    (out : X86Control.State) (answer : AimResult)
    (image : Image initial resolve out answer)
    (nonnull : ∀ j<initial.size, resolve initial[j]!≠0)
    (value : out.core.regs 0=answer.slope.raw.toBitVec) :
    E1M1BulletAim.ProbeResult out.core answer := by
  refine ⟨value,?_⟩
  cases target : answer.target with
  | none =>
    have zero : OriginalBulletSlope.target out.core=0 := image.absent target
    simp only [zero,Option.isSome_none,Bool.false_eq_true,ne_eq,not_true_eq_false]
  | some id =>
    obtain ⟨j,inside,identity,pointer,slope⟩ := image.selected id target
    have hit : OriginalBulletSlope.target out.core≠0 := by
      change load32 out.core.memory 0x2b9f8≠0
      rw [pointer]; exact nonnull j inside
    exact ⟨fun _ => rfl,fun _ => hit⟩

/-- A level shot can return EAX=0 while still requiring the controller to stop
searching. Presence is read from the target pointer, never inferred from EAX. -/
theorem zero_slope_hit (out : X86Control.State) (answer : AimResult)
    (related : E1M1BulletAim.ProbeResult out.core answer)
    (hit : answer.target.isSome=true) (zero : answer.slope.raw.toBitVec=0) :
    out.core.regs 0=0 ∧ OriginalBulletSlope.target out.core≠0 := by
  exact ⟨related.slope.trans zero,related.presence.mpr hit⟩
end Doom.Proofs.E1M1AimReturnedTarget
