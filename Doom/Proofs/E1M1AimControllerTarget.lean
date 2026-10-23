import Doom.Proofs.E1M1AimControllerCall
import Doom.Proofs.E1M1AimWindowTarget
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
namespace Doom.Proofs.E1M1AimControllerTarget
open Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1AimReturnedTarget (Image)
attribute [local irreducible] load32 store32

/-- Export the existing collected-record encoding to the production selection.
IDs are not equated with pointers. This intentionally retains the record witness;
it does not strengthen the older image with an unproved actor-kind predicate. -/
structure Observed (initial : Array Intercept) (resolve : Intercept → Word)
    (out : X86Control.State) (selected : AutoAim.Selection) : Prop where
  absent : selected.window=none → load32 out.core.memory 0x2b9f8=0
  selected : ∀ window, selected.window=some window → ∃ j<initial.size,
    initial[j]!.id=window.target ∧ load32 out.core.memory 0x2b9f8=resolve initial[j]! ∧
    load32 out.core.memory 0x2b9b4=selected.slope.raw.toBitVec

/-- Preserving the two target globals preserves the complete existing image. -/
theorem frame (initial : Array Intercept) (resolve : Intercept → Word)
    (out next : X86Control.State) (answer : AimResult) (image : Image initial resolve out answer)
    (target : load32 next.core.memory 0x2b9f8=load32 out.core.memory 0x2b9f8)
    (slope : load32 next.core.memory 0x2b9b4=load32 out.core.memory 0x2b9b4) :
    Image initial resolve next answer := by
  refine ⟨fun absent => target.trans (image.absent absent),?_⟩
  intro id selected
  obtain ⟨j,bound,same,pointer,value⟩ := image.selected id selected
  exact ⟨j,bound,same,target.trans pointer,slope.trans value⟩

theorem accepted (second : Bool) (initial : Array Intercept) (resolve : Intercept → Word)
    (out : X86Control.State) (answer : AimResult) (image : Image initial resolve out answer) :
    Image initial resolve (E1M1BulletAim.accepted second out.core) answer := by
  apply frame initial resolve out _ answer image
  all_goals exact load_store_apart _ _ _ _ (by unfold Apart; decide)

theorem last (initial : Array Intercept) (resolve : Intercept → Word)
    (out : X86Control.State) (answer : AimResult) (image : Image initial resolve out answer) :
    Image initial resolve (E1M1BulletAim.lastReturn out.core out.flags) answer := by
  apply frame initial resolve out _ answer image
  all_goals exact load_store_apart _ _ _ _ (by unfold Apart; decide)

/-- The actual source query supplies target/window identity; no extra target
agreement premise is added to the controller. -/
theorem selection (scene : Scene) (shooter : Nat) (facing probe : Angle) (offset : UInt32)
    (answer : AimResult) (initial : Array Intercept) (resolve : Intercept → Word)
    (out : X86Control.State)
    (query : scene.aimLineAttack shooter probe (Fixed.ofInt 1024)=.ok answer)
    (image : Image initial resolve out answer) :
    Observed initial resolve out (BulletAim.selection facing offset answer) := by
  have same := E1M1AimWindowTarget.aim scene shooter probe (Fixed.ofInt 1024) answer query
  constructor
  · intro absent
    apply image.absent
    change answer.window=none at absent
    rw [same,absent]; rfl
  · intro window present
    change answer.window=some window at present
    have chosen : answer.target=some window.target := by rw [same,present]; rfl
    exact image.selected window.target chosen

theorem miss (initial : Array Intercept) (resolve : Intercept → Word)
    (out : X86Control.State) (answer : AimResult) (facing : Angle)
    (image : Image initial resolve out answer) (absent : answer.target=none) :
    Observed initial resolve out {facing} := by
  exact ⟨fun _ => image.absent absent,fun _ h => by cases h⟩

/-- The final left hit or all-miss result, now including its target image after
store/pops/RET. Null-target paths make no claim about the stale aim-slope global. -/
theorem last_correspondence (scene : Scene) (shooter : Nat) (angle : Angle)
    (a b c : AimResult) (out : X86Control.State)
    (initial : Array Intercept) (resolve : Intercept → Word)
    (p0 : BulletAim.query scene shooter angle 0=.ok a)
    (p1 : BulletAim.query scene shooter angle 0x04000000=.ok b)
    (p2 : BulletAim.query scene shooter angle 0xfc000000=.ok c)
    (no0 : a.target.isSome=false) (no1 : b.target.isSome=false)
    (related : E1M1BulletAim.ProbeResult out.core c) (image : Image initial resolve out c) :
    ∃ selected, scene.bulletAim shooter angle=.ok selected ∧
      load32 (E1M1BulletAim.lastReturn out.core out.flags).core.memory 0x2c0c0=selected.slope.raw.toBitVec ∧
      Observed initial resolve (E1M1BulletAim.lastReturn out.core out.flags) selected := by
  have finalImage := last initial resolve out c image
  cases target : c.target with
  | some id =>
    refine ⟨BulletAim.selection angle 0xfc000000 c,
      BulletAim.live_left scene shooter angle a b c p0 p1 p2 no0 no1 (by rw [target]; rfl),?_,?_⟩
    · exact (E1M1BulletAim.last_slope out.core out.flags).trans related.slope
    · exact selection scene shooter angle ⟨angle.raw+0xfc000000⟩ 0xfc000000 c initial resolve _ p2 finalImage
  | none =>
    have zero := E1M1AimMissZero.aim scene shooter ⟨angle.raw+0xfc000000⟩ (Fixed.ofInt 1024) c p2 target
    refine ⟨{facing:=angle},BulletAim.live_miss scene shooter angle a b c p0 p1 p2 no0 no1 (by rw [target]; rfl),?_,
      miss initial resolve _ c angle finalImage target⟩
    rw [E1M1BulletAim.last_slope,related.slope,zero]
end Doom.Proofs.E1M1AimControllerTarget
