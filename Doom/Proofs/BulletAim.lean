import Doom.Hitscan
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.BulletAim
open Collision

def query (scene : Scene) (shooter : Nat) (angle : Angle) (offset : UInt32) :=
  scene.aimLineAttack shooter ⟨angle.raw+offset⟩ (Fixed.ofInt 1024)
def selection (angle : Angle) (offset : UInt32) (r : AimResult) : AutoAim.Selection :=
  {slope := r.slope, facing := angle, offset, window := r.window}
def choose (angle : Angle) (a b c : AimResult) : AutoAim.Selection :=
  if a.target.isSome then selection angle 0 a
  else if b.target.isSome then selection angle 0x04000000 b
  else if c.target.isSome then selection angle 0xfc000000 c
  else {facing := angle}

/-- Live production loop, including short circuiting and error propagation.
No replacement implementation is introduced for the proof. -/
theorem live_unfold (scene : Scene) (shooter : Nat) (angle : Angle) :
    scene.bulletAim shooter angle = (do
      let a ← query scene shooter angle 0
      if a.target.isSome then return selection angle 0 a
      let b ← query scene shooter angle 0x04000000
      if b.target.isSome then return selection angle 0x04000000 b
      let c ← query scene shooter angle 0xfc000000
      if c.target.isSome then return selection angle 0xfc000000 c
      return {facing := angle}) := by
  cases h0 : query scene shooter angle 0 with
  | error e => simp [Scene.bulletAim,query,selection,bind,pure,Except.bind,Except.pure] at h0 ⊢ <;> simp [h0]
  | ok a =>
    by_cases ha : a.target.isSome=true
    · simp [Scene.bulletAim,query,selection,bind,pure,Except.bind,Except.pure] at h0 ⊢; simp [h0,ha]
    · cases h1 : query scene shooter angle 0x04000000 with
      | error e => simp [Scene.bulletAim,query,selection,bind,pure,Except.bind,Except.pure] at h0 h1 ⊢; simp [h0,ha,h1]
      | ok b =>
        by_cases hb : b.target.isSome=true
        · simp [Scene.bulletAim,query,selection,bind,pure,Except.bind,Except.pure] at h0 h1 ⊢; simp [h0,ha,h1,hb]
        · cases h2 : query scene shooter angle 0xfc000000 with
          | error e => simp [Scene.bulletAim,query,selection,bind,pure,Except.bind,Except.pure] at h0 h1 h2 ⊢; simp [h0,ha,h1,hb,h2]
          | ok c =>
            by_cases hc : c.target.isSome=true <;>
              simp [Scene.bulletAim,query,selection,bind,pure,Except.bind,Except.pure] at h0 h1 h2 ⊢ <;>
              simp [h0,ha,h1,hb,h2,hc]

/-- The original controller's last probe returns its slope without testing
linetarget again. Equivalence therefore requires zero on a third-probe miss. -/
def controllerSlope (a b c : AimResult) : Fixed :=
  if a.target.isSome then a.slope else if b.target.isSome then b.slope else c.slope

theorem selection_slope (angle : Angle) (a b c : AimResult)
    (lastMiss : c.target.isSome=false → c.slope=⟨0⟩) :
    (choose angle a b c).slope=controllerSlope a b c := by
  by_cases ha : a.target.isSome=true <;> by_cases hb : b.target.isSome=true <;>
    by_cases hc : c.target.isSome=true <;>
    simp_all [choose,selection,controllerSlope]

theorem live_center (scene : Scene) (shooter : Nat) (angle : Angle) (a : AimResult)
    (probe : query scene shooter angle 0=.ok a) (hit : a.target.isSome=true) :
    scene.bulletAim shooter angle=.ok (selection angle 0 a) := by
  rw [live_unfold]; simp [probe,hit,bind,pure,Except.bind,Except.pure]
theorem live_right (scene : Scene) (shooter : Nat) (angle : Angle) (a b : AimResult)
    (p0 : query scene shooter angle 0=.ok a) (p1 : query scene shooter angle 0x04000000=.ok b)
    (no : a.target.isSome=false) (hit : b.target.isSome=true) :
    scene.bulletAim shooter angle=.ok (selection angle 0x04000000 b) := by
  rw [live_unfold]; simp [p0,p1,no,hit,bind,pure,Except.bind,Except.pure]
theorem live_left (scene : Scene) (shooter : Nat) (angle : Angle) (a b c : AimResult)
    (p0 : query scene shooter angle 0=.ok a) (p1 : query scene shooter angle 0x04000000=.ok b)
    (p2 : query scene shooter angle 0xfc000000=.ok c)
    (no0 : a.target.isSome=false) (no1 : b.target.isSome=false) (hit : c.target.isSome=true) :
    scene.bulletAim shooter angle=.ok (selection angle 0xfc000000 c) := by
  rw [live_unfold]; simp [p0,p1,p2,no0,no1,hit,bind,pure,Except.bind,Except.pure]
theorem live_miss (scene : Scene) (shooter : Nat) (angle : Angle) (a b c : AimResult)
    (p0 : query scene shooter angle 0=.ok a) (p1 : query scene shooter angle 0x04000000=.ok b)
    (p2 : query scene shooter angle 0xfc000000=.ok c)
    (no0 : a.target.isSome=false) (no1 : b.target.isSome=false) (no2 : c.target.isSome=false) :
    scene.bulletAim shooter angle=.ok {facing := angle} := by
  rw [live_unfold]; simp [p0,p1,p2,no0,no1,no2,bind,pure,Except.bind,Except.pure]

/-- The controller chooses a vertical slope; the facing stays at the input angle. -/
theorem facing (angle : Angle) (a b c : AimResult) : (choose angle a b c).facing=angle := by
  simp only [choose]; split <;> try rfl
  split <;> try rfl
  split <;> rfl
end Doom.Proofs.BulletAim
