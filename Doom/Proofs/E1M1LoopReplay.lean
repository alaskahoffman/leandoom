import Doom.Proofs.E1M1TraversalLoop
set_option backward.isDefEq.respectTransparency false
set_option smartUnfolding false
set_option maxRecDepth 32768
set_option maxHeartbeats 100000
namespace Doom.Proofs.E1M1LoopReplay
attribute [local irreducible] ForIn.forIn E1M1LineSourceLoop.lineCell Collision.thingIntercept Collision.appendIntercept E1M1TraversalLoop.finish
open Collision E1M1TraversalLoop
open E1M1PathAdvance (step ended)
open E1M1GridRoute (sourceRoute)

private theorem map_bind {α β γ : Type} (v : Except String α) (f : α → β)
    (k : β → Except String γ) : (v.map f >>= k)=(v >>= fun x => k (f x)) := by
  cases v <;> rfl

/-- The production object loop's final pure return does not change its result. -/
theorem object_loop (scene : Scene) (trace : Divline) (ids : Array Nat) (r : PathResult) :
    E1M1ThingTraversal.objectCell trace scene.things ids r=objectLoop scene trace ids r := by
  simp only [E1M1ThingTraversal.objectCell,objectLoop,bind_pure]
  rfl

private theorem aiming_inside (scene : Scene) (trace : Divline) (ex ey dx dy : Int32)
    (xs ys yi xi : Fixed) (x y : Int32) (seen : Array Bool) (r : PathResult) (i : Nat)
    (inside : pathCellInside x y scene.grid.width scene.grid.height=true) :
    body scene trace E1M1TraversalSource.aimingScan 3 ex ey dx dy xs ys i (none,r,yi,xi,x,y,seen)=
      (do let (seen,r) ← E1M1LoggedCell.collect trace scene x y seen r
          finish ex ey dx dy xs ys r yi xi x y seen) := by
  simp only [body,E1M1LoggedCell.collect,E1M1CollectionLog.log,
    show ((3 : Nat) &&& 1 != 0) = true from rfl,
    show ((3 : Nat) &&& 2 != 0) = true from rfl,ite_true]
  simp only [if_pos inside]
  cases found : scene.grid.cells[pathCellIndex x y scene.grid.width]? with
  | none => rfl
  | some ids =>
    simp only [E1M1TraversalSource.aimingScan,map_bind,bind_assoc,pure_bind]
    congr 1
    funext out
    rcases out with ⟨seen',r'⟩
    simp only [E1M1FiringThings.sceneCell]
    cases linked : scene.links[pathCellIndex x y scene.grid.width]? with
    | none => rfl
    | some things =>
      simp only [object_loop]

private theorem aiming_outside (scene : Scene) (trace : Divline) (ex ey dx dy : Int32)
    (xs ys yi xi : Fixed) (x y : Int32) (seen : Array Bool) (r : PathResult) (i : Nat)
    (inside : pathCellInside x y scene.grid.width scene.grid.height≠true) :
    body scene trace E1M1TraversalSource.aimingScan 3 ex ey dx dy xs ys i (none,r,yi,xi,x,y,seen)=
      (do let (seen,r) ← E1M1LoggedCell.collect trace scene x y seen r
          finish ex ey dx dy xs ys r yi xi x y seen) := by
  simp only [body,E1M1LoggedCell.collect,E1M1CollectionLog.log,
    show ((3 : Nat) &&& 1 != 0) = true from rfl,
    show ((3 : Nat) &&& 2 != 0) = true from rfl,ite_true]
  simp only [if_neg inside]
  rfl

/-- The actual aiming iteration is logged collection followed by numeric control.
Both branches preserve source errors without success or capacity assumptions. -/
theorem aiming_body (scene : Scene) (trace : Divline) (ex ey dx dy : Int32)
    (xs ys yi xi : Fixed) (x y : Int32) (seen : Array Bool) (r : PathResult) (i : Nat) :
    body scene trace E1M1TraversalSource.aimingScan 3 ex ey dx dy xs ys i (none,r,yi,xi,x,y,seen)=
      (do let (seen,r) ← E1M1LoggedCell.collect trace scene x y seen r
          finish ex ey dx dy xs ys r yi xi x y seen) := by
  by_cases inside : pathCellInside x y scene.grid.width scene.grid.height=true
  · exact aiming_inside scene trace ex ey dx dy xs ys yi xi x y seen r i inside
  · exact aiming_outside scene trace ex ey dx dy xs ys yi xi x y seen r i inside

set_option smartUnfolding true

/-- Decode only the source loop's mutable state; the machine counter is ghost data. -/
def pack (g : E1M1PathAdvance.Cell) (seen : Array Bool) (r : PathResult) : LoopState :=
  (none,r,⟨Int32.ofBitVec g.yi⟩,⟨Int32.ofBitVec g.xi⟩,
    Int32.ofBitVec g.mapX,Int32.ofBitVec g.mapY,seen)

/-- Signed Int32 endpoint and axis operations agree with the checked word step. -/
theorem finish_pack (g : E1M1PathAdvance.Cell) (seen : Array Bool) (r : PathResult) :
    finish (Int32.ofBitVec g.endX) (Int32.ofBitVec g.endY)
      (Int32.ofBitVec g.xDirection) (Int32.ofBitVec g.yDirection)
      ⟨Int32.ofBitVec g.xStride⟩ ⟨Int32.ofBitVec g.yStride⟩ r
      ⟨Int32.ofBitVec g.yi⟩ ⟨Int32.ofBitVec g.xi⟩
      (Int32.ofBitVec g.mapX) (Int32.ofBitVec g.mapY) seen =
      if ended g then .ok (.done (pack g seen r)) else .ok (.yield (pack (step g) seen r)) := by
  have hx : (Int32.ofBitVec g.yi >>> 16=Int32.ofBitVec g.mapY) ↔
      g.yi.sshiftRight 16=g.mapY := by rw [← Int32.toBitVec_inj]; rfl
  have hy : (Int32.ofBitVec g.xi >>> 16=Int32.ofBitVec g.mapX) ↔
      g.xi.sshiftRight 16=g.mapX := by rw [← Int32.toBitVec_inj]; rfl
  by_cases ex : g.mapX=g.endX <;> by_cases ey : g.mapY=g.endY <;>
    by_cases x : g.yi.sshiftRight 16=g.mapY <;> by_cases y : g.xi.sshiftRight 16=g.mapX <;>
    simp_all [finish,pack,step,ended,E1M1PathAdvance.axis,Int32.ofBitVec_inj] <;> rfl

/-- The live body with immutable endpoint/direction/stride parameters decoded. -/
def callback (scene : Scene) (trace : Divline) (g : E1M1PathAdvance.Cell) :=
  body scene trace E1M1TraversalSource.aimingScan 3
    (Int32.ofBitVec g.endX) (Int32.ofBitVec g.endY)
    (Int32.ofBitVec g.xDirection) (Int32.ofBitVec g.yDirection)
    ⟨Int32.ofBitVec g.xStride⟩ ⟨Int32.ofBitVec g.yStride⟩

/-- Grid stepping preserves all immutable loop parameters. -/
theorem callback_step (scene : Scene) (trace : Divline) (g : E1M1PathAdvance.Cell) :
    callback scene trace (step g)=callback scene trace g := by
  unfold step E1M1PathAdvance.axis
  split <;> (try split) <;> (try split) <;> rfl

/-- Collection runs before the endpoint test, including in the last budget slot. -/
theorem body_pack (scene : Scene) (trace : Divline) (g : E1M1PathAdvance.Cell)
    (seen : Array Bool) (r : PathResult) (i : Nat) :
    callback scene trace g i (pack g seen r)=
      (do let (seen,r) ← E1M1LoggedCell.collect trace scene
            (Int32.ofBitVec g.mapX) (Int32.ofBitVec g.mapY) seen r
          if ended g then pure (.done (pack g seen r))
          else pure (.yield (pack (step g) seen r))) := by
  unfold callback pack
  rw [aiming_body]
  apply congrArg (fun k : (Array Bool × PathResult) → Except String (ForInStep LoopState) =>
    E1M1LoggedCell.collect trace scene (Int32.ofBitVec g.mapX) (Int32.ofBitVec g.mapY) seen r >>= k)
  funext out
  exact finish_pack g out.1 out.2

/-- Every finite source iteration sequence equals collection over the generated
route, including errors and the final mutable numeric state. -/
theorem replay (scene : Scene) (trace : Divline) (pick : Int32 → Int32 → E1M1CellWalkInvariant.Cell)
    (fuel start : Nat) (g : E1M1PathAdvance.Cell) (seen : Array Bool) (r : PathResult) :
    forIn (List.range' start fuel) (pack g seen r) (callback scene trace g)=
      (E1M1LoggedWalk.collect trace scene (sourceRoute pick fuel g) seen r).map
        (fun out => pack (E1M1CellWalk.grid g (sourceRoute pick fuel g)) out.1 out.2) := by
  induction fuel generalizing start g seen r with
  | zero => simp only [List.range'_zero,List.forIn_nil,sourceRoute,E1M1LoggedWalk.collect,E1M1CellWalk.grid,Except.map]; rfl
  | succ fuel ih =>
    simp only [List.range'_succ,List.forIn_cons,body_pack]
    cases collected : E1M1LoggedCell.collect trace scene
        (Int32.ofBitVec g.mapX) (Int32.ofBitVec g.mapY) seen r with
    | error e =>
      simp only [sourceRoute,E1M1LoggedWalk.collect,E1M1GridRoute.selected,collected,
        Bind.bind,Except.bind,Except.map]
    | ok out =>
      rcases out with ⟨seen',r'⟩
      cases endpoint : ended g with
      | true =>
        simp only [sourceRoute,ite_true,E1M1LoggedWalk.collect,E1M1GridRoute.selected,
          collected,Bind.bind,Except.bind,Except.map,E1M1CellWalk.grid,step,endpoint]
        rfl
      | false =>
        simp only [sourceRoute,endpoint,Bool.false_eq_true,ite_false,E1M1LoggedWalk.collect,
          E1M1GridRoute.selected,collected,Bind.bind,Except.bind,Except.map,E1M1CellWalk.grid]
        rw [←callback_step scene trace g]
        exact ih (start+1) (step g) seen' r'

/-- The actual range-based source loop is the checked generated-route replay. -/
theorem walk_replay (scene : Scene) (trace : Divline)
    (pick : Int32 → Int32 → E1M1CellWalkInvariant.Cell) (fuel : Nat)
    (g : E1M1PathAdvance.Cell) (seen : Array Bool) (r : PathResult) :
    walk E1M1TraversalSource.aimingScan 3 fuel scene trace
      (Int32.ofBitVec g.endX) (Int32.ofBitVec g.endY)
      (Int32.ofBitVec g.xDirection) (Int32.ofBitVec g.yDirection)
      ⟨Int32.ofBitVec g.xStride⟩ ⟨Int32.ofBitVec g.yStride⟩ (pack g seen r)=
      (E1M1LoggedWalk.collect trace scene (sourceRoute pick fuel g) seen r).map
        (fun out => pack (E1M1CellWalk.grid g (sourceRoute pick fuel g)) out.1 out.2) := by
  unfold walk
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simpa [Std.Legacy.Range.size,callback] using replay scene trace pick fuel 0 g seen r

end Doom.Proofs.E1M1LoopReplay
