/-
P_UseLines / PTR_UseTraverse from Chocolate Doom 3.1.1 p_map.c,
commit 410d96855b5df5410ff591a90efeafa889119224.
Derived from id Software (1993-1996), Simon Howard (2005-2014).
SPDX-License-Identifier: GPL-2.0-or-later. See COPYING.md.
-/
import Doom.Path
import Doom.Angles

namespace Doom.Collision

inductive UseAction where
  | nothing
  | blocked
  | special (line : Nat) (back : Bool)
  deriving BEq, Repr

structure UseResult where
  action : UseAction
  path : PathResult

/-- P_LineOpening checks for a back sidedef, independently of ML_TWOSIDED.
An opening only needs positive height for use traversal, not player clearance. -/
private def Line.useOpen (line : Line) : Bool :=
  match line.back with
  | none => false
  | some back =>
    (min line.front.ceiling.raw back.ceiling.raw - max line.front.floor.raw back.floor.raw) > 0

/-- Trace the original 64-unit fine-angle ray through the BLOCKMAP. The first
special stops traversal even if its action will reject the caller or back side.
Return the action request so dispatch can mutate the scene after traversal ends. -/
def Scene.useLines (scene : Scene) (x y : Fixed) (angle : Angle) : Except String UseResult := do
  let endX := x + (⟨64 * angle.fineCosine.raw⟩ : Fixed)
  let endY := y + (⟨64 * angle.fineSine.raw⟩ : Fixed)
  let path ← scene.pathTraverse x y endX endY 1 fun hit _ =>
    let line := scene.lines[hit.id]!
    !line.special && line.useOpen
  let action := match path.visited.back? with
    | none => UseAction.nothing
    | some hit =>
      let line := scene.lines[hit.id]!
      if line.special then .special hit.id (line.pointSide x y)
      else if !line.useOpen then .blocked else .nothing
  return ⟨action,path⟩

end Doom.Collision
