import Doom.Proofs.E1M1AimPortalPrefixExit
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1AimBlockingSource
open Collision E1M1AimIteration E1M1AimSource

/-- A one-sided wall stops any iteration, before heights or divisions are read. -/
theorem wall (scene : Scene) (shooter : Nat) (thing : SolidThing) (path : PathResult)
    (distance lower upper : Fixed) (log : Array AutoAim.Portal) (i : Nat) (rest : List Nat)
    (hit : Intercept) (selected : path.visited[i]! = hit) (isLine : hit.isLine=true)
    (solid : scene.lines[hit.id]!.twoSided=false) :
    remaining scene shooter thing path distance (i::rest) lower upper log =
      .ok {path:=stopped path (i+1)} := by
  simp [remaining,List.forIn_cons,visit,selected,isLine,solid]
  rfl

/-- A two-sided opening with no vertical gap stops any iteration before clipping
or division, including equality of floor and ceiling. -/
theorem closed (scene : Scene) (shooter : Nat) (thing : SolidThing) (path : PathResult)
    (distance lower upper : Fixed) (log : Array AutoAim.Portal) (i : Nat) (rest : List Nat)
    (hit : Intercept) (back : Heights) (selected : path.visited[i]! = hit) (isLine : hit.isLine=true)
    (two : scene.lines[hit.id]!.twoSided=true) (backSector : scene.lines[hit.id]!.back=some back)
    (blocked : min scene.lines[hit.id]!.front.ceiling.raw back.ceiling.raw ≤
      max scene.lines[hit.id]!.front.floor.raw back.floor.raw) :
    remaining scene shooter thing path distance (i::rest) lower upper log =
      .ok {path:=stopped path (i+1)} := by
  simp [remaining,List.forIn_cons,visit,selected,isLine,two,backSector,blocked]
  rfl

end Doom.Proofs.E1M1AimBlockingSource
