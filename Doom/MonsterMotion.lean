/- Nonplayer, nonmissile, nonfloating P_XYMovement/P_ZMovement branches.
Pinned Chocolate Doom 3.1.1 p_mobj.c; GPL-2.0-or-later. -/
import Doom.WorldPhysics

namespace Doom.MonsterMotion
open Collision

/-- Corpses retain momentum while straddling a ledge, but only above the strict
quarter-unit threshold. Contact floor and subsector floor are distinct inputs. -/
def friction (body : Motion) (corpse : Bool) (sectorFloor : Fixed) : Motion :=
  if body.z.raw > body.floorz.raw then body
  else if corpse && (body.momx.raw > 16384 || body.momx.raw < -16384 ||
      body.momy.raw > 16384 || body.momy.raw < -16384) && body.floorz != sectorFloor then body
  else if body.momx.raw > -4096 && body.momx.raw < 4096 &&
      body.momy.raw > -4096 && body.momy.raw < 4096 then
    { body with momx := ⟨0⟩, momy := ⟨0⟩ }
  else { body with momx := body.momx * ⟨0xe800⟩, momy := body.momy * ⟨0xe800⟩ }

def vertical (body : Motion) : Motion := Id.run do
  let mut body := { body with z := body.z+body.momz }
  if body.z.raw ≤ body.floorz.raw then
    body := { body with z := body.floorz, momz := ⟨max 0 body.momz.raw⟩ }
  else if !body.noGravity then
    body := { body with momz := if body.momz.raw == 0 then ⟨-131072⟩ else body.momz-Fixed.ofInt 1 }
  if (body.z+body.height).raw > body.ceilingz.raw then
    body := { body with z := body.ceilingz-body.height, momz := ⟨min 0 body.momz.raw⟩ }
  return body

/-- Momentum movement precedes the live/dead state countdown. A blocked monster
stops rather than sliding; a pending positive split remainder is still tried.
The host supplies the original P_TryMove effects and current subsector floor. -/
def horizontal (host : α) (body : Motion) (corpse : Bool)
    (sectorFloor : α → Motion → Fixed)
    (move : α → Motion → Fixed → Fixed → Except String (α × Motion × Bool))
    : Except String (α × Motion) := do
  let steps := body.xySteps
  if steps.isEmpty then return (host,body)
  let mut body := { body with momx := clampMomentum body.momx, momy := clampMomentum body.momy }
  let mut host := host
  for (dx,dy) in steps do
    let (next,moved,accepted) ← move host body (body.x+dx) (body.y+dy)
    host := next
    body := if accepted then moved else { moved with momx := ⟨0⟩, momy := ⟨0⟩ }
  return (host,friction body corpse (sectorFloor host body))

/-- Live collision adapter. Map specials execute during P_TryMove, before the
next split attempt; XY movement and friction precede conditional Z movement. -/
def advance (scene : Scene) (id : Nat) (extra : Motion) (corpse : Bool)
    (sectorAt : SectorAt) (cross : Scene → Crossing → Except String Scene)
    : Except String (Scene × Motion) := do
  let some thing := scene.things[id]? | throw "monster motion: missing actor"
  if thing.moveFlags.floating then throw "monster motion: floating actor outside profile"
  let (scene,body) ← horizontal scene (thing.motion extra) corpse
    (fun scene _ => scene.sectors[scene.things[id]!.sector]!.floor)
    (fun scene body x y => do
      let scene := { scene with things := scene.things.set! id (scene.things[id]!.withMotion body) }
      let result ← scene.tryMove id x y sectorAt cross false
      return (result.scene,result.scene.things[id]!.motion body,result.decision.accepted))
  let mut body := body
  let mut scene := { scene with things := scene.things.set! id (scene.things[id]!.withMotion body) }
  if body.z != body.floorz || body.momz.raw != 0 then
    body := vertical body
    scene := { scene with things := scene.things.set! id (scene.things[id]!.withMotion body) }
  return (scene,body)

end Doom.MonsterMotion
