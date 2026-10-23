import Doom.Player
open Doom Doom.Collision

def checkReaction : Except String Bool := do
  let grid : Blockmap := default
  let m : Map := ⟨"test",#[],#[],#[],#[],#[],#[],#[],#[],ByteArray.empty,grid⟩
  let body : Motion := { angle := ⟨1234⟩, momx := ⟨100⟩, momy := ⟨-200⟩ }
  let actor : SolidThing := { (default : SolidThing) with momx := body.momx, momy := body.momy, ceiling := body.ceilingz }
  let scene : Scene := { grid, lines := #[],links := #[],things := #[actor] }
  let p : Player := { (default : Player) with
    body := body
    reactionTime := 2
    scene := some scene
    view := { height := Fixed.ofInt 30, delta := Fixed.ofInt 1 } }
  let cmd : Ticcmd := { forwardMove := 50, sideMove := -40, angleTurn := 1000 }
  let (p1,_) ← p.prepareTick m 0 (some cmd)
  let (p2,_) ← p1.prepareTick m 0 (some cmd)
  let (p3,_) ← p2.prepareTick m 0 (some cmd)
  let (neg,_) ← ({ p with reactionTime := -2147483648 } : Player).prepareTick m 0 (some cmd)
  let airScene := { scene with things := #[{ actor with z := Fixed.ofInt 1 }] }
  let (air,_) ← ({ p with reactionTime := 1, cachedOnGround := true, scene := some airScene } : Player).prepareTick m 0 (some cmd)
  return !p1.cachedOnGround && !p2.cachedOnGround && p3.cachedOnGround && air.cachedOnGround &&
    p1.view.height == Fixed.ofInt 30 && p2.view.height == Fixed.ofInt 30 &&
    p3.view.height == Fixed.ofInt 31 && air.view.height == Fixed.ofInt 31 &&
    p1.reactionTime == 1 && p2.reactionTime == 0 && p3.reactionTime == 0 &&
    p1.body.angle == body.angle && p2.body.angle == body.angle && p1.body.momx == body.momx && p2.body.momy == body.momy &&
    p1.animation.frame == 149 && p2.animation.frame == 149 && p3.animation.frame == 150 &&
    p3.body.angle == (body.movePlayer cmd).angle && p3.body.momx == (body.movePlayer cmd).momx &&
    neg.reactionTime == 2147483647 && neg.body.angle == body.angle && neg.animation.frame == 149
#eval checkReaction
