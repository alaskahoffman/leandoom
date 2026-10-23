import Doom.Combat
open Doom Doom.Collision

def fixture (timer : Int32) (seed : UInt8) : Simulation := Id.run do
  let sector : Sector := ⟨0,128,"FLOOR","CEIL",160,7,0⟩
  let map : Map := ⟨"test",#[],#[],#[{ (default : Linedef) with front := 0, back := 65535 }],
    #[{ (default : Sidedef) with sector := 0 }],#[sector],
    #[default],#[⟨1,0⟩],#[],ByteArray.empty,default⟩
  let actor : SolidThing := { (default : SolidThing) with
    shootable := true, health := 100, floor := Fixed.ofInt 0, ceiling := Fixed.ofInt 128 }
  let scene : Scene := { grid := default, lines := #[default], links := #[],things := #[actor], sectors := #[⟨Fixed.ofInt 0,Fixed.ofInt 128⟩] }
  let player : Player := { (default : Player) with reactionTime := timer,scene := some scene }
  return { map,original := map,player,ticks := 1,rng := {play := seed} }

-- Exercise the real floor callback and private hurtPlayer wrapper, including
-- the single no-pain RNG entry. This catches a helper that is proved but unused.
#eval Id.run do
  let mut sawPain := false
  let mut sawNoPain := false
  for n in [:256] do
    for timer in ([0,1,18,-1] : List Int32) do
      let s := fixture timer (UInt8.ofNat n)
      let t := s.hurtFromFloor
      if t.physicsError.isSome || t.inventory.health != 95 || t.player.reactionTime != 0 then return false
      if t.rng.play != s.rng.play+1 then return false
      if t.player.animation.frame == 156 then sawPain := true else sawNoPain := true
      let guarded := ({s with inventory := {s.inventory with invulnerability := 1}} : Simulation).hurtFromFloor
      if guarded.physicsError.isSome || guarded.inventory.health != 100 || guarded.player.reactionTime != timer then return false
      if guarded.rng != s.rng then return false
      let noDamage := ({s with ticks := 2} : Simulation).hurtFromFloor
      if noDamage.physicsError.isSome || noDamage.inventory.health != 100 || noDamage.player.reactionTime != timer then return false
  return sawPain && sawNoPain
