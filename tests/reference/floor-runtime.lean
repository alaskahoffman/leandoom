import Doom.Proofs.OriginalFloorRuntime
open Doom Doom.Collision Doom.Proofs
namespace FloorRuntimeFixture

def fixture (special suit tick : Nat) (z : Fixed) (timer : Int32) (seed : UInt8) : Simulation := Id.run do
  let sector : Sector := ⟨0,128,"FLOOR","CEIL",160,special,0⟩
  let map : Map := ⟨"test",#[],#[],#[{ (default : Linedef) with front := 0, back := 65535 }],
    #[{ (default : Sidedef) with sector := 1 }],#[{ sector with special := 9 },sector],
    #[default],#[⟨1,0⟩],#[],ByteArray.empty,default⟩
  let actor : SolidThing := { (default : SolidThing) with
    x := Fixed.ofInt 12, y := Fixed.ofInt 23, z, floor := Fixed.ofInt 32, ceiling := Fixed.ofInt 128 }
  let scene : Scene := {
    grid := default, lines := #[default], links := #[], things := #[actor],
    sectors := #[⟨Fixed.ofInt 0,Fixed.ofInt 128⟩,⟨Fixed.ofInt 0,Fixed.ofInt 128⟩] }
  -- Wrong incoming player position, collision floor different from sector floor,
  -- and stale player inventory: the real preparation must synchronize these.
  let player : Player := { (default : Player) with
    body := { x := Fixed.ofInt 999, y := Fixed.ofInt 998, z := Fixed.ofInt 997 },
    inventory := { (default : Inventory) with suit := suit+100 },
    reactionTime := timer, scene := some scene, levelTime := Int32.ofNat tick }
  return { map, original := map, player, inventory := { (default : Inventory) with suit := suit },
           secrets := 2147483647, rng := ⟨seed,173⟩, ticks := tick+1 }

def cmd : Ticcmd := { forwardMove := 50, sideMove := -40, angleTurn := 1000 }
def recordDamage (s : Simulation) (amount : Nat) : Simulation :=
  { s with shots := s.shots+1, kills := amount, secrets := Int32.ofNat s.rng.play.toNat }

def checks (special suit tick : Nat) (z : Fixed) (timer : Int32) (seed : UInt8)
    (amount : Nat) (nextIndex : UInt8) : Bool := Id.run do
  let s := fixture special suit tick z timer seed
  match s.prepareSectorTick 0 (some cmd) with
  | .error _ => return false
  | .ok (out,actual) =>
    let some (words,requested,play,misc) := FloorRuntime.output (.ok (out,actual)) | return false
    let effect := out.applyFloorEffect recordDamage
    return requested == amount && play == nextIndex.toBitVec.setWidth 32 && misc == (173#32) &&
      words == PreparedRuntime.words out.player && out.player.body.x == Fixed.ofInt 12 &&
      out.player.body.y == Fixed.ofInt 23 && out.player.body.z == z &&
      out.player.inventory.suit == suit && out.inventory.suit == suit &&
      out.map.sectors[1]!.special == special && out.map.sectors[0]!.special == 9 &&
      out.secrets == 2147483647 && out.ticks == tick+1 && out.rng.play == seed &&
      out.player.reactionTime == PlayerReaction.remaining timer &&
      actual.forwardMove == cmd.forwardMove && actual.sideMove == cmd.sideMove && actual.angleTurn == cmd.angleTurn &&
      effect.rng.play == nextIndex && effect.rng.misc == 173 && effect.inventory.suit == suit &&
      effect.shots == (if amount == 0 then 0 else 1) &&
      effect.secrets == (if amount == 0 then 2147483647 else Int32.ofNat nextIndex.toNat) &&
      (if amount == 0 then
        let real := out.hurtFromFloor
        real.rng.play == nextIndex && real.rng.misc == 173 && real.inventory.health == out.inventory.health &&
          real.inventory.suit == suit && real.physicsError.isNone
       else effect.kills == amount)

def errors : Bool := Id.run do
  let s := fixture 4 1 32 (Fixed.ofInt 0) 2 65
  let missing := { s with player := { s.player with scene := none } }
  let badBsp := { s with map := { s.map with subsectors := #[] } }
  let a := match missing.prepareSectorTick 0 (some cmd) with
    | .ok _ => false
    | .error failed => failed.player.body.x == Fixed.ofInt 999 && failed.player.reactionTime == 2 &&
      failed.rng.play == 65 && (FloorRuntime.output (.error failed)).isNone
  let b := match badBsp.prepareSectorTick 0 (some cmd) with
    | .ok _ => false
    | .error failed => failed.player.body.x == Fixed.ofInt 12 && failed.player.reactionTime == 1 &&
      failed.rng.play == 65 && failed.physicsError == some "BSP: invalid subsector"
  let direct := badBsp.applyFloorEffect recordDamage
  let c := direct.physicsError == some "BSP: invalid subsector" && direct.rng.play == 65 &&
    direct.shots == 0 && direct.player.body.x == Fixed.ofInt 999 && direct.inventory.suit == 1 &&
    (FloorRuntime.output (.ok (badBsp,cmd))).isNone
  return a && b && c

#eval [checks 5 0 0 (Fixed.ofInt 0) 0 65 10 65,
  checks 5 1 32 (Fixed.ofInt 0) 2 65 0 65,
  checks 7 0 32 (Fixed.ofInt 0) 0 0 5 0,
  checks 7 0 31 (Fixed.ofInt 0) 2 0 0 0,
  checks 4 1 32 (Fixed.ofInt 0) 0 65 20 66,
  checks 4 1 1 (Fixed.ofInt 0) 2 65 0 66,
  checks 4 1 32 (Fixed.ofInt 1) 0 65 0 65,
  checks 4 1 32 (Fixed.ofInt (-1)) 2 65 0 65,
  checks 16 1 4294967296 (Fixed.ofInt 0) 0 255 20 0,
  checks 16 1 4294967297 (Fixed.ofInt 0) 2 255 0 0,
  checks 16 1 32 (Fixed.ofInt 0) 0 0 0 1,
  checks 16 0 32 (Fixed.ofInt 0) (-2147483648) 65 20 65,errors]
end FloorRuntimeFixture
