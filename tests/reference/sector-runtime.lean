import Doom.Simulation
open Doom Doom.Collision

/-- Deliberately different incoming Player and collision-actor positions, a
sector floor different from collision floorz, and a nonzero selected index. -/
def fixture (z : Fixed) (timer : Int32) : Simulation := Id.run do
  let sector : Sector := ⟨0,128,"FLOOR","CEIL",160,9,0⟩
  let map : Map := ⟨"test",#[],#[],#[{ (default : Linedef) with front := 0, back := 65535 }],
    #[{ (default : Sidedef) with sector := 1 }],#[{ sector with special := 7 },sector],
    #[default],#[⟨1,0⟩],#[],ByteArray.empty,default⟩
  let actor : SolidThing := { (default : SolidThing) with
    x := Fixed.ofInt 12, y := Fixed.ofInt 23, z, floor := Fixed.ofInt 32, ceiling := Fixed.ofInt 128 }
  let scene : Scene := {
    grid := default, lines := #[default], links := #[], things := #[actor],
    sectors := #[⟨Fixed.ofInt 0,Fixed.ofInt 128⟩,⟨Fixed.ofInt 0,Fixed.ofInt 128⟩] }
  let player : Player := { (default : Player) with
    body := { x := Fixed.ofInt 999, y := Fixed.ofInt 998, z := Fixed.ofInt 997 },
    reactionTime := timer, scene := some scene }
  return { map, original := map, player, secrets := 2147483647, ticks := 123 }

def cmd : Ticcmd := { forwardMove := 50, sideMove := -40, angleTurn := 1000 }

def success (z : Fixed) (timer : Int32) : Bool :=
  let s := fixture z timer
  match s.prepareSectorTick 0 (some cmd) with
  | .error _ => false
  | .ok (out,actual) =>
    let onFloor := z == Fixed.ofInt 0
    out.player.body.x == Fixed.ofInt 12 && out.player.body.y == Fixed.ofInt 23 && out.player.body.z == z &&
    out.map.sectors[1]!.special == (if onFloor then 0 else 9) &&
    out.secrets == (if onFloor then -2147483648 else 2147483647) &&
    out.map.sectors[0]!.special == 7 && out.ticks == 123 && out.physicsError.isNone &&
    out.player.reactionTime == PlayerReaction.remaining timer &&
    actual.forwardMove == cmd.forwardMove && actual.sideMove == cmd.sideMove && actual.angleTurn == cmd.angleTurn &&
    (match out.prepareSectorTick 0 (some cmd) with
      | .error _ => false
      | .ok (again,_) => again.secrets == out.secrets)

def errors : Bool := Id.run do
  let s := fixture (Fixed.ofInt 0) 2
  let missing := { s with player := { s.player with scene := none } }
  let badBsp := { s with map := { s.map with subsectors := #[] } }
  let a := match missing.prepareSectorTick 0 (some cmd) with
    | .ok _ => false
    | .error failed => failed.player.body.x == Fixed.ofInt 999 && failed.player.reactionTime == 2 &&
      failed.secrets == s.secrets && failed.physicsError == some "player: missing collision scene"
  let b := match badBsp.prepareSectorTick 0 (some cmd) with
    | .ok _ => false
    | .error failed => failed.player.body.x == Fixed.ofInt 12 && failed.player.reactionTime == 1 &&
      failed.secrets == s.secrets && failed.physicsError == some "BSP: invalid subsector"
  return a && b

#eval [success (Fixed.ofInt 0) 0,success (Fixed.ofInt 0) 1,
  success (Fixed.ofInt 0) (-2147483648),success (Fixed.ofInt 1) 0,success (Fixed.ofInt 1) 1,errors]
