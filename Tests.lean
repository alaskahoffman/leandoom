import Doom.Controls
import Doom.CombatView
import Doom.Inventory
import Doom.Actors
import Doom.Angles

open Doom

private def expect (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError s!"failed: {label}")

private def tree : Doom.Map := {
  name := "TEST"
  things := #[]
  vertices := #[]
  lines := #[⟨0, 0, 4, 0, 0, 0, 1⟩]
  sides := #[⟨0, 0, "-", "-", "-", 0⟩, ⟨0, 0, "-", "-", "-", 1⟩]
  sectors := #[⟨0, 128, "F", "C", 160, 0, 0⟩, ⟨32, 64, "F", "C", 160, 0, 0⟩]
  segs := #[⟨0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0⟩]
  subsectors := #[⟨1, 0⟩, ⟨1, 1⟩]
  nodes := #[⟨⟨0, 0⟩, ⟨0, 128⟩, default, default, .subsector 0, .subsector 1⟩]
  reject := ByteArray.empty
  blockmap := default
}

def main : IO Unit := do
  expect ((Fixed.ofInt (-3)).raw.toInt == -196608) "signed 16.16 encoding"
  expect ((Fixed.ofInt 32767 + Fixed.ofInt 1).raw.toInt == -2147483648) "addition wraps"
  expect ((Fixed.ofInt (-32768) - Fixed.ofInt 1).raw.toInt == 2147418112) "subtraction wraps"
  expect (((⟨-1⟩ : Fixed) * (⟨32768⟩ : Fixed)).raw.toInt == -1) "multiply arithmetic shift"
  expect ((Fixed.ofInt (-3) * Fixed.ofFloat 0.5).raw.toInt == -98304) "negative multiply"
  expect ((Fixed.div? (⟨-1⟩ : Fixed) (Fixed.ofInt 3)).map (·.raw.toInt) == some 0) "division truncates toward zero"
  expect ((Fixed.div? (Fixed.ofInt 3) (Fixed.ofInt 2)).map (·.raw.toInt) == some 98304) "fixed division"
  expect ((Fixed.div? (Fixed.ofInt 1) (Fixed.ofInt 0)).isNone) "division rejects zero"
  expect ((Fixed.divChecked (Fixed.ofInt (-3)) (Fixed.ofInt 2)).toOption.map (·.raw.toInt) == some (-98304)) "reference division truncates signed quotient"
  expect ((Fixed.divChecked ⟨65536⟩ ⟨4⟩).toOption.map (·.raw.toInt) == some 2147483647) "reference division saturates conservatively before overflow"
  expect ((Fixed.divChecked ⟨65536⟩ ⟨5⟩).toOption.map (·.raw.toInt) == some 858993459) "reference division just below saturation boundary"
  expect ((Fixed.divChecked ⟨-1⟩ ⟨0⟩).toOption.map (·.raw.toInt) == some (-2147483648)) "reference division saturates negative zero divisor"
  expect ((Fixed.divChecked ⟨0⟩ ⟨0⟩).toOption.map (·.raw.toInt) == some 2147483647) "reference division saturates zero over zero"
  expect ((Fixed.divChecked ⟨-2147483648⟩ ⟨1⟩).toOption.isNone) "unverified absolute overflow is explicit"
  expect ((Angle.fromVector (Fixed.ofInt 0) (Fixed.ofInt 1)).raw == 0x3fffffff) "north keeps original angle asymmetry"
  expect ((⟨0⟩ : Angle).fineSine.raw == 25 && (⟨0⟩ : Angle).fineCosine.raw == 65535) "fine angles retain original half-bin table samples"
  expect ((slopeDiv 0x20000000 512).val == 0) "slope numerator wraps before division"
  expect ((Angle.ofDegrees 360).raw == 0) "angle wraps"
  expect ((Angle.ofDegrees (-90)).raw == 3221225472) "negative angle"
  expect ((Angle.ofDegrees 0 |>.turn (-0.1)).raw > 4000000000) "negative incremental turn wraps"
  let east := Fixed.ofInt 1
  let west := Fixed.ofInt (-1)
  let zero := Fixed.ofInt 0
  expect ((tree.subsectorAt east zero).toOption == some 0) "BSP east/right"
  expect ((tree.subsectorAt west zero).toOption == some 1) "BSP west/left"
  expect ((tree.subsectorAt zero zero).toOption == some 1) "BSP vertical tie"
  expect ((tree.sectorAt east zero).toOption == some 0) "front sector lookup"
  expect ((tree.sectorAt west zero).toOption == some 1) "back sector lookup"
  expect (tree.frontToBack east zero == #[0, 1]) "BSP near-first east"
  expect (tree.frontToBack west zero == #[1, 0]) "BSP near-first west"
  let horizontal : Node := ⟨⟨0, 0⟩, ⟨128, 0⟩, default, default, .subsector 0, .subsector 1⟩
  expect (!horizontal.onLeft zero zero && horizontal.onLeft zero east) "BSP horizontal tie"
  let diagonal : Node := ⟨⟨0, 0⟩, ⟨128, 128⟩, default, default, .subsector 0, .subsector 1⟩
  expect (diagonal.onLeft zero zero && !diagonal.onLeft east zero) "BSP diagonal tie"
  let fineDiagonal : Node := ⟨⟨0, 0⟩, ⟨1, 1⟩, default, default, .subsector 0, .subsector 1⟩
  expect (fineDiagonal.onLeft ⟨1⟩ zero) "BSP rounds a sub-unit near miss onto side 1"
  let cyclic := { tree with nodes := #[{ tree.nodes[0]! with right := .node 0 }] }
  expect ((cyclic.subsectorAt east zero).toOption.isNone) "bounded malformed BSP query"
  let boundsMap : Doom.Map := { tree with
    vertices := #[⟨128,128⟩,⟨256,256⟩]
    lines := #[{ tree.lines[0]! with v2 := 1, flags := 0 }]
    blockmap := { origin := ⟨0,0⟩, width := 4, height := 4, cells := Array.replicate 16 #[] } }
  expect ((Collision.mapSectorBlocks boundsMap 0).toOption == some ⟨0,2,0,2⟩) "sector bounds include both line vertices and MAXRADIUS"
  expect ((Collision.mapSectorBlocks boundsMap 1).toOption == some ⟨0,2,0,2⟩) "sector bounds include back sector even without two-sided flag"
  let camera : Camera := ⟨zero, zero, Fixed.ofInt 41, Angle.ofDegrees 0⟩
  expect ((camera.move 2 0.05).x.toFloat == 8.0) "forward movement"
  expect ((camera.move 16 0.05).y.toFloat == -8.0) "right strafe"
  expect ((camera.move 6 0.05).x.toFloat == 0.0) "opposing keys cancel"
  expect ((camera.move 2 1.0).x.toFloat == 8.0) "long frame time clamped"
  expect ((camera.move 128 0.05).z.toFloat == 49.0) "vertical movement"
  expect ((camera.move 2 (-1.0)).x.toFloat == 0.0) "negative elapsed ignored"
  expect (skyForMap "E1M1" == "SKY1" && skyForMap "E2M1" == "SKY2") "episode skies 1/2"
  expect (skyForMap "E3M1" == "SKY3" && skyForMap "E4M1" == "SKY4") "episode skies 3/4"
  expect (skyForMap "MAP11" == "SKY1" && skyForMap "MAP12" == "SKY2") "Doom II sky boundary 11/12"
  expect (skyForMap "MAP20" == "SKY2" && skyForMap "MAP21" == "SKY3") "Doom II sky boundary 20/21"
  let art : Art := {
    palettes := ⟨Array.replicate 768 20 ++ Array.replicate 768 90⟩
    colormaps := ⟨Array.replicate (32*256) 0⟩
    lumps := #[]
    pnames := #[]
    definitions := {}
  }
  expect (art.color 0 == ⟨20, 20, 20⟩) "base palette"
  expect (art.color 0 0 1 == ⟨90, 90, 90⟩) "alternate palette"
  let texture : Texture := ⟨2, 1, ⟨#[255, 3]⟩, ⟨#[1, 0]⟩⟩
  expect (texture.sample (-2) 0 == some 255) "negative texture coordinate wrap"
  expect ((texture.sample 1 0).isNone) "transparent texel"
  let injured : Inventory := { health := 95 }
  expect (((injured.pickup 2011).map (·.1.health)) == some 100) "stimpack heals up to normal cap"
  expect (((({ health := 20 } : Inventory).pickup 2012).map (·.1.health)) == some 45) "medikit heals 25"
  expect ((({ health := 150 } : Inventory).pickup 2012).isNone) "medikit cannot reduce bonus health"
  expect (((({ health := 20 } : Inventory).pickup 2023).map (·.1.health)) == some 100) "berserk heals"
  expect ((thingPose 49 24).map (·.frame) == some "GOR1B") "unequal decoration frame duration"
  expect ((thingPose 49 25).map (·.frame) == some "GOR1C") "decoration frame boundary"
  expect ((thingPose 23 5).isSome && (thingPose 23 6).isNone) "dead lost soul reaches null state"
  let green : Inventory := { armor := 100, armorType := 1 }
  expect ((green.damage 30).health == 80 && (green.damage 30).armor == 90) "green armor absorbs one third"
  let blue : Inventory := { armor := 200, armorType := 2 }
  expect ((blue.damage 30).health == 85 && (blue.damage 30).armor == 185) "blue armor absorbs half"
  let exhausted : Inventory := { armor := 2, armorType := 2 }
  expect ((exhausted.damage 30).health == 72 && (exhausted.damage 30).armorType == 0) "armor exhaustion"
  expect (({ invulnerability := 1 } : Inventory).damage 100 == { invulnerability := 1 }) "invulnerability"
  expect (({ health := 0 } : Inventory).damage 30 == { health := 0 }) "dead players take no further damage"
  expect ((({} : Inventory).pickup 2007 true).map (·.1.bullets) == some 55) "dropped clip gives five bullets"
  expect ((({} : Inventory).pickup 2001 true).map (·.1.shells) == some 4) "dropped shotgun gives four shells"
  expect (randomTable.size == 256 && randomTable[1]! == 8 && randomTable[255]! == 249) "random table bounds and endpoints"
  let streams : DoomRandom := {}
  expect (streams.nextMisc.2.nextPlay.1 == 8 && streams.nextMisc.2.nextPlay.2.misc == 1) "independent random streams"
  expect (({ play := 255 } : DoomRandom).nextPlay == (0, {})) "random index wraps before table access"
  expect (streams.subPlay.1 == -101 && streams.subPlay.2.play == 2) "random subtraction preserves draw order"
  let dead : Actor := { thing := 0, kind := 3004, health := 0, mode := .dying, age := 1000 }
  expect (dead.pose.frame == "POSSL") "corpse holds terminal pose"
  let powers := Inventory.fromPickup { powers := #v[2,41,1,2,1,2], shadow := true, bonus := 2 }
  let advanced := powers.tick
  expect (advanced.pickupState.powers == #v[1,42,0,1,1,1]) "runtime retains berserk count and advances timed powers"
  expect (!advanced.pickupState.shadow && advanced.pickupState.bonus == 1) "invisibility clears at expiry; bonus fades"
  expect (advanced.tick.pickupState.powers == #v[0,43,0,0,1,0]) "runtime counter state survives inventory round trip"
  let deadInventory := { powers with health := 0 }
  expect (deadInventory.tick == deadInventory) "dead branch does not tick live counters"
  let staleShadow := Inventory.fromPickup { shadow := true }
  expect staleShadow.tick.pickupState.shadow "zero invisibility does not itself clear shadow"
  let fuzzFrame : IndexedFrame := {}
  let fuzzFrame := fuzzFrame.fuzzPost art 10 0 200
  expect (fuzzFrame.phase.val == 48) "fuzz excludes border rows and advances shared phase"
  let nextFuzzFrame := fuzzFrame.fuzzPost art 11 10 15
  expect (nextFuzzFrame.phase.val == 3) "fuzz phase persists across posts and wraps"
  expect (nextFuzzFrame.indices.size == 64000 && nextFuzzFrame.rgb.size == 192000) "indexed and RGB buffers retain full frame size"
  let emptyMap := { tree with nodes := #[], subsectors := #[⟨0,0⟩], segs := #[] }
  let weapon : Patch := ⟨⟨1,3,⟨#[1,2,3]⟩,⟨#[1,1,1]⟩⟩,-150,-100⟩
  let assets : Assets := {
    art, walls := {}, flats := {}, sky := none, weapons := ({} : Std.HashMap String Patch).insert "PISGA0" weapon }
  let simulation : Simulation := {
    map := emptyMap, original := emptyMap, player := { camera, feet := 0 }, combatEnabled := true,
    inventory := Inventory.fromPickup { powers := #v[0,0,2100,0,0,0], shadow := true } }
  let .ok (_, firstPhase) := simulation.drawFrame assets | throw (IO.userError "first fuzz presentation failed")
  let .ok (_, secondPhase) := simulation.drawFrame assets none firstPhase | throw (IO.userError "second fuzz presentation failed")
  expect (firstPhase.val == 3) "weapon presentation advances fuzz phase for visible pixels"
  expect (secondPhase.val == 6) "successive presentations advance phase even without a game tic"
  let shortFrame : IndexedFrame := { viewHeight := 168 }
  let shortFuzz := shortFrame.fuzzPost art 100 0 168
  expect (shortFuzz.phase.val == 16) "status view fuzz visits 166 interior rows"
  expect (shortFuzz.indices[167*320+100]! == shortFrame.indices[167*320+100]!) "fuzz leaves last world row above bar untouched"
  let persisted : Status.Face := { count := 12, priority := 8, lastAttack := 40, index := 6, oldHealth := 80 }
  let restarted := persisted.start {}
  expect (restarted.count == 12 && restarted.priority == 8 && restarted.lastAttack == 40 && restarted.index == 0 && restarted.oldHealth == -1) "status start preserves original static timers while resetting face and health cache"
  IO.println "80 arithmetic, BSP, sector bounds, rendering, inventory, animation, and combat checks passed"
