import Doom.Replay
import Doom.Proofs.Movement
import Doom.Proofs.AutoAim
import Doom.Proofs.Firing

namespace Doom.Demo
open Lean

private def momentum (body : Motion) : Json := Json.mkObj [
  ("x",toJson body.momx.raw.toInt), ("y",toJson body.momy.raw.toInt),
  -- Strings preserve exact integers in JavaScript, including squared Int32 values.
  ("squared",toJson (toString (Proofs.speedSquared body)))]

private def aimSource (s : Simulation) : String := Id.run do
  let mut code := "-- Autoaim: the ray stays inside the clipped vertical window.\n"
  if let some shot := s.lastFire then
    let gun := if shot.gun == .pistol then "pistol" else "shotgun"
    code := code ++ s!"-- Last {gun} shot, tic {shot.tic}.\n"
    if let some aim := shot.aim then
      code := code ++ s!"-- Facing {aim.facing.raw.toNat}; aim probe offset {aim.offset.toNat}.\n"
      code := code ++ "-- Fired yaw: " ++ String.intercalate ", " (shot.pelletAngles.toList.map (toString ∘ UInt32.toNat)) ++ ".\n"
      if let some w := aim.window then
        let lo := w.bottom.toInt
        let hi := w.top.toInt
        let d := w.distance.raw.toInt
        -- Original arithmetic on unusual maps can leave this theorem's domain.
        -- Preserve the engine result and say so; never invent a proof instance.
        if -40960 ≤ lo && lo ≤ hi && hi ≤ 40960 && 0 ≤ d && d ≤ 67108864 then
          let lower := ((⟨w.bottom⟩ : Fixed) * w.distance).raw.toInt
          let rise := (aim.slope * w.distance).raw.toInt
          let upper := ((⟨w.top⟩ : Fixed) * w.distance).raw.toInt
          code := code ++ s!"-- Target {w.target}; muzzle z {w.shootZ.raw.toInt}; distance {d} (16.16).\n"
          code := code ++ s!"def bottom : Int32 := max ({w.targetBottom.toInt}) ({w.portalBottom.toInt})\n"
          code := code ++ s!"def top : Int32 := min ({w.targetTop.toInt}) ({w.portalTop.toInt})\n"
          code := code ++ s!"\nexample : ({lo} : Int) ≤ {aim.slope.raw.toInt} ∧ ({aim.slope.raw.toInt} : Int) ≤ {hi} := by\n"
          code := code ++ "  exact autoaim_center_inside bottom top (by decide) (by decide) (by decide)\n"
          code := code ++ s!"\n-- Vertical rise at target distance, relative to muzzle (16.16).\nexample : ({lower} : Int) ≤ {rise} ∧ ({rise} : Int) ≤ {upper} := by\n"
          code := code ++ s!"  exact autoaim_trajectory_inside bottom top ({d})\n    (by decide) (by decide) (by decide) (by decide) (by decide)\n"
          code := code ++ "-- The theorem holds at EVERY distance from 0 to 1024 map units.\n"
          return code
        code := code ++ "-- This observed window lies outside the theorem's stated bounds.\n"
      else
        code := code ++ s!"-- No autoaim target found. Actual slope: {aim.slope.raw.toInt}.\n"
  else code := code ++ "-- Fire toward an actor to fill in an observed instance.\n"
  code := code ++ "example (bottom top distance : Int32)\n    (lo : -40960 ≤ bottom.toInt) (ordered : bottom.toInt ≤ top.toInt)\n    (hi : top.toInt ≤ 40960)\n    (near : 0 ≤ distance.toInt) (far : distance.toInt ≤ 67108864) :\n    ((⟨bottom⟩ : Fixed) * ⟨distance⟩).raw.toInt ≤\n      (AutoAim.center bottom top * ⟨distance⟩).raw.toInt ∧\n    (AutoAim.center bottom top * ⟨distance⟩).raw.toInt ≤\n      ((⟨top⟩ : Fixed) * ⟨distance⟩).raw.toInt := by\n  exact autoaim_trajectory_inside bottom top distance lo ordered hi near far\n"
  return code

/-- A compilable Lean file whose examples use the observed integers. It is
shown as source, not presented as a new interactive proof search. -/
def source (s : Simulation) (flying : Bool := false) : String := Id.run do
  let v := s.player.body
  let speed := Float.sqrt (v.momx.toFloat*v.momx.toFloat + v.momy.toFloat*v.momy.toFloat)
  let mut code := "import Doom.Proofs.Movement\nimport Doom.Proofs.AutoAim\nopen Doom Doom.Proofs\n\n"
  code := code ++ s!"-- tic {s.ticks} · speed {speed} map units/tic\n"
  code := code ++ "-- Theorems checked at build time; live instances below.\n"
  if flying then code := code ++ "-- Free camera: showing the player's last movement sample.\n"
  else if s.inventory.health == 0 then code := code ++ "-- Player dead: showing the last live-player friction sample.\n"
  if let some f := s.player.frictionSample then
    code := code ++ "\ndef body : Motion :=\n  { momx := ⟨" ++ toString f.before.momx.raw.toInt ++
      "⟩, momy := ⟨" ++ toString f.before.momy.raw.toInt ++ "⟩,\n    z := ⟨" ++ toString f.before.z.raw.toInt ++
      "⟩, floorz := ⟨" ++ toString f.before.floorz.raw.toInt ++ "⟩, noMomentum := " ++
      (if f.before.noMomentum then "true" else "false") ++ " }\n"
    code := code ++ "def cmd : Ticcmd := { forwardMove := " ++ toString f.cmd.forwardMove.toInt ++
      ", sideMove := " ++ toString f.cmd.sideMove.toInt ++ " }\n"
    code := code ++ s!"\n-- Squared speed after friction ≤ before friction (exact).\nexample : {Proofs.speedSquared f.after} ≤ {Proofs.speedSquared f.before} := by\n"
  else
    code := code ++ "\n-- At rest: XY movement skipped the friction call.\n"
    code := code ++ "example (body : Motion) (cmd : Ticcmd) :\n    speedSquared (body.friction cmd) ≤ speedSquared body := by\n"
  code := code ++ "  obtain ⟨hx, hy⟩ := friction_does_not_accelerate body cmd\n"
  code := code ++ "  exact Nat.add_le_add (Nat.mul_le_mul hx hx)\n                      (Nat.mul_le_mul hy hy)\n\n"
  code := code ++ aimSource s
  return code

private def aimJson (s : Simulation) : Json :=
  match s.lastFire.bind (·.aim) with
  | none => .null
  | some aim => Json.mkObj [
      ("slope",toJson aim.slope.raw.toInt), ("facing",toJson aim.facing.raw.toNat),
      ("offset",toJson aim.offset.toNat),
      ("pelletAngles",toJson ((s.lastFire.map (·.pelletAngles) |>.getD #[]).map UInt32.toNat)),
      ("window",match aim.window with
        | none => .null
        | some w => Json.mkObj [
          ("target",toJson w.target), ("distance",toJson w.distance.raw.toInt),
          ("targetZ",toJson w.targetZ.raw.toInt), ("targetHeight",toJson w.targetHeight.raw.toInt),
          ("portals",toJson (w.portals.map fun p => Json.mkObj [
            ("distance",toJson p.distance.raw.toInt), ("bottom",toJson p.bottom.raw.toInt),
            ("top",toJson p.top.raw.toInt), ("line",toJson p.line)])),
          ("shootZ",toJson w.shootZ.raw.toInt),
          ("portalBottom",toJson w.portalBottom.toInt), ("portalTop",toJson w.portalTop.toInt),
          ("targetBottom",toJson w.targetBottom.toInt), ("targetTop",toJson w.targetTop.toInt),
          ("bottom",toJson w.bottom.toInt), ("top",toJson w.top.toInt)])]

/-- Read-only observations. Importing the proof modules makes a successful
viewer build depend on checking the theorems; polling does not prove new goals. -/
def snapshot (s : Simulation) (flying : Bool := false) (keys : UInt32 := 0) : Json :=
  Json.mkObj [
    ("schema",toJson (1 : Nat)), ("status",toJson "running"),
    ("source",toJson (source s flying)), ("aim",aimJson s),
    ("tic",toJson s.ticks), ("keys",toJson keys.toNat),
    ("health",toJson s.inventory.health), ("flying",toJson flying),
    ("grounded",toJson (decide (s.player.body.z.raw ≤ s.player.body.floorz.raw))),
    ("exitRequested",toJson s.exitRequested),
    ("movement",Json.mkObj [
      ("live",momentum s.player.body),
      ("sampleTic",toJson s.player.levelTime.toInt),
      ("friction",match s.player.frictionSample with
        | none => .null
        | some sample => Json.mkObj [
          ("before",momentum sample.before), ("after",momentum sample.after),
          ("forward",toJson sample.cmd.forwardMove.toInt),
          ("side",toJson sample.cmd.sideMove.toInt),
          ("grounded",toJson (decide (sample.before.z.raw ≤ sample.before.floorz.raw))),
          ("noMomentum",toJson sample.before.noMomentum)])]),
    ("weapon",Json.mkObj [
      ("ready",toJson s.inventory.pickupState.readyWeapon.val),
      ("pending",toJson s.inventory.pickupState.pendingWeapon.val),
      ("frame",toJson (Weapon.label s.weapon.weapon)),
      ("tics",toJson s.weapon.weapon.tics.toInt),
      ("bullets",toJson s.inventory.bullets), ("shells",toJson s.inventory.shells),
      ("pistolCycle",toJson Fire.Gun.pistol.cycleTics),
      ("shotgunCycle",toJson Fire.Gun.shotgun.cycleTics),
      ("lastFire",match s.lastFire with
        | none => .null
        | some shot => Json.mkObj [
          ("gun",toJson (if shot.gun == .pistol then "pistol" else "shotgun")),
          ("tic",toJson shot.tic), ("before",toJson shot.ammoBefore.toInt),
          ("after",toJson shot.ammoAfter.toInt),
          ("expected",toJson shot.pelletsExpected), ("traced",toJson shot.pelletsTraced)])])]

/-- Same-directory rename: readers see one complete snapshot. -/
def writeSnapshot (path : System.FilePath) (json : Json) : IO Unit := do
  let temporary := System.FilePath.mk (path.toString ++ ".tmp")
  IO.FS.writeFile temporary json.compress
  IO.FS.rename temporary path

end Doom.Demo
