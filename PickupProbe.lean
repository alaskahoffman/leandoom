import Doom.PlayerCounters
import Doom.Things
import Doom.RenderLighting

open Doom Doom.Pickup

private def integer (s : String) : Except String Int32 := do
  let some n := s.toInt? | throw "invalid integer"
  if n < -2147483648 || n > 2147483647 then throw "integer outside int32"
  return Int32.ofInt n

private def bounded (s : String) (n : Nat) : Except String (Fin n) := do
  let v := (← integer s).toInt
  if v < 0 then throw "integer outside enum"
  if h : v.toNat < n then return ⟨v.toNat, h⟩
  throw "integer outside enum"

private def vector (parts : List String) (n : Nat) : Except String (Vector Int32 n) := do
  let values ← parts.toArray.mapM integer
  if h : values.size = n then return ⟨values, h⟩
  throw "invalid vector length"

private def bits (values : Vector Bool n) : Nat := Id.run do
  let mut mask := 0
  for i in [:n] do
    if values[i]! then mask := mask + 2^i
  return mask

private def flags (mask : Int32) (n : Nat) : Vector Bool n :=
  Vector.ofFn fun i => mask.toUInt32.toNat / 2^i.val % 2 != 0

private def showState (s : State) (accepted : Int) (sound : Nat := 0) : String := Id.run do
  let mut text := s!"{accepted} {sound} {s.health} {s.bodyHealth} {s.armor} {s.armorType} {s.readyWeapon.val} {s.pendingWeapon.val} {s.bonus} {s.items} {if s.backpack then 1 else 0} {if s.shadow then 1 else 0}"
  for n in s.ammo.toArray ++ s.maxAmmo.toArray do text := text ++ s!" {n}"
  text := text ++ s!" {bits s.weapons} {bits s.cards}"
  for n in s.powers.toArray do text := text ++ s!" {n}"
  return text ++ " " ++ s.message

private def step (s : State) (p : Profile) (command : List String)
    : Except String (State × Profile × String) := do
  let mut s := s
  let mut p := p
  let mut accepted : Int := -1
  let mut sound := 0
  let mut granted := false
  match command with
  | ["lighttables", sector, extra, orientation, scale, distance] =>
    let light := RenderLighting.level (← integer sector).toInt (← integer extra).toInt (← integer orientation).toInt
    let some scale := scale.toNat? | throw "invalid light scale"
    let some distance := distance.toNat? | throw "invalid light distance"
    return (s,p,s!"{light} {RenderLighting.scaleMap light scale} {RenderLighting.planeMap light distance}")
  | ["light", kind, fixed, normal, fullbright, shadow, invisibility] =>
    let kind := (← bounded kind 6).val
    let fixed := (← bounded fixed 33).val
    let normal := (← bounded normal 32).val
    let fullbright := (← bounded fullbright 2).val != 0
    let shadow := (← bounded shadow 2).val != 0
    let invisibility ← integer invisibility
    let choice := match kind with
      | 2 => some RenderLighting.sky
      | 3 => RenderLighting.sprite fixed normal fullbright shadow
      | 4 => RenderLighting.weapon fixed normal fullbright invisibility
      | _ => some (RenderLighting.surface fixed normal)
    return (s, p, choice.map toString |>.getD "-1")
  | ["editor", kind] =>
    let kind := (← integer kind).toInt.toNat
    let some item := itemOfEditor? kind | return (s, p, "none")
    let some spec := thingDef kind | throw "missing pickup dimensions"
    return (s, p, s!"{item.sprite.val} {if item.countItem then 1 else 0} {spec.radius} {spec.height}")
  | ["counters", damage, fixed] =>
    s := { s with damageCount := ← integer damage, fixedColormap := ← integer fixed }
  | ["think", dead] =>
    let dead := (← bounded dead 2).val != 0
    if !dead then s := s.tickCounters
    let powers := String.intercalate " " (s.powers.toArray.toList.map toString)
    return (s, p, powers ++ s!" {if s.shadow then 1 else 0} {s.bonus} {s.damageCount} {s.fixedColormap} {if dead then 4 else 123}")
  | ["reset"] => s := {}; p := {}
  | ["profile", skill, commercial] => p := ⟨← bounded skill 5, (← bounded commercial 2).val != 0⟩
  | ["base", health, body, armor, typ, ready, pending, bonus, items, backpack, shadow] =>
    s := { s with
      health := ← integer health, bodyHealth := ← integer body, armor := ← integer armor,
      armorType := ← integer typ, readyWeapon := ← bounded ready 9, pendingWeapon := ← bounded pending 10,
      bonus := ← integer bonus, items := ← integer items,
      backpack := (← bounded backpack 2).val != 0, shadow := (← bounded shadow 2).val != 0 }
  | "ammo" :: values => s := { s with ammo := ← vector values 4 }
  | "max" :: values => s := { s with maxAmmo := ← vector values 4 }
  | "powers" :: values => s := { s with powers := ← vector values 6 }
  | ["weapons", mask] => s := { s with weapons := flags (← integer mask) 9 }
  | ["cards", mask] => s := { s with cards := flags (← integer mask) 6 }
  | ["giveammo", ammo, clips] =>
    (granted, s) := s.giveAmmo p (← bounded ammo 5) (← integer clips)
    accepted := if granted then 1 else 0
  | ["giveweapon", weapon, dropped] =>
    (granted, s) := s.giveWeapon p (← bounded weapon 9) ((← bounded dropped 2).val != 0)
    accepted := if granted then 1 else 0
  | ["givebody", count] =>
    (granted, s) := s.giveBody (← integer count); accepted := if granted then 1 else 0
  | ["givearmor", typ] =>
    (granted, s) := s.giveArmor (← integer typ); accepted := if granted then 1 else 0
  | ["givecard", card] => s := s.giveCard (← bounded card 6); accepted := 1
  | ["givepower", power] =>
    (granted, s) := s.givePower (← bounded power 6); accepted := if granted then 1 else 0
  | ["touch", sprite, z, bodyZ, height, dropped, counted] =>
    let item : Item := {
      sprite := ← bounded sprite 36, z := ⟨← integer z⟩,
      dropped := (← bounded dropped 2).val != 0, countItem := (← bounded counted 2).val != 0 }
    let result := s.touch p item ⟨← integer bodyZ⟩ ⟨← integer height⟩
    s := result.state
    accepted := if result.removed then 1 else 0
    sound := match result.sound with | none => 0 | some .item => 1 | some .weapon => 2 | some .power => 3
  | _ => throw "invalid pickup fixture command"
  return (s, p, showState s accepted sound)

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "usage: pickup-probe input.txt")
  let mut s : State := {}
  let mut p : Profile := {}
  let out ← IO.getStdout
  let mut lineNumber := 0
  for line in (← IO.FS.readFile path).splitOn "\n" do
    lineNumber := lineNumber + 1
    if line.trimAscii.isEmpty then continue
    match step s p ((line.splitOn " ").filter (!·.isEmpty)) with
    | .ok (next, profile, text) => s := next; p := profile; out.putStrLn text
    | .error error => throw (IO.userError s!"line {lineNumber}: {error}")
