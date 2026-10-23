import Doom.Weapon
open Doom

def main (args : List String) : IO UInt32 := do
  let [input,output] := args | throw (IO.userError "flash-update-probe input output")
  let mut out := ""
  for line in (← IO.FS.readFile input).splitOn "\n" do
    if line.isEmpty then continue
    let [id,timer,light,x,y] := line.splitOn " " | throw (IO.userError "invalid flash input")
    let v : Weapon.State := {
      flash := { frame := id.toNat!, tics := Int32.ofInt timer.toInt! }
      extraLight := Int32.ofInt light.toInt!
      weapon := { x := ⟨Int32.ofInt x.toInt!⟩, y := ⟨Int32.ofInt y.toInt!⟩ } }
    let t := Weapon.tickFlash v
    let ptr := if t.flash.frame=0 then 0 else 0x15a28+28*t.flash.frame
    out := out ++ s!"{ptr} {t.flash.tics.toUInt32.toNat} {t.extraLight.toUInt32.toNat} {t.flash.x.raw.toUInt32.toNat} {t.flash.y.raw.toUInt32.toNat}\n"
  IO.FS.writeFile output out
  return 0
