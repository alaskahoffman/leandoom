import Doom.Weapon
open Doom

def main (args : List String) : IO UInt32 := do
  let [input,output] := args | throw (IO.userError "weapon-flash-probe input output")
  let mut out := ""
  for line in (← IO.FS.readFile input).splitOn "\n" do
    if line.isEmpty then continue
    let [wid,wt,id,timer,light,x,y] := line.splitOn " " | throw (IO.userError "invalid input")
    let c : Weapon.Context := { events := #[.noise], state := {
      flash := { frame := id.toNat!, tics := Int32.ofInt timer.toInt! }
      extraLight := Int32.ofInt light.toInt!
      weapon := { frame := wid.toNat!, tics := Int32.ofInt wt.toInt!, x := ⟨Int32.ofInt x.toInt!⟩, y := ⟨Int32.ofInt y.toInt!⟩ } } }
    let t := Weapon.tick c
    let ptr := if t.state.flash.frame=0 then 0 else 0x15a28+28*t.state.flash.frame
    out := out ++ s!"{ptr} {t.state.flash.tics.toUInt32.toNat} {t.state.extraLight.toUInt32.toNat} {t.state.flash.x.raw.toUInt32.toNat} {t.state.flash.y.raw.toUInt32.toNat} {t.state.weapon.tics.toUInt32.toNat} {t.events.size}\n"
  IO.FS.writeFile output out
  return 0
