import Doom.Weapon
open Doom

def main (args : List String) : IO UInt32 := do
  let [input,output] := args | throw (IO.userError "weapon-ready-probe input output")
  let mut rows : Array String := #[]
  for line in (← IO.FS.readFile input).splitOn "\n" do
    if line.isEmpty then continue
    let [a,t] := line.splitOn " " | throw (IO.userError "amplitude time")
    let v := Weapon.readyIdle {} ⟨Int32.ofInt a.toInt!⟩ (Int32.ofInt t.toInt!)
    rows := rows.push s!"{v.weapon.x.raw.toUInt32.toNat} {v.weapon.y.raw.toUInt32.toNat} {if v.attackDown then 1 else 0}"
  IO.FS.writeFile output (String.intercalate "\n" rows.toList ++ "\n")
  return 0
