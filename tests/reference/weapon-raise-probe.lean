import Doom.Weapon
open Doom

def main (args : List String) : IO UInt32 := do
  let [input,output] := args | throw (IO.userError "weapon-raise-probe input output")
  let mut rows : Array String := #[]
  for line in (← IO.FS.readFile input).splitOn "\n" do
    if line.isEmpty then continue
    let y : Fixed := ⟨Int32.ofInt line.toInt!⟩
    let (height,ready) := Weapon.raiseStep y
    rows := rows.push s!"{height.raw.toUInt32.toNat} {if ready then 1 else 0}"
  IO.FS.writeFile output (String.intercalate "\n" rows.toList ++ "\n")
  return 0
