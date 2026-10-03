import Doom.LevelSpecials
open Doom Doom.LevelSpecials

private structure State where
  special : Nat := 0
  count : Int32 := 0

private def run (s : State) (line : String) : Except String (State × String) := do
  let op :: args := (line.splitOn " ").filter (!·.isEmpty) | throw "level: empty command"
  let args ← args.mapM fun a => do
    let some n := a.toInt? | throw "level: invalid integer"
    if n < -2147483648 || n > 2147483647 then throw "level: integer out of range"
    pure n
  match op,args with
  | "secret",[z,floor,special,count] =>
    let (special,count) := secret special.toNat ⟨Int32.ofInt z⟩ ⟨Int32.ofInt floor⟩ (Int32.ofInt count)
    return (⟨special,count⟩,s!"{special} {count}")
  | "visit",[z,floor] =>
    let (special,count) := secret s.special ⟨Int32.ofInt z⟩ ⟨Int32.ofInt floor⟩ s.count
    return (⟨special,count⟩,s!"{special} {count}")
  | "total",n::values =>
    if n != values.length then throw "level: wrong sector count"
    return (s,s!"{totalSecrets (values.toArray.map Int.toNat)}")
  | "palette",[ep] =>
    let palette := switchList ep.toNat
    return (s,s!"{palette.size}" ++ palette.foldl (fun out name => out ++ " " ++ name) "")
  | "exit",player::side::_flags::special::top::middle::bottom::n::values =>
    if n != values.length || n % 2 != 0 then throw "level: invalid palette"
    let result := exitSwitch values.toArray ⟨top,middle,bottom⟩ special.toNat (player != 0) (side != 0)
    let textures := result.textures
    let trace := if result.switchSound then " s 0" else ""
    return (s,s!"{result.special} {textures.top} {textures.middle} {textures.bottom} {if result.completed then 1 else 0} {if result.completed then 0 else 1} /{trace}")
  | _,_ => throw "level: invalid command"

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "usage: level-probe input.txt")
  let out ← IO.getStdout
  let mut state : State := {}
  for line in (← IO.FS.readFile path).splitOn "\n" do
    if line.trimAscii.isEmpty then continue
    match run state line with
    | .error error => throw (IO.userError error)
    | .ok (next,text) => state := next; out.putStrLn text
