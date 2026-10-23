import Doom.Weapon
open Doom
def main (args : List String) : IO Unit := do
  let [input,output] := args | throw (IO.userError "expected input output")
  let data ← IO.FS.readFile input
  let mut result := ""
  for line in data.splitOn "\n" do
    if line.isEmpty then continue
    let [p,h,a] := line.splitOn " " | throw (IO.userError "expected pending health attack")
    let some p := p.toNat? | throw (IO.userError "pending")
    let some hp := h.toInt? | throw (IO.userError "health")
    let pc := match Weapon.readyDecision p (Int32.ofInt hp) (a=="1") with
      | .lower => 0x2d040 | .fire => 0x2d410 | .idle => 0x2d392
    result := result ++ toString pc ++ "\n"
  IO.FS.writeFile output result
