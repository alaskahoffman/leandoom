import Doom.Status
open Doom

private def mask (v : Vector Bool n) : Nat :=
  (Array.range n).foldl (fun m i => if v[i]! then m + 2^i else m) 0

private def stateText (s : Status.Face) : String :=
  s!"{s.index} {s.count} {s.oldHealth} {mask s.oldWeapons}"

private def run (face : Status.Face) (line : String) : Except String (Status.Face × String) := do
  let words := (line.splitOn " ").filter (!·.isEmpty)
  let args ← (words.drop 1).mapM fun s => do
    let some n := s.toInt? | throw "status: invalid integer"
    if n < -2147483648 || n > 4294967295 then throw "status: integer out of range"
    pure n
  match words.head?, args with
  | some "num", [v,w,d] =>
    if (w != 2 && w != 3) || d < 1 || d > 16 || v > 2147483647 then throw "status: invalid number range"
    let result := (Status.digits v w.toNat d.toNat 44).foldl (fun s d => s ++ s!" {d.x}:{d.digit}") "num"
    return (face,result)
  | some "palette", [damage,bonus,strength,suit] =>
    if [damage,bonus,strength,suit].any (fun n => n < 0 || n > 1000000) then throw "status: invalid palette range"
    let p : Pickup.State := {
      damageCount := Int32.ofInt damage, bonus := Int32.ofInt bonus
      powers := #v[0,Int32.ofInt strength,0,Int32.ofInt suit,0,0] }
    return (face,s!"{Status.palette p}")
  | some "start", [weapons] =>
    if weapons < 0 || weapons > 511 then throw "status: invalid weapons"
    let p : Pickup.State := { weapons := Vector.ofFn (fun i => weapons.toNat / 2^i.val % 2 == 1) }
    let next := face.start p
    return (next,stateText next)
  | some "face", [h,d,b,inv,weapons,attack,god,angle,bad,r] =>
    if h < 0 || h > 200 || d < 0 || d > 100 || b < 0 || b > 100 || inv < 0 || inv > 1000000 ||
       weapons < 0 || weapons > 511 || attack < 0 || attack > 1 || god < 0 || god > 1 ||
       angle < 0 || bad < -1 || r < 0 || r > 255 then throw "status: invalid face range"
    let p : Pickup.State := {
      health := Int32.ofInt h, damageCount := Int32.ofInt d, bonus := Int32.ofInt b
      powers := #v[Int32.ofInt inv,0,0,0,0,0]
      weapons := Vector.ofFn (fun i => weapons.toNat / 2^i.val % 2 == 1) }
    let next := face.tick {
      player := p, attack := attack != 0, god := god != 0
      angle := angle.toNat.toUInt32, attackerAngle := if bad < 0 then none else some bad.toNat.toUInt32
      random := r.toNat }
    return (next,stateText next)
  | some "widgets", [weapon,keys,a,b,c,d] =>
    if weapon < 0 || weapon > 8 || keys < 0 || keys > 63 then throw "status: invalid widget range"
    let w := weapon.toNat
    if hw : w < 9 then
      let p : Pickup.State := {
        readyWeapon := ⟨w,hw⟩, cards := Vector.ofFn (fun i => keys.toNat / 2^i.val % 2 == 1)
        ammo := #v[Int32.ofInt a,Int32.ofInt b,Int32.ofInt c,Int32.ofInt d] }
      let k := fun (i : Fin 3) => (Status.key p i).map Int.ofNat |>.getD (-1)
      return (face,s!"{Status.readyAmmo p} {k 0} {k 1} {k 2}")
    else throw "status: invalid weapon"
  | _,_ => throw "status: invalid command"

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "usage: status-probe input.txt")
  let mut face : Status.Face := {}
  let out ← IO.getStdout
  for line in (← IO.FS.readFile path).splitOn "\n" do
    if line.trimAscii.isEmpty then continue
    match run face line with
    | .error error => throw (IO.userError error)
    | .ok (next,text) => face := next; out.putStrLn text
