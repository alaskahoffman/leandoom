import Doom.VerticalDoor
open Doom

private def kinds : Array VerticalDoor.Kind :=
  #[.normal,.close30ThenOpen,.close,.open,.raiseIn5Mins,.blazeRaise,.blazeOpen,.blazeClose]

private structure World where
  door : VerticalDoor.State := {}
  heights : Plane.Heights := {}
  removed : Bool := false
  started : Bool := false

private structure Trace where
  mask : Nat
  calls : Nat := 0
  text : String := ""

private def change (h : Plane.Heights) (crush : Bool) (t : Trace) : Bool × Trace :=
  (t.mask / 2^t.calls % 2 == 1, { t with
    calls := t.calls+1,
    text := t.text ++ s!" c {h.floor.raw.toInt} {h.ceiling.raw.toInt} {if crush then 1 else 0}" })

private def dump (w : World) (trace : String := "") : String :=
  let d := w.door
  let kind := (kinds.findIdx? (· == d.kind)).getD 0
  s!"d {kind} {w.heights.floor.raw.toInt} {w.heights.ceiling.raw.toInt} {d.speed.raw.toInt} {d.top.raw.toInt} {d.direction.toInt} {d.topWait.toInt} {d.countdown.toInt} {if w.removed then 1 else 0} {if w.removed then 0 else 1} /{trace}"

private def parse (s : String) : Except String Int := do
  let some n := s.toInt? | throw "doors: invalid integer"
  if n < -2147483648 || n > 2147483647 then throw "doors: integer outside signed 32-bit range"
  return n

private def fixed (i : Int) : Fixed := ⟨Int32.ofInt i⟩

private def run (w : World) (line : String) : Except String (World × String) := do
  let op :: rest := (line.splitOn " ").filter (!·.isEmpty) | throw "doors: empty command"
  let values ← rest.mapM parse
  match op,values with
  | "plane",[floor,ceiling,speed,dest,crush,plane,direction,mask] =>
    if speed < 0 || crush < 0 || crush > 1 || plane < 0 || plane > 1 ||
        (direction != -1 && direction != 1) || mask < 0 || mask > 3 then throw "doors: invalid plane input"
    let result := Plane.move ⟨fixed floor,fixed ceiling⟩ (fixed speed) (fixed dest) (crush == 1)
      (if plane == 0 then .floor else .ceiling) (Int32.ofInt direction) ({ mask := mask.toNat } : Trace) change
    let code := match result.result with | .ok => 0 | .crushed => 1 | .pastDestination => 2
    return (w,s!"p {code} {result.heights.floor.raw.toInt} {result.heights.ceiling.raw.toInt} /{result.state.text}")
  | "door",[kind,floor,ceiling,speed,top,direction,wait,count] =>
    if kind < 0 || kind > 7 || speed < 0 || direction < -1 || direction > 2 then throw "doors: invalid door input"
    let door : VerticalDoor.State := {
      kind := kinds[kind.toNat]!, top := fixed top, speed := fixed speed,
      direction := Int32.ofInt direction, topWait := Int32.ofInt wait, countdown := Int32.ofInt count }
    let next : World := { door, heights := ⟨fixed floor,fixed ceiling⟩, started := true }
    return (next,dump next)
  | "tick",[mask] =>
    if !w.started || mask < 0 || mask > 3 then throw "doors: invalid tick input"
    if w.removed then return (w,dump w)
    let result := w.door.tick w.heights ({ mask := mask.toNat } : Trace) change
    let next := { w with door := result.door, heights := result.heights, removed := result.removed }
    let mut trace := result.state.text
    if result.removed then trace := trace ++ " r"
    for sound in result.sounds do
      let code := match sound with | .close => 0 | .open => 1 | .blazeClose => 2
      trace := trace ++ s!" s {code}"
    return (next,dump next trace)
  | "height",[floor,ceiling] =>
    if !w.started then throw "doors: spawn first"
    let next := { w with heights := ⟨fixed floor,fixed ceiling⟩ }
    return (next,dump next)
  | _,_ => throw "doors: invalid command"

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "usage: doors-probe input.txt")
  let out ← IO.getStdout
  let mut world : World := {}
  for line in (← IO.FS.readFile path).splitOn "\n" do
    if line.trimAscii.isEmpty then continue
    match run world line with
    | .error error => throw (IO.userError error)
    | .ok (next,text) => world := next; out.putStrLn text
