import Doom.PlayerPhysics

open Doom

private structure Fixture where
  body : Motion := {}
  keyboard : KeyboardState := {}
  view : ViewState := {}

private def integer (text : String) (lo hi : Int) : Except String Int := do
  let some n := text.toInt? | throw s!"invalid integer: {text}"
  if n < lo || n > hi then throw s!"integer outside [{lo}, {hi}]: {text}"
  return n

private def raw (text : String) : Except String Fixed := do
  return ⟨Int32.ofInt (← integer text (-2147483648) 2147483647)⟩

private def command (f s a : String) : Except String Ticcmd := do
  return { forwardMove := Int8.ofInt (← integer f (-128) 127)
           sideMove := Int8.ofInt (← integer s (-128) 127)
           angleTurn := Int16.ofInt (← integer a (-32768) 32767) }

-- Fixture bits are independent of the viewer's legacy SDL key mask.
private def keys (mask : Nat) : MovementKeys :=
  let bit n := mask &&& n != 0
  { forward := bit 1, backward := bit 2, left := bit 4, right := bit 8
    strafeLeft := bit 16, strafeRight := bit 32, strafe := bit 64,
    speed := bit 128, attack := bit 256, use := bit 512 }

private def showBody (body : Motion) (attempts : Array (Fixed × Fixed) := #[]) : String :=
  let fields := s!"{body.x.raw.toInt} {body.y.raw.toInt} {body.momx.raw.toInt} {body.momy.raw.toInt} {body.angle.raw.toNat} {body.frame.val} {attempts.size}"
  attempts.foldl (fun text (x, y) => text ++ s!" {x.raw.toInt} {y.raw.toInt}") fields

private def showCommand (cmd : Ticcmd) (state : KeyboardState) : String :=
  s!"{cmd.forwardMove.toInt} {cmd.sideMove.toInt} {cmd.angleTurn.toInt} {cmd.buttons.toNat} {state.turnHeld.toInt}"

private def showPhysics (body : Motion) (view : ViewState) (landing : Bool := false)
    (attempts : Array (Fixed × Fixed) := #[]) : String :=
  showBody body attempts ++ s!" | {body.z.raw.toInt} {body.momz.raw.toInt} {body.floorz.raw.toInt} {body.ceilingz.raw.toInt} {body.height.raw.toInt} {if body.noGravity then 1 else 0} {view.height.raw.toInt} {view.delta.raw.toInt} {view.z.raw.toInt} {view.bob.raw.toInt} {if landing then 1 else 0}"

private def step (state : Fixture) (parts : List String) : Except String (String × Fixture) := do
  match parts with
  | ["reset"] => return ("reset", {})
  | ["held", n] =>
    let held ← raw n
    return ("held", { state with keyboard := ⟨held.raw⟩ })
  | ["body", x, y, mx, my, angle, z, floor, frame, cheat] =>
    let frame ← integer frame 0 4
    let frame : Fin 5 ← if h : frame.toNat < 5 then pure ⟨frame.toNat, h⟩ else throw "invalid frame"
    let cheat ← integer cheat 0 1
    let body : Motion := {
      x := ← raw x, y := ← raw y, momx := ← raw mx, momy := ← raw my,
      angle := ⟨(← raw angle).raw.toUInt32⟩, z := ← raw z, floorz := ← raw floor,
      frame, noMomentum := cheat == 1 }
    return (showBody body, { state with body })
  | ["key", mask, dup] | ["tick", mask, dup] =>
    let mask ← integer mask 0 1023
    let dup ← integer dup 1 9
    let (cmd, keyboard) := state.keyboard.build (keys mask.toNat) (Int32.ofInt dup)
    if parts.head! == "key" then
      return (showCommand cmd keyboard, { state with keyboard })
    let (body, attempts) := (state.body.movePlayer cmd).advanceUnobstructed cmd
    return (showCommand cmd keyboard ++ " | " ++ showBody body attempts, { state with body, keyboard })
  | ["move", f, s, a] =>
    let body := state.body.movePlayer (← command f s a)
    return (showBody body, { state with body })
  | ["xy", f, s, a] =>
    let (body, attempts) := state.body.advanceUnobstructed (← command f s a)
    return (showBody body attempts, { state with body })
  | ["thrust", a, m] =>
    let body := state.body.thrust ⟨(← raw a).raw.toUInt32⟩ (← raw m)
    return (showBody body, { state with body })
  | ["vertical", momz, ceiling, height, noGravity] =>
    let noGravity ← integer noGravity 0 1
    let body := { state.body with
      momz := ← raw momz
      ceilingz := ← raw ceiling
      height := ← raw height
      noGravity := noGravity == 1 }
    return (showPhysics body state.view, { state with body })
  | ["view", height, delta, z, bob] =>
    let view : ViewState := ⟨← raw height, ← raw delta, ← raw z, ← raw bob⟩
    return (showPhysics state.body view, { state with view })
  | ["space", floor, ceiling] =>
    let body := { state.body with floorz := ← raw floor, ceilingz := ← raw ceiling }
    return (showPhysics body state.view, { state with body })
  | ["zmove"] =>
    let (body, view, landing) := state.body.moveZ state.view
    return (showPhysics body view landing, { state with body, view })
  | ["height", time, ground, live] =>
    let time ← raw time
    let ground ← integer ground 0 1
    let live ← integer live 0 1
    let view := state.view.calcHeight state.body time.raw (ground == 1) (live == 1)
    return (showPhysics state.body view, { state with view })
  | ["physics", mask, dup, time] =>
    let mask ← integer mask 0 1023
    let dup ← integer dup 1 9
    let time ← raw time
    let (cmd, keyboard) := state.keyboard.build (keys mask.toNat) (Int32.ofInt dup)
    let result := state.body.physicsUnobstructed state.view cmd time.raw
    return (showCommand cmd keyboard ++ " | " ++ showPhysics result.body result.view result.landing result.attempts,
            { body := result.body, view := result.view, keyboard })
  | _ => throw s!"invalid motion fixture command: {parts}"

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "usage: motion-probe input.txt")
  let input ← IO.FS.readFile path
  let stdout ← IO.getStdout
  let mut state : Fixture := {}
  let mut lineNumber := 0
  for line in input.splitOn "\n" do
    lineNumber := lineNumber + 1
    if line.trimAscii.isEmpty then continue
    let parts := (line.trimAscii.toString.splitOn " ").filter (!·.isEmpty)
    match step state parts with
    | .ok (result, next) =>
      state := next
      stdout.putStrLn result
    | .error message => throw (IO.userError s!"line {lineNumber}: {message}")
