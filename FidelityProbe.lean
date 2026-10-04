import Doom.Bsp
import Doom.Random
import Doom.Angles

open Doom

private def fixed (text : String) : Except String Fixed := do
  let some n := text.toInt? | throw s!"invalid signed integer: {text}"
  if n < -2147483648 || n > 2147483647 then throw "raw fixed value exceeds int32"
  return ⟨Int32.ofInt n⟩

private def step (rng : DoomRandom) (line : String) : Except String (String × DoomRandom) := do
  let parts := (line.trimAscii.toString.splitOn " ").filter (!·.isEmpty)
  match parts with
  | ["mul", a, b] => return (toString ((← fixed a) * (← fixed b)).raw.toInt, rng)
  | ["add", a, b] => return (toString ((← fixed a) + (← fixed b)).raw.toInt, rng)
  | ["sub", a, b] => return (toString ((← fixed a) - (← fixed b)).raw.toInt, rng)
  | ["div", a, b] =>
    match Fixed.divChecked (← fixed a) (← fixed b) with
    | .ok value => return (toString value.raw.toInt, rng)
    | .error .divideByZero => return ("divide-by-zero", rng)
    | .error .quotientOverflow => return ("quotient-overflow", rng)
  | ["slope", a, b] =>
    return (toString (slopeDiv (← fixed a).raw.toUInt32 (← fixed b).raw.toUInt32).val, rng)
  | ["angle", x, y, ox, oy] =>
    return (toString (Angle.between (← fixed ox) (← fixed oy) (← fixed x) (← fixed y)).raw.toNat, rng)
  | ["fine", a] =>
    let angle : Angle := ⟨(← fixed a).raw.toUInt32⟩
    return (s!"{angle.fineSine.raw.toInt} {angle.fineCosine.raw.toInt}", rng)
  | ["sine", index] =>
    let some n := index.toNat? | throw "invalid table index"
    if h : n < 10240 then return (toString (Tables.fineSine.get ⟨n, h⟩).toInt, rng)
    else throw "sine index out of range"
  | ["tangent", index] =>
    let some n := index.toNat? | throw "invalid table index"
    if h : n < 4096 then return (toString (Tables.fineTangent.get ⟨n, h⟩).toInt, rng)
    else throw "tangent index out of range"
  | ["atan", index] =>
    let some n := index.toNat? | throw "invalid table index"
    if h : n < 2049 then return (toString (Tables.tanToAngle.get ⟨n, h⟩).toNat, rng)
    else throw "arctangent index out of range"
  | ["side", x, y, ox, oy, dx, dy] =>
    let side := pointOnSide (← fixed x) (← fixed y) (← fixed ox) (← fixed oy) (← fixed dx) (← fixed dy)
    return (if side then "1" else "0", rng)
  | ["node", x, y, ox, oy, dx, dy] =>
    let values ← [ox, oy, dx, dy].mapM fun text => do
      let some n := text.toInt? | throw "invalid map coordinate"
      if n < -32768 || n > 32767 then throw "map coordinate exceeds int16"
      pure n
    let [ox, oy, dx, dy] := values | throw "invalid node"
    let node : Node := ⟨⟨ox, oy⟩, ⟨dx, dy⟩, default, default, .subsector 0, .subsector 1⟩
    return (if node.onLeft (← fixed x) (← fixed y) then "1" else "0", rng)
  | [op] =>
    let (value, rng) ← match op with
      | "play" => pure (Int.ofNat rng.nextPlay.1, rng.nextPlay.2)
      | "misc" => pure (Int.ofNat rng.nextMisc.1, rng.nextMisc.2)
      | "subplay" => pure rng.subPlay
      | "clear" => pure (0, rng.clear)
      | _ => throw s!"unknown operation: {op}"
    return (s!"{value} {rng.play.toNat} {rng.misc.toNat}", rng)
  | _ => throw s!"invalid probe command: {line}"

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "usage: fidelity-probe input.txt")
  let input ← IO.FS.readFile path
  let stdout ← IO.getStdout
  let mut rng : DoomRandom := {}
  let mut lineNumber := 0
  for line in input.splitOn "\n" do
    lineNumber := lineNumber + 1
    if line.trimAscii.isEmpty then continue
    match step rng line with
    | .ok (result, next) =>
      rng := next
      stdout.putStrLn result
    | .error message => throw (IO.userError s!"line {lineNumber}: {message}")
