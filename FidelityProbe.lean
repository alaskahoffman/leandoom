import Doom.PlayerDeath
import Doom.PlayerAnim
import Doom.PlayerReaction
import Doom.Bsp
import Doom.Random
import Doom.Angles
import Doom.RenderSky
import Doom.RenderProjection
import Doom.RenderSprite
import Doom.SurfaceAnimation

open Doom

private def fixed (text : String) : Except String Fixed := do
  let some n := text.toInt? | throw s!"invalid signed integer: {text}"
  if n < -2147483648 || n > 2147483647 then throw "raw fixed value exceeds int32"
  return ⟨Int32.ofInt n⟩

private def step (rng : DoomRandom) (line : String) : Except String (String × DoomRandom) := do
  let parts := (line.trimAscii.toString.splitOn " ").filter (!·.isEmpty)
  match parts with
  | ["player-animation", frame, tics, forward, side] => do
    let some frame := frame.toNat? | throw "invalid state index"
    if frame >= 65536 then throw "state index exceeds relation bound"
    let some f := forward.toInt? | throw "invalid forward"
    let some c := side.toInt? | throw "invalid side"
    if f < -128 || f > 127 || c < -128 || c > 127 then throw "command exceeds int8"
    let state : PlayerAnim.State := ⟨frame,(← fixed tics).raw⟩
    let result := state.startWalking { forwardMove := Int8.ofInt f, sideMove := Int8.ofInt c }
    return (s!"{result.frame} {result.tics.toInt}",rng)
  | ["player-preparation", timer, angle, turn, z, floor, ceiling, forward, side,
      mx, my, frame, tics, height, delta, time, cached, noMomentum, live] => do
    let some t := turn.toInt? | throw "invalid turn"
    let some f := forward.toInt? | throw "invalid forward"
    let some c := side.toInt? | throw "invalid side"
    if t < -32768 || t > 32767 then throw "turn exceeds int16"
    if f < -128 || f > 127 || c < -128 || c > 127 then throw "command exceeds int8"
    let some frame := frame.toNat? | throw "invalid state index"
    if frame >= 65536 then throw "state index exceeds relation bound"
    let body : Motion := {
      angle := ⟨(← fixed angle).raw.toUInt32⟩, z := ← fixed z, floorz := ← fixed floor,
      ceilingz := ← fixed ceiling, momx := ← fixed mx, momy := ← fixed my,
      noMomentum := noMomentum != "0" }
    let timer := (← fixed timer).raw
    let cmd : Ticcmd := { angleTurn := Int16.ofInt t, forwardMove := Int8.ofInt f, sideMove := Int8.ofInt c }
    let ground := if timer = 0 then body.z.raw ≤ body.floorz.raw else cached != "0"
    let moved := PlayerReaction.move body timer cmd
    let anim := PlayerReaction.animate ⟨frame,(← fixed tics).raw⟩ timer cmd
    let view := ViewState.calcHeight { height := ← fixed height, delta := ← fixed delta }
      moved (← fixed time).raw ground (live != "0")
    return (s!"{moved.angle.raw.toNat} {moved.momx.raw.toInt} {moved.momy.raw.toInt} {anim.frame} {anim.tics.toInt} {(PlayerReaction.remaining timer).toInt} {view.height.raw.toInt} {view.delta.raw.toInt} {view.z.raw.toInt} {view.bob.raw.toInt} {if ground then 1 else 0}",rng)
  | ["player-reaction", timer, angle, turn, z, floor, forward, side, mx, my, frame, tics] => do
    let some t := turn.toInt? | throw "invalid turn"
    let some f := forward.toInt? | throw "invalid forward"
    let some c := side.toInt? | throw "invalid side"
    if t < -32768 || t > 32767 then throw "turn exceeds int16"
    if f < -128 || f > 127 || c < -128 || c > 127 then throw "command exceeds int8"
    let body : Motion := {
      angle := ⟨(← fixed angle).raw.toUInt32⟩,
      z := ← fixed z, floorz := ← fixed floor, momx := ← fixed mx, momy := ← fixed my }
    let timer := (← fixed timer).raw
    let result := PlayerReaction.move body timer {
      angleTurn := Int16.ofInt t, forwardMove := Int8.ofInt f, sideMove := Int8.ofInt c }
    let some frame := frame.toNat? | throw "invalid state index"
    if frame >= 65536 then throw "state index exceeds relation bound"
    let anim : PlayerAnim.State := ⟨frame,(← fixed tics).raw⟩
    let anim := PlayerReaction.animate anim timer { forwardMove := Int8.ofInt f, sideMove := Int8.ofInt c }
    return (s!"{result.angle.raw.toNat} {result.momx.raw.toInt} {result.momy.raw.toInt} {anim.frame} {anim.tics.toInt} {(PlayerReaction.remaining timer).toInt}", rng)
  | ["player-step", angle, turn, z, floor, forward, side, mx, my, frame, tics] => do
    let some t := turn.toInt? | throw "invalid turn"
    let some f := forward.toInt? | throw "invalid forward"
    let some c := side.toInt? | throw "invalid side"
    if t < -32768 || t > 32767 then throw "turn exceeds int16"
    if f < -128 || f > 127 || c < -128 || c > 127 then throw "command exceeds int8"
    let body : Motion := {
      angle := ⟨(← fixed angle).raw.toUInt32⟩,
      z := ← fixed z, floorz := ← fixed floor, momx := ← fixed mx, momy := ← fixed my }
    let result := body.movePlayer {
      angleTurn := Int16.ofInt t, forwardMove := Int8.ofInt f, sideMove := Int8.ofInt c }
    let some frame := frame.toNat? | throw "invalid state index"
    if frame >= 65536 then throw "state index exceeds relation bound"
    let anim : PlayerAnim.State := ⟨frame,(← fixed tics).raw⟩
    let anim := anim.startWalking { forwardMove := Int8.ofInt f, sideMove := Int8.ofInt c }
    return (s!"{result.angle.raw.toNat} {result.momx.raw.toInt} {result.momy.raw.toInt} {anim.frame} {anim.tics.toInt}", rng)
  | ["move-player", angle, turn, z, floor, forward, side, mx, my] => do
    let some t := turn.toInt? | throw "invalid turn"
    let some f := forward.toInt? | throw "invalid forward"
    let some c := side.toInt? | throw "invalid side"
    if t < -32768 || t > 32767 then throw "turn exceeds int16"
    if f < -128 || f > 127 || c < -128 || c > 127 then throw "command exceeds int8"
    let body : Motion := {
      angle := ⟨(← fixed angle).raw.toUInt32⟩,
      z := ← fixed z, floorz := ← fixed floor, momx := ← fixed mx, momy := ← fixed my }
    let result := body.movePlayer {
      angleTurn := Int16.ofInt t, forwardMove := Int8.ofInt f, sideMove := Int8.ofInt c }
    return (s!"{result.angle.raw.toNat} {result.momx.raw.toInt} {result.momy.raw.toInt}", rng)
  | ["move-front", angle, turn, z, floor, forward, side, mx, my] => do
    let some t := turn.toInt? | throw "invalid turn"
    let some f := forward.toInt? | throw "invalid forward"
    let some c := side.toInt? | throw "invalid side"
    if t < -32768 || t > 32767 then throw "turn exceeds int16"
    if f < -128 || f > 127 || c < -128 || c > 127 then throw "command exceeds int8"
    let body : Motion := {
      angle := ⟨(← fixed angle).raw.toUInt32⟩,
      z := ← fixed z, floorz := ← fixed floor, momx := ← fixed mx, momy := ← fixed my }
    -- Execute the real player update with side input suppressed: its angle and
    -- momentum equal the state immediately before the original side thrust.
    let result := body.movePlayer { angleTurn := Int16.ofInt t, forwardMove := Int8.ofInt f }
    let sideBody : Motion := { z := body.z, floorz := body.floorz }
    let sideResult := sideBody.movePlayer { sideMove := Int8.ofInt c }
    let takeSide := sideResult.momx.raw != 0 || sideResult.momy.raw != 0
    return (s!"{result.angle.raw.toNat} {result.momx.raw.toInt} {result.momy.raw.toInt} {if takeSide then 1 else 0}", rng)
  | ["move-guards", z, floor, forward, side] => do
    let some f := forward.toInt? | throw "invalid forward command"
    let some t := side.toInt? | throw "invalid side command"
    if f < -128 || f > 127 || t < -128 || t > 127 then throw "command exceeds int8"
    let body : Motion := { z := ← fixed z, floorz := ← fixed floor }
    let forwardBody := body.movePlayer { forwardMove := Int8.ofInt f }
    let sideBody := body.movePlayer { sideMove := Int8.ofInt t }
    let moved (b : Motion) := if b.momx.raw != 0 || b.momy.raw != 0 then 1 else 0
    return (s!"{if body.onGround then 1 else 0} {moved forwardBody} {moved sideBody}", rng)
  | ["thrust", angle, move, mx, my] => do
    let body : Motion := { momx := ← fixed mx, momy := ← fixed my }
    let result := body.thrust ⟨(← fixed angle).raw.toUInt32⟩ (← fixed move)
    return (s!"{result.momx.raw.toInt} {result.momy.raw.toInt}", rng)
  | ["turn", angle, amount] => do
    let some amount := amount.toInt? | throw "invalid turn command"
    if amount < -32768 || amount > 32767 then throw "turn command exceeds int16"
    let body : Motion := { angle := ⟨(← fixed angle).raw.toUInt32⟩ }
    return (toString (body.turn (Int16.ofInt amount)).angle.raw.toNat, rng)
  | ["render-tangent", index] => do
    let some i := index.toNat? | throw "invalid renderer tangent index"
    if i >= 8192 then throw "renderer tangent index out of range"
    return (s!"{RenderProjection.tangent (UInt32.ofNat i <<< 19)}", rng)
  | ["calc-height", height, delta, z, ceiling, mx, my, time, ground, noMomentum, live] => do
    let body : Motion := {
      z := ← fixed z, ceilingz := ← fixed ceiling,
      momx := ← fixed mx, momy := ← fixed my, noMomentum := noMomentum != "0" }
    let view := ViewState.calcHeight { height := ← fixed height, delta := ← fixed delta }
      body (← fixed time).raw (ground != "0") (live != "0")
    return (s!"{view.height.raw.toInt} {view.delta.raw.toInt} {view.z.raw.toInt} {view.bob.raw.toInt}",rng)
  | ["deathview", a, target, damage, height, delta, z, floor, ceiling, mx, my, time] => do
    let body : Motion := {
      angle := ⟨(← fixed a).raw.toUInt32⟩,
      z := ← fixed z, floorz := ← fixed floor, ceilingz := ← fixed ceiling,
      momx := ← fixed mx, momy := ← fixed my }
    let attacker ← if target == "none" then pure none else pure (some (← fixed target).raw.toUInt32)
    let (angle,count) := PlayerDeath.look body.angle.raw attacker (← fixed damage).raw
    let view := PlayerDeath.view { height := ← fixed height, delta := ← fixed delta } body (← fixed time).raw
    return (s!"{angle.toNat} {count.toInt} {view.height.raw.toInt} {view.delta.raw.toInt} {view.z.raw.toInt} {view.bob.raw.toInt}",rng)
  | ["anim", ticks, base, count, index] => do
    let some ticks := ticks.toNat? | throw "invalid ticks"
    let some base := base.toNat? | throw "invalid base"
    let some count := count.toNat? | throw "invalid count"
    let some index := index.toNat? | throw "invalid index"
    return (toString (SurfaceAnimation.frame ticks base count index),rng)
  | ["sprite", view, dx, dy, z, vz, width, left, top, flip, facing] => do
    let dx ← fixed dx
    let dy ← fixed dy
    let some width := width.toInt? | throw "invalid width"
    let some left := left.toInt? | throw "invalid left"
    let some top := top.toInt? | throw "invalid top"
    let some p := RenderSprite.project (← fixed view).raw.toUInt32 dx.raw dy.raw (← fixed z).raw (← fixed vz).raw width left top (flip == "1") | return ("hidden",rng)
    let rot := RenderSprite.direction dx dy (← fixed facing).raw.toUInt32
    return (s!"{rot} {p.scale.toInt} {p.first} {p.stop} {p.frac.toInt} {p.step.toInt} {p.texturemid.toInt}",rng)
  | ["post", scale, mid, height, top, count, ct, cb] => do
    let some height := height.toNat? | throw "invalid height"
    let some top := top.toNat? | throw "invalid top"
    let some count := count.toNat? | throw "invalid count"
    let some ct := ct.toInt? | throw "invalid top clip"
    let some cb := cb.toInt? | throw "invalid bottom clip"
    let mid := (← fixed mid).raw
    let (first,last) := RenderSprite.postBounds (← fixed scale).raw mid height top count
    let first := max first (ct+1)
    let last := min last (cb-1)
    return (if first > last then "hidden" else s!"{first} {last} {(mid-Int32.ofNat (top*65536)).toInt}",rng)
  | ["span", xf, yf, xs, ys, count] => do
    let some count := count.toNat? | throw "invalid count"
    let mut position := RenderProjection.packed (← fixed xf).raw (← fixed yf).raw
    let step := RenderProjection.packed (← fixed xs).raw (← fixed ys).raw
    let mut values := #[]
    for _ in [:min count 320] do
      values := values.push (toString (RenderProjection.flatSpot position))
      position := position + step
    return (String.intercalate " " values.toList,rng)
  | ["project", view, ax, ay, bx, byText, angle, offset] => do
    let view := (← fixed view).raw.toUInt32
    let ax ← fixed ax
    let ay ← fixed ay
    let bx ← fixed bx
    let byValue ← fixed byText
    let angle := (← fixed angle).raw.toUInt32
    let offset := (← fixed offset).raw
    let a := (Angle.fromVector ax ay).raw
    let b := (Angle.fromVector bx byValue).raw
    let some (first,stop) := RenderProjection.bounds view a b | return ("hidden",rng)
    let w := RenderProjection.wall view a angle ax.raw ay.raw offset
    let s1 := RenderProjection.scale view w.normal w.distance first
    let s2 := RenderProjection.scale view w.normal w.distance (stop-1)
    return (s!"{first} {stop} {w.distance.toInt} {w.offset.toInt} {w.centerAngle} {s1.toInt} {s2.toInt} {(w.column first).toInt} {(w.column ((first+stop-1)/2)).toInt} {(w.column (stop-1)).toInt}",rng)
  | ["plane", view, vx, vy, height, vh, y, x] => do
    let some vh := vh.toNat? | throw "invalid height"
    let some y := y.toNat? | throw "invalid row"
    let some x := x.toNat? | throw "invalid column"
    let p := RenderProjection.planeSpan (← fixed view).raw.toUInt32 (← fixed vx).raw (← fixed vy).raw (← fixed height).raw vh y x
    return (s!"{p.distance.toInt} {p.xfrac.toInt} {p.yfrac.toInt} {p.xstep.toInt} {p.ystep.toInt}",rng)
  | ["sky", angle, x, y, height] =>
    let some x := x.toNat? | throw "invalid sky column"
    let some y := y.toNat? | throw "invalid sky row"
    let some height := height.toNat? | throw "invalid view height"
    return (s!"{RenderSky.screenAngles[min x 320]!} {RenderSky.column (← fixed angle).raw.toUInt32 x} {RenderSky.row height y}",rng)
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
