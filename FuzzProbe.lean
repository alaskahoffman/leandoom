import Doom.Fuzz

open Doom

private def integer (s : String) : Except String Int := do
  let some n := s.toInt? | throw "fuzz: invalid integer"
  if n < -2147483648 || n > 2147483647 then throw "fuzz: integer outside int32"
  return n

private def bounded (s : String) (bound : Nat) : Except String Nat := do
  let n ← integer s
  if n < 0 || n ≥ bound then throw "fuzz: invalid fixture range"
  return n.toNat

private def initial (seed : Nat) : ByteArray := Id.run do
  let mut bytes := ByteArray.emptyWithCapacity (320*200)
  for y in [:200] do
    for x in [:320] do bytes := bytes.push ((x*17+y*13+y/2*7+seed)%256).toUInt8
  return bytes

private def maps (variant : Nat) : ByteArray := Id.run do
  let mut bytes := ByteArray.emptyWithCapacity (7*256)
  for i in [:7*256] do bytes := bytes.push ((i*73+i/256*11+variant*19)%256).toUInt8
  return bytes

private def pixelHash (pixels : ByteArray) : UInt64 :=
  pixels.data.foldl (fun h b => (h ^^^ b.toUInt64) * 1099511628211) 14695981039346656037

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "usage: fuzz-probe input.txt")
  let mut pixels := initial 0
  let mut colormaps := maps 0
  let mut phase : Fuzz.Phase := 0
  let out ← IO.getStdout
  for line in (← IO.FS.readFile path).splitOn "\n" do
    if line.trimAscii.isEmpty then continue
    let result : Except String (ByteArray × ByteArray × Fuzz.Phase × String) := do
      match (line.splitOn " ").filter (!·.isEmpty) with
      | ["reset", seed, pos, variant] =>
        let seed ← bounded seed 256
        let pos ← bounded pos 50
        let variant ← bounded variant 4
        if h : pos < 50 then return (initial seed, maps variant, ⟨pos,h⟩, "reset")
        else throw "fuzz: invalid phase"
      | ["draw", x, low, high, height] =>
        let x ← bounded x 320
        let height ← bounded height 201
        let result ← Fuzz.checkedColumn pixels colormaps phase x (← integer low) (← integer high) height
        let mut text := s!"{result.phase.val} {result.low} {result.high}"
        for y in [:200] do text := text ++ s!" {result.pixels[y*320+x]!.toNat}"
        return (result.pixels, colormaps, result.phase, text)
      | ["snapshot"] => return (pixels,colormaps,phase,s!"{phase.val} {pixelHash pixels}")
      | _ => throw "fuzz: invalid fixture command"
    match result with
    | .ok (next, tables, pos, text) => pixels := next; colormaps := tables; phase := pos; out.putStrLn text
    | .error error => throw (IO.userError error)
