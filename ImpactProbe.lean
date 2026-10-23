import Doom.Impact
open Doom

private def dump (b : Impact.Body) (rng : DoomRandom) : String :=
  s!"{b.motion.x.raw} {b.motion.y.raw} {b.motion.z.raw} {b.motion.momz.raw} {if b.removed then 0 else b.frame} {b.tics} {b.lastlook} {rng.play.toNat} {if b.removed then 1 else 0}"

def main (args : List String) : IO UInt32 := do
  try
    let [input,output] := args | throw (IO.userError "impact-probe INPUT OUTPUT")
    let mut result := ""
    for line in (← IO.FS.readFile input).splitOn "\n" do
      if line.isEmpty then continue
      let values ← (line.splitOn " ").mapM fun s =>
        match s.toInt? with | some n => pure n | none => throw (IO.userError "invalid integer")
      let [blood,damage,melee,index,x,y,z,floor,ceiling,steps] := values
        | throw (IO.userError "expected ten integers")
      if index < 0 || index > 255 || steps < 0 || steps > 64 then throw (IO.userError "invalid bounds")
      let (initial,rng) := Impact.spawn (blood != 0) (Int32.ofInt damage) (melee != 0)
        ⟨Int32.ofInt x⟩ ⟨Int32.ofInt y⟩ ⟨Int32.ofInt z⟩ ⟨Int32.ofInt floor⟩ ⟨Int32.ofInt ceiling⟩
        { play := UInt8.ofNat index.toNat }
      let mut body := initial
      result := result ++ dump body rng ++ "\n"
      for _ in [:steps.toNat] do
        body ← match Impact.tick body with | .ok b => pure b | .error e => throw (IO.userError e)
        result := result ++ dump body rng ++ "\n"
    IO.FS.writeFile output result
    return 0
  catch e =>
    (← IO.getStderr).putStrLn s!"{e}"
    return 1
