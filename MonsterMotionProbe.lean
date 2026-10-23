import Doom.MonsterMotion
import Doom.DamageThrust

open Doom

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "usage: monster-motion-probe commands")
  let stdout ← IO.getStdout
  for line in (← IO.FS.readFile path).splitOn "\n" do
    if line.trimAscii.isEmpty then continue
    let op::fields := line.splitOn " " | throw (IO.userError "empty command")
    let v ← fields.toArray.mapM fun s =>
      match s.toInt? with
      | some i => pure (Int32.ofInt i)
      | none => throw (IO.userError "invalid integer")
    let n (i : Nat) := v[i]!
    let f (i : Nat) : Fixed := ⟨n i⟩
    if op == "thrust" && v.size == 16 then
      let (x,y,rng) := DamageThrust.apply ⟨f 0,f 1,f 2⟩ (n 3) (n 4) (n 5) (f 6) (f 7)
        (if n 15 == 0 then none else some ⟨f 8,f 9,f 10⟩) (n 11 != 0) (n 12 != 0 && n 14 != 0)
        { play := (n 13).toUInt32.toNat.toUInt8 }
      stdout.putStrLn s!"{x.raw.toInt} {y.raw.toInt} {rng.play.toNat}"
    else if op == "motion" && v.size == 14 then
      let mut body : Motion := {
        x := f 0, y := f 1, z := f 2, momx := f 3, momy := f 4, momz := f 5,
        floorz := f 6, ceilingz := f 7, height := f 8, noGravity := n 10 != 0 }
      for _ in [:(n 13).toInt.toNat] do
        let result := MonsterMotion.horizontal (#[] : Array (Fixed × Fixed)) body (n 9 != 0)
          (fun _ _ => f 11) (fun attempts body x y => do
            let accepted := (n 12).toUInt32.toNat &&& (2^attempts.size) != 0
            return (attempts.push (x,y),if accepted then { body with x,y } else body,accepted))
        let .ok (attempts,next) := result | throw (IO.userError "motion fixture failed")
        body := next
        if body.z != body.floorz || body.momz.raw != 0 then body := MonsterMotion.vertical body
        let mut out := s!"{body.x.raw.toInt} {body.y.raw.toInt} {body.z.raw.toInt} {body.momx.raw.toInt} {body.momy.raw.toInt} {body.momz.raw.toInt} {attempts.size}"
        for (x,y) in attempts do out := out ++ s!" {x.raw.toInt} {y.raw.toInt}"
        stdout.putStrLn out
    else throw (IO.userError "invalid monster fixture command")
