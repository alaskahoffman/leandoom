import Doom.Imp
import Doom.Projectile
open Doom Doom.Collision

structure Fixture where
  own : SolidThing := {x := ⟨0⟩,y := ⟨0⟩,radius := Fixed.ofInt 20}
  target : SolidThing := {x := Fixed.ofInt 128,y := ⟨0⟩,radius := Fixed.ofInt 16,shootable := true}
  mask : Nat := 255
  sight : Bool := true
  heard : Bool := false
  shadow : Bool := false
  moves : Array Nat := #[]

def hooks : Imp.Hooks Fixture := {
  thing := fun f id => pure (if id == 0 then f.target else f.own),
  sight := fun f _ _ => pure f.sight,
  shadow := fun f _ => f.shadow,
  soundTarget := fun f _ => if f.heard then some 0 else none,
  move := fun f a => do
    if a.movedir == 8 then return (f,a,false)
    let f := { f with moves := f.moves.push a.movedir }
    let ok := f.mask &&& (1 <<< a.movedir) != 0
    let xs : Array Int32 := #[65536,47000,0,-47000,-65536,-47000,0,47000]
    let ys : Array Int32 := #[0,47000,65536,47000,0,-47000,-65536,-47000]
    let f := if ok then { f with own := { f.own with x := f.own.x+⟨8*xs[a.movedir]!⟩,y := f.own.y+⟨8*ys[a.movedir]!⟩ } } else f
    return (f,a,ok) }

private def dump (w : Imp.World Fixture) (answer : Int := -1) : String := Id.run do
  let a := w.actor
  let mut s := s!"{answer} {a.frame} {a.tics} {a.angle.raw.toNat} {if a.target.isSome then 1 else 0} {a.movedir} {a.movecount} {a.reaction} {a.threshold} {a.lastlook} {if a.ambush then 1 else 0} {if a.justHit then 1 else 0} {if a.justAttacked then 1 else 0} {w.rng.play.toNat} {w.host.own.x.raw} {w.host.own.y.raw} /"
  for e in w.events do
    s := s ++ match e with | .sound n => s!" sound {n}" | .melee _ n => s!" damage {n}" | .missile _ => " missile" | .hitscan _ => " hitscan"
  s := s ++ " /"
  for dir in w.host.moves do s := s ++ s!" {dir}"
  return s

def main (args : List String) : IO Unit := do
  let path::options := args | throw (IO.userError "usage: imp-probe commands")
  let zombie := options == ["zombie"]
  let out ← IO.getStdout
  let mut w : Imp.World Fixture := { host := {}, actor := {id := 1}, rng := {} }
  for line in (← IO.FS.readFile path).splitOn "\n" do
    let op::args := (line.splitOn " ").filter (!·.isEmpty) | continue
    let v := (args.map String.toInt!).toArray
    let n := fun i => v[i]!.toNat
    let f := fun i => (⟨Int32.ofInt v[i]!⟩ : Fixed)
    if op == "spawn" then
      let own : SolidThing := {x := f 0,y := f 1,z := f 2,radius := Fixed.ofInt 20}
      let target : SolidThing := {x := f 3,y := f 4,z := f 5,radius := Fixed.ofInt 16}
      let result := do
        let (p,rng) ← Projectile.spawn 1 own target (v[6]! != 0) {play := UInt8.ofNat (n 7)}
        let (p,rng) := if v[8]! == 0 then Projectile.explode p rng else (p,rng)
        let m := p.motion
        pure s!"{m.x.raw} {m.y.raw} {m.z.raw} {m.momx.raw} {m.momy.raw} {m.momz.raw} {m.angle.raw.toNat} {p.frame} {p.tics} {if p.exploding then 1 else 0} {rng.play.toNat}"
      match result with
      | .ok line => out.putStrLn line
      | .error e => throw (IO.userError e)
      continue
    w := { w with events := #[], host := { w.host with moves := #[] } }
    if op == "setup" then
      w := {
        host := {
          own := {x := f 0,y := f 1,radius := Fixed.ofInt 20},
          target := {x := f 2,y := f 3,radius := Fixed.ofInt 16,health := Int32.ofInt v[19]!,shootable := v[19]! > 0},
          mask := n 7, sight := v[8]! != 0, heard := v[9]! != 0, shadow := v[11]! != 0 },
        actor := {
          id := 1, kind := if zombie then 3004 else 3001,
          frame := if zombie then ImpData.POSS_STND else ImpData.TROO_STND, angle := ⟨UInt32.ofInt v[4]!⟩,target := if v[5]! == 0 then none else some 0,
          movedir := n 6, ambush := v[10]! != 0, reaction := Int32.ofInt v[12]!, movecount := Int32.ofInt v[13]!,
          threshold := Int32.ofInt v[14]!,justHit := v[15]! != 0,justAttacked := v[16]! != 0,lastlook := n 17},
        rng := {play := UInt8.ofNat (n 18)} }
      out.putStrLn (dump w)
      continue
    let action : Imp.M Fixture Int := do
      match op with
      | "enter" => Imp.enter hooks 64 (n 0); return -1
      | "tick" => Imp.tick hooks; return -1
      | "newdir" => Imp.newChaseDir hooks; return -1
      | "melee" => return if (← Imp.meleeRange hooks) then 1 else 0
      | "range" => return if (← Imp.missileRange hooks) then 1 else 0
      | _ => throw "invalid imp command"
    match action.run w with
    | .error e => throw (IO.userError e)
    | .ok (answer,next) => w := next; out.putStrLn (dump w answer)
