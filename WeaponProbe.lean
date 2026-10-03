import Doom.Weapon
import Doom.Random
open Doom
private def dump (c : Weapon.Context) (rng : DoomRandom) (events : Array String) : String :=
  let w := c.state.weapon; let f := c.state.flash
  s!"{c.player.readyWeapon.val} {c.player.pendingWeapon.val} {c.player.ammo[0].toInt} {c.player.ammo[1].toInt} {w.frame} {w.tics.toInt} {w.x.raw.toInt} {w.y.raw.toInt} {f.frame} {f.tics.toInt} {f.x.raw.toInt} {f.y.raw.toInt} {c.state.refire.toInt} {if c.state.attackDown then 1 else 0} {c.state.extraLight.toInt} {rng.play.toNat}|" ++ String.intercalate ";" events.toList ++ "\n"
def main (args : List String) : IO UInt32 := do
  try
    let [input,output] := args | throw (IO.userError "weapon-probe input output")
    let mut c : Weapon.Context := {}
    let mut rng : DoomRandom := {}
    let mut angle : UInt32 := 0
    let mut out := ""
    for line in (← IO.FS.readFile input).splitOn "\n" do
      if line.isEmpty then continue
      let mut events := #[]
      match line.splitOn " " with
      | ["reset",weapon,bullets,shells,owned,seed,a] =>
        let w := weapon.toNat!
        c := { state := { weapon := { frame := Weapon.ready w } }, player := { readyWeapon := ⟨w%9,Nat.mod_lt _ (by decide)⟩, ammo := #v[Int32.ofInt bullets.toInt!,Int32.ofInt shells.toInt!,0,0], weapons := #v[true,true,owned == "1",false,false,false,false,false,false] } }
        rng := { play := seed.toNat!.toUInt8 }; angle := a.toNat!.toUInt32
      | ["tick",attack,choice,bob,draws] =>
        let selection := if choice == "9" then none else some choice.toNat!
        c := Weapon.tick ({ c with attack := attack == "1", bob := ⟨Int32.ofInt bob.toInt!⟩ }.select selection)
        for event in c.events do
          match event with
          | .noise => events := events.push "noise"
          | .pistol _ | .shotgun =>
            let shotgun := event == .shotgun
            let accurate := match event with | .pistol value => value | _ => false
            events := events.push (if shotgun then "sound:shotgn" else "sound:pistol")
            for _ in [:if shotgun then 7 else 1] do
              let (roll,next) := rng.nextPlay; rng := next
              let mut a := angle
              if !accurate then
                let (spread,next) := rng.subPlay; rng := next
                a := a + (Int32.ofInt spread * 262144).toUInt32
              events := events.push s!"shot:{a.toNat}:{5*(roll%3+1)}"
              for _ in [:draws.toNat!] do rng := rng.nextPlay.2
          | .punch =>
            let (roll,next) := rng.nextPlay
            let (spread,next) := next.subPlay; rng := next
            events := events.push s!"shot:{(angle+(Int32.ofInt spread*262144).toUInt32).toNat}:{2*(roll%10+1)}"
            for _ in [:draws.toNat!] do rng := rng.nextPlay.2
        c := { c with time := c.time+1 }
      | ["die"] =>
        c := Weapon.drop { c with dead := true, player := { c.player with health := 0 } }
      | _ => throw (IO.userError s!"bad command {line}")
      out := out ++ dump c rng events
    IO.FS.writeFile output out
    return 0
  catch e =>
    (← IO.getStderr).putStrLn e.toString
    return 1
