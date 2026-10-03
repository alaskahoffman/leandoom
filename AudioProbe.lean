import Lean
import Doom.Audio.Opl
import Doom.Audio.Pcm
import Doom.Audio.Mus
import Doom.App
import Doom.Audio.Music
import Doom.Audio.Sfx
open Lean Doom Doom.Audio

def main (args : List String) : IO UInt32 := do
  try
    match args with
    | ["opl",input,output] =>
      let mut chip : Opl.Chip := {}
      let mut pcm := ByteArray.empty
      for line in (← IO.FS.readFile input).splitOn "\n" do
        let p := (line.splitOn " ").filter (!·.isEmpty)
        match p with
        | ["w",r,v] => chip ← checked (chip.write r.toNat! v.toNat!)
        | ["s",n] =>
          for _ in [:n.toNat!] do
            let ((l,r),next) := chip.sample
            chip := next
            pcm := put16 (put16 pcm l) r
        | [] => pure ()
        | _ => throw (IO.userError s!"invalid opl command {line}")
      IO.FS.writeBinFile output pcm
    | ["music",bank,input,count,output] =>
      let bank ← checked (Music.instruments (← IO.FS.readBinFile bank))
      let score ← checked (Score.parse (← IO.FS.readBinFile input))
      let mut player := Music.Player.start bank score
      let mut pcm := ByteArray.empty
      for _ in [:count.toNat!] do
        let (samples,next) ← checked (player.render 1260)
        player := next
        for (l,r) in samples do pcm := put16 (put16 pcm l) r
      IO.FS.writeBinFile output (wav pcm)
    | ["driver",bank,input,output] =>
      let bank ← checked (Music.instruments (← IO.FS.readBinFile bank))
      let mut driver : Music.Driver := { bank }
      let mut out := ""
      for line in (← IO.FS.readFile input).splitOn "\n" do
        if line.isEmpty then continue
        let [status,a,b] := line.splitOn " " | throw (IO.userError "invalid driver event")
        driver ← checked ({ driver with writes := #[] }.handle ⟨0,status.toNat!,a.toNat!,b.toNat!⟩)
        out := out ++ String.intercalate " " (driver.writes.toList.map fun (r,v) => s!"{r}:{v}") ++ "\n"
      IO.FS.writeFile output out
    | ["channels",input,output] =>
      let bank := Audio.Tables.sfx.map fun (name,_) => (name,({ rate := 11025, data := ByteArray.mk (Array.replicate 256 128) } : Sample))
      let mut state : Sfx.State := { bank }
      let mut rng : DoomRandom := {}
      let mut out := ""
      for line in (← IO.FS.readFile input).splitOn "\n" do
        if line.isEmpty then continue
        match line.splitOn " " with
        | ["reset",seed,volume] =>
          state := { bank, volume := volume.toNat! }
          rng := { misc := seed.toNat!.toUInt8 }
        | ["start",name,id,x,y,angle] =>
          let origin := if id.toInt! < 0 then none else some (Sfx.Origin.actor id.toNat!)
          (state,rng) ← checked (state.start ⟨⟨⟨0⟩,⟨0⟩⟩,⟨angle.toNat!.toUInt32⟩⟩
            ⟨name,origin,⟨⟨Int32.ofInt x.toInt!⟩,⟨Int32.ofInt y.toInt!⟩⟩⟩ rng)
        | _ => throw (IO.userError "invalid channel command")
        out := out ++ s!"{rng.misc.toNat}|" ++ String.intercalate ";" (state.channels.toList.map fun c =>
          match c with
          | none => "-"
          | some c =>
            let id : Int := match c.origin with | some (.actor n) => Int.ofNat n | _ => -1
            s!"{c.name}:{id}:{c.pitch}:{c.params.volume}:{c.params.separation}") ++ "\n"
      IO.FS.writeFile output out
    | ["spatial",input,output] =>
      let mut out := ""
      for line in (← IO.FS.readFile input).splitOn "\n" do
        if line.isEmpty then continue
        let [x,y,angle,tx,ty,volume,map8] := line.splitOn " " | throw (IO.userError "invalid spatial case")
        let result ← checked (Sfx.adjust ⟨⟨⟨Int32.ofInt x.toInt!⟩,⟨Int32.ofInt y.toInt!⟩⟩,⟨UInt32.ofNat angle.toNat!⟩⟩
          ⟨⟨Int32.ofInt tx.toInt!⟩,⟨Int32.ofInt ty.toInt!⟩⟩ volume.toNat! (map8 == "1"))
        out := out ++ (result.map (fun p => s!"{p.volume} {p.separation}") |>.getD "none") ++ "\n"
      IO.FS.writeFile output out
    | ["mus",input,output] =>
      let score ← checked (Score.parse (← IO.FS.readBinFile input))
      IO.FS.writeFile output (Json.mkObj [("duration",toJson score.duration),("events",toJson (score.events.map fun e => #[e.tick,e.status,e.a,e.b]))]).compress
    | ["dmx",input,output] =>
      let sample ← checked (Sample.parse (← IO.FS.readBinFile input))
      IO.FS.writeBinFile output sample.data
      IO.println sample.rate
    | _ => throw (IO.userError "audio-probe: opl/mus/dmx input output")
    return 0
  catch e =>
    (← IO.getStderr).putStrLn e.toString
    return 1
