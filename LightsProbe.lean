import Doom.SectorLights
open Doom

private def emptyMap : Map := ⟨"LIGHTS",#[],#[],#[],#[],#[],#[],#[],#[],ByteArray.empty,default⟩
private structure World where
  map : Map := emptyMap
  rng : DoomRandom := {}
  lights : Array SectorLights.Thinker := #[]
  started : Bool := false
  busy : Array Nat := #[]

private def dump (w : World) : String := Id.run do
  let mut out := s!"{w.rng.play.toNat} {w.rng.misc.toNat}"
  for s in w.map.sectors do out := out ++ s!" | {s.light} {s.special}"
  out := out ++ " / "
  for t in w.lights do
    let kind := match t.kind with | .fire => 0 | .flash => 1 | .strobe => 2 | .glow => 3
    out := out ++ s!"| {t.sector} {kind} {t.count} {t.minimum} {t.maximum} {t.dark} {t.direction} "
  return out

private def bounded (s : String) (lo hi : Int) : Except String Int := do
  let some n := s.toInt? | throw "lights: invalid integer"
  if n < lo || n > hi then throw "lights: input out of range"
  return n

private def run (w : World) (line : String) : Except String (World × String) := do
  match (line.splitOn " ").filter (!·.isEmpty) with
  | ["reset",play,misc] =>
    let play ← bounded play 0 255; let misc ← bounded misc 0 255
    return ({ rng := ⟨play.toNat.toUInt8,misc.toNat.toUInt8⟩ },"reset")
  | ["sector",level,special] =>
    if w.started || w.map.sectors.size ≥ 32 then throw "lights: invalid sector setup"
    let light ← bounded level (-32768) 32767
    let special ← bounded special 0 32767
    let s : Sector := ⟨0,128,"F","C",light,special.toNat,0⟩
    return ({ w with map := { w.map with sectors := w.map.sectors.push s } },"sector")
  | ["line",flags,front,back] =>
    if w.started || w.map.lines.size ≥ 64 then throw "lights: invalid line setup"
    let flags ← bounded flags 0 65535
    let front ← bounded front 0 (Int.ofNat w.map.sectors.size-1)
    let back ← bounded back (-1) (Int.ofNat w.map.sectors.size-1)
    if flags.toNat &&& 4 != 0 && back == -1 then throw "lights: two-sided line missing back sector"
    let side (sector : Nat) : Sidedef := ⟨0,0,"-","-","-",sector⟩
    let sides := w.map.sides.push (side front.toNat)
    let sides := if back < 0 then sides else sides.push (side back.toNat)
    let l : Linedef := ⟨0,0,flags.toNat,0,0,w.map.sides.size,if back < 0 then 65535 else w.map.sides.size+1⟩
    return ({ w with map := { w.map with sides, lines := w.map.lines.push l } },"line")
  | ["tagsector",index,tag,busy] =>
    let index ← bounded index 0 (Int.ofNat w.map.sectors.size-1)
    let tag ← bounded tag 0 65535
    let busy ← bounded busy 0 1
    let sector := { w.map.sectors[index.toNat]! with tag := tag.toNat }
    let occupied := w.busy.filter (· != index.toNat)
    let map := { w.map with sectors := w.map.sectors.set! index.toNat sector }
    let busy := if busy == 0 then occupied else occupied.push index.toNat
    return ({ w with map, busy },"tagsector")
  | ["trigger",index,special,tag] =>
    let index ← bounded index 0 (Int.ofNat w.map.lines.size-1)
    let special ← bounded special 0 32767
    let tag ← bounded tag 0 65535
    let line := { w.map.lines[index.toNat]! with special := special.toNat, tag := tag.toNat }
    return ({ w with map := { w.map with lines := w.map.lines.set! index.toNat line } },"trigger")
  | ["cross",index,player,side] =>
    let index ← bounded index 0 (Int.ofNat w.map.lines.size-1)
    let player ← bounded player 0 1
    let _ ← bounded side 0 1
    let world : SectorLights.World := { map := w.map, rng := w.rng, thinkers := w.lights, busy := w.busy }
    let world := world.cross index.toNat (player != 0)
    let next := { w with map := world.map, rng := world.rng, lights := world.thinkers }
    return (next,s!"special {next.map.lines[index.toNat]!.special} " ++ dump next)
  | ["spawn"] =>
    if w.started then throw "lights: already spawned"
    let (map,lights,rng) := SectorLights.spawnMap w.map w.rng
    let next := { w with map,lights,rng,started := true }
    return (next,dump next)
  | ["tick"] =>
    if !w.started then throw "lights: spawn first"
    let (map,lights,rng) := SectorLights.tickMap w.map w.lights w.rng
    let next := { w with map,lights,rng }
    return (next,dump next)
  | ["set",index,value] =>
    let index ← bounded index 0 (Int.ofNat w.map.sectors.size-1)
    let light ← bounded value (-32768) 32767
    let sector := { w.map.sectors[index.toNat]! with light }
    let next := { w with map := { w.map with sectors := w.map.sectors.set! index.toNat sector } }
    return (next,dump next)
  | [op,count] =>
    if op != "play" && op != "misc" then throw "lights: invalid RNG command"
    let count ← bounded count 0 1024
    let rng := (List.range count.toNat).foldl (fun rng _ => if op == "play" then rng.nextPlay.2 else rng.nextMisc.2) w.rng
    let next := { w with rng }
    return (next,dump next)
  | _ => throw "lights: invalid command"

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "usage: lights-probe input.txt")
  let out ← IO.getStdout
  let mut state : World := {}
  for line in (← IO.FS.readFile path).splitOn "\n" do
    if line.trimAscii.isEmpty then continue
    match run state line with
    | .error error => throw (IO.userError error)
    | .ok (next,text) => state := next; out.putStrLn text
