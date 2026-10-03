import Doom.FloorMover
open Doom Doom.FloorMover

private def emptyMap : Map := ⟨"MOVERS",#[],#[],#[],#[],#[],#[],#[],#[],ByteArray.empty,default⟩
private structure World where
  map : Map := emptyMap
  movers : Array Thinker := #[]
  busy : Array Nat := #[]
  solo : Thinker := {}
  heights : Plane.Heights := {}
  removed : Bool := false

private def fixed (n : Int) : Fixed := ⟨Int32.ofInt n⟩
private def status (n : Int) : Except String Status :=
  match n with | 0 => .ok .up | 1 => .ok .down | 2 => .ok .waiting | 3 => .ok .stasis | _ => .error "movers: invalid status"
private def code : Status → Nat | .up => 0 | .down => 1 | .waiting => 2 | .stasis => 3
private def soundCode : Sound → Nat | .move => 0 | .stop => 1 | .start => 2
private structure Trace where
  text : String := ""
  calls : Nat := 0
  mask : Nat := 0
private def change (h : Plane.Heights) (_ : Bool) (s : Trace) : Bool × Trace :=
  (s.mask / 2^s.calls % 2 != 0, { s with calls := s.calls+1, text := s.text ++ s!" c {h.floor.raw.toInt} {h.ceiling.raw.toInt}" })
private def events (trace : String) (es : Array Event) : String :=
  es.foldl (fun s e => s ++ match e with | .remove => " r" | .sound sound => s!" s {soundCode sound}") trace
private def soloDump (w : World) (trace : String) : String :=
  let base := s!"{w.heights.floor.raw.toInt} {w.heights.ceiling.raw.toInt}"
  if w.solo.kind == .turboLower then s!"f {base} {if w.removed then 1 else 0} /{trace}"
  else s!"p {base} {code w.solo.status} {w.solo.count} {if w.removed then 1 else 0} /{trace}"
private def soloTick (w : World) (time mask : Int) : World × String := Id.run do
  if w.removed then return (w,soloDump w "")
  let r := w.solo.tick w.heights (Int32.ofInt time) ({ mask := mask.toNat } : Trace) change
  let w := { w with solo := r.thinker, heights := r.heights, removed := r.removed }
  return (w,soloDump w (events r.state.text r.events))
private def dump (w : World) (trace : String) : String := Id.run do
  let mut text := s!"{w.map.sectors.size}"
  for i in [:w.map.sectors.size] do
    text := text ++ s!" {(Fixed.ofInt w.map.sectors[i]!.floor).raw.toInt} {if w.busy.contains i || w.movers.any (·.sector == i) then 1 else 0}"
  text := text ++ s!" | {w.map.lines.size}"
  for line in w.map.lines do text := text ++ s!" {line.special}"
  text := text ++ s!" | {w.movers.size}"
  for m in w.movers do
    text := text ++ s!" {m.sector} {if m.kind == .turboLower then 0 else 1} {m.low.raw.toInt} {m.high.raw.toInt} {m.speed.raw.toInt} {code m.status} {m.count} {m.wait}"
  return text ++ " /" ++ trace
private def integer (s : String) : Except String Int := do
  let some n := s.toInt? | throw "movers: invalid integer"
  if n < -2147483648 || n > 2147483647 then throw "movers: outside int32"
  return n
private def run (w : World) (line : String) : Except String (World × String) := do
  let op :: args := (line.splitOn " ").filter (!·.isEmpty) | throw "movers: empty command"
  let args ← args.mapM integer
  match op,args with
  | "floor",[floor,ceiling,dest,speed,time,mask] =>
    if speed < 0 || mask < 0 || mask > 3 then throw "movers: invalid floor input"
    return soloTick { w with solo := { low := fixed dest, speed := fixed speed }, heights := ⟨fixed floor,fixed ceiling⟩, removed := false } time mask
  | "lift",[floor,ceiling,low,high,speed,st,count,wait,time,mask] =>
    if speed < 0 || mask < 0 || mask > 3 then throw "movers: invalid lift input"
    let solo : Thinker := { kind := .lift, low := fixed low, high := fixed high, speed := fixed speed, status := ← status st, count := Int32.ofInt count, wait := Int32.ofInt wait }
    return soloTick { w with solo, heights := ⟨fixed floor,fixed ceiling⟩, removed := false } time mask
  | "lifttick",[time,mask] =>
    if w.solo.kind != .lift || mask < 0 || mask > 3 then throw "movers: invalid lift tick"
    return soloTick w time mask
  | "reset",[] => return ({},"reset")
  | "sector",[floor,ceiling,tag,occupied] =>
    if tag < 0 || tag > 65535 || (occupied != 0 && occupied != 1) then throw "movers: invalid sector"
    let sector : Sector := ⟨floor,ceiling,"F","C",160,0,tag.toNat⟩
    return ({ w with map := { w.map with sectors := w.map.sectors.push sector }, busy := if occupied == 0 then w.busy else w.busy.push w.map.sectors.size },"sector")
  | "line",[flags,front,back,special,tag] =>
    if front < 0 || front ≥ w.map.sectors.size || back < -1 || back ≥ w.map.sectors.size || flags < 0 || special < 0 || special > 32767 || tag < 0 || tag > 65535 then throw "movers: invalid line"
    if flags.toNat &&& 4 != 0 && back == -1 then throw "movers: missing back sector"
    let side (n : Nat) : Sidedef := ⟨0,0,"-","-","-",n⟩
    let sides := w.map.sides.push (side front.toNat)
    let sides := if back < 0 then sides else sides.push (side back.toNat)
    let line : Linedef := ⟨0,0,flags.toNat,special.toNat,tag.toNat,w.map.sides.size,if back < 0 then 65535 else w.map.sides.size+1⟩
    return ({ w with map := { w.map with sides, lines := w.map.lines.push line } },"line")
  | "cross",[index,player,projectile,side] =>
    if index < 0 || (player != 0 && player != 1) || (projectile != 0 && projectile != 1) || (side != 0 && side != 1) then throw "movers: invalid crossing"
    let r ← FloorMover.cross w.map w.movers w.busy index.toNat (player != 0) (projectile != 0)
    let w := { w with map := r.map, movers := r.thinkers }
    let trace := r.sounds.foldl (fun s (_,sound) => s ++ s!" s {soundCode sound}") ""
    return (w,dump w trace)
  | "worldtick",[time] =>
    let mut w := w
    let mut movers := #[]
    let mut trace := ""
    for m in w.movers do
      let sector := w.map.sectors[m.sector]!
      let r := m.tick ⟨Fixed.ofInt sector.floor,Fixed.ofInt sector.ceiling⟩ (Int32.ofInt time) ({} : Trace) change
      trace := trace ++ events r.state.text r.events
      let sector := { sector with floor := r.heights.floor.raw.toInt / 65536 }
      w := { w with map := { w.map with sectors := w.map.sectors.set! m.sector sector } }
      if !r.removed then movers := movers.push r.thinker
    w := { w with movers }
    return (w,dump w trace)
  | _,_ => throw "movers: invalid command"

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "usage: movers-probe input.txt")
  let out ← IO.getStdout
  let mut world : World := {}
  for line in (← IO.FS.readFile path).splitOn "\n" do
    if line.trimAscii.isEmpty then continue
    match run world line with
    | .error error => throw (IO.userError error)
    | .ok (next,text) => world := next; out.putStrLn text
