/-
Sector lighting from Chocolate Doom 3.1.1 p_lights.c / p_spec.c,
commit 410d96855b5df5410ff591a90efeafa889119224.
Derived from id Software (1993-1996), Simon Howard (2005-2014).
SPDX-License-Identifier: GPL-2.0-or-later. See COPYING.md.
-/
import Doom.Map
import Doom.FloorMover
import Doom.Random

namespace Doom.SectorLights

inductive Kind where
  | fire | flash | strobe | glow
  deriving Inhabited, BEq, Repr

structure Thinker where
  kind : Kind := .fire
  sector : Nat := 0
  count : Int32 := 0
  minimum : Int32 := 0
  maximum : Int32 := 0
  dark : Int32 := 0
  direction : Int32 := 0
  deriving Inhabited, BEq, Repr

/-- sector_t.lightlevel is a signed short, unlike the thinker's int fields. -/
def lightShort (value : Int32) : Int32 := Int32.ofInt (Int16.ofInt value.toInt).toInt

/-- Lighting cases of P_SpawnSpecials for DOOM 1.9. `minimum` comes from the
original two-sided adjacency search. Special 4 retains its damage-sector marker. -/
def spawn (special : Nat) (light minimum : Int32) (rng : DoomRandom)
    : Option (Thinker × Nat × DoomRandom) := Id.run do
  let base : Thinker := { minimum, maximum := light }
  match special with
  | 1 =>
    let (r, rng) := rng.nextPlay
    return some ({ base with kind := .flash, count := Int32.ofInt (Int.ofNat ((r &&& 64)+1)) }, 0, rng)
  | 2 | 3 | 4 | 12 | 13 =>
    let sync := special == 12 || special == 13
    let (r, rng) := if sync then (0, rng) else rng.nextPlay
    let thinker := { base with
      kind := .strobe, minimum := if minimum == light then 0 else minimum
      count := if sync then 1 else Int32.ofInt (Int.ofNat ((r &&& 7)+1))
      dark := if special == 3 || special == 12 then 35 else 15 }
    return some (thinker, if special == 4 then 4 else 0, rng)
  | 8 => return some ({ base with kind := .glow, direction := -1 }, 0, rng)
  | 17 => return some ({ base with kind := .fire, minimum := minimum+16, count := 4 }, 0, rng)
  | _ => return none

/-- One original T_* lighting call. In particular fire tests the current light
against its lower bound before subtracting from max, and glow reverses by undoing
its step rather than clamping to the endpoint. Every sector write narrows to short. -/
def Thinker.tick (initial : Thinker) (light : Int32) (rng : DoomRandom)
    : Thinker × Int32 × DoomRandom := Id.run do
  let mut s := initial
  let mut light := light
  if s.kind == .glow then
    if s.direction == -1 then
      light := lightShort (light-8)
      if light ≤ s.minimum then
        light := lightShort (light+8)
        s := { s with direction := 1 }
    else if s.direction == 1 then
      light := lightShort (light+8)
      if light ≥ s.maximum then
        light := lightShort (light-8)
        s := { s with direction := -1 }
    return (s,light,rng)
  s := { s with count := s.count-1 }
  if s.count != 0 then return (s,light,rng)
  match s.kind with
  | .fire =>
    let (r, rng) := rng.nextPlay
    let amount : Int32 := Int32.ofInt (Int.ofNat ((r &&& 3)*16))
    let value := if light-amount < s.minimum then s.minimum else s.maximum-amount
    return ({ s with count := 4 }, lightShort value, rng)
  | .flash =>
    let (r, rng) := rng.nextPlay
    let high := light == s.maximum
    let count := Int32.ofInt (Int.ofNat ((r &&& (if high then 7 else 64))+1))
    return ({ s with count }, lightShort (if high then s.minimum else s.maximum), rng)
  | .strobe =>
    let low := light == s.minimum
    return ({ s with count := if low then 5 else s.dark },
      lightShort (if low then s.maximum else s.minimum), rng)
  | .glow => return (s,light,rng)

/-- P_FindMinSurroundingLight/getNextSector over validated WAD sidedef indices.
One-sided lines never count, even if a back sidedef happens to be present. -/
def minimumAround (map : Map) (sector : Nat) : Int32 := Id.run do
  let mut lowest := Int32.ofInt map.sectors[sector]!.light
  for line in map.lines do
    if line.flags &&& 4 == 0 then continue
    let some front := map.sides[line.front]? | continue
    let some back := map.sides[line.back]? | continue
    let neighbor := if front.sector == sector then some back.sector
      else if back.sector == sector then some front.sector else none
    if let some neighbor := neighbor then
      lowest := min lowest (Int32.ofInt map.sectors[neighbor]!.light)
  return lowest

/-- Spawn in sector order, sharing the gameplay RNG with surrounding thinkers. -/
def spawnMap (map : Map) (rng : DoomRandom) : Map × Array Thinker × DoomRandom := Id.run do
  let mut map := map
  let mut rng := rng
  let mut thinkers := #[]
  for i in [:map.sectors.size] do
    let sector := map.sectors[i]!
    if let some (thinker, special, next) := spawn sector.special (Int32.ofInt sector.light) (minimumAround map i) rng then
      thinkers := thinkers.push { thinker with sector := i }
      rng := next
      map := { map with sectors := map.sectors.set! i { sector with special } }
  return (map,thinkers,rng)

/-- Thinkers keep insertion order, including random draws on coincident tics. -/
def tickMap (map : Map) (thinkers : Array Thinker) (rng : DoomRandom)
    : Map × Array Thinker × DoomRandom := Id.run do
  let mut map := map
  let mut thinkers := thinkers
  let mut rng := rng
  for i in [:thinkers.size] do
    let thinker := thinkers[i]!
    let sector := map.sectors[thinker.sector]!
    let (next,light,random) := thinker.tick (Int32.ofInt sector.light) rng
    thinkers := thinkers.set! i next
    rng := random
    map := { map with sectors := map.sectors.set! thinker.sector { sector with light := light.toInt } }
  return (map,thinkers,rng)

/-- EV_LightTurnOn deliberately carries `bright` across tagged sectors. If it
becomes nonzero, subsequent sectors reuse it instead of searching their neighbors.
Tag zero is an ordinary tag here. -/
def turnOn (initial : Map) (tag : Nat) (brightness : Int32) : Map := Id.run do
  let mut map := initial
  let mut bright := brightness
  for i in [:map.sectors.size] do
    let sector := map.sectors[i]!
    if sector.tag != tag then continue
    if bright == 0 then
      for line in map.lines do
        if line.flags &&& 4 == 0 then continue
        let some front := map.sides[line.front]? | continue
        let some back := map.sides[line.back]? | continue
        let neighbor := if front.sector == i then some back.sector
          else if back.sector == i then some front.sector else none
        if let some neighbor := neighbor then
          bright := max bright (Int32.ofInt map.sectors[neighbor]!.light)
    map := { map with sectors := map.sectors.set! i { sector with light := (lightShort bright).toInt } }
  return map

/-- EV_TurnTagLightsOff reads the already-updated map for each next sector. -/
def turnOff (initial : Map) (tag : Nat) : Map := Id.run do
  let mut map := initial
  for i in [:map.sectors.size] do
    let sector := map.sectors[i]!
    if sector.tag != tag then continue
    let level := minimumAround map i
    map := { map with sectors := map.sectors.set! i { sector with light := (lightShort level).toInt } }
  return map

/-- Runtime state carried through immediate movement callbacks. `busy` represents
sector.specialdata (doors and supported floor/platform movers); light thinkers do not
own specialdata and therefore do not suppress another strobe thinker. -/
structure World where
  map : Map
  thinkers : Array Thinker := #[]
  rng : DoomRandom := {}
  busy : Array Nat := #[]
  movers : Array FloorMover.Thinker := #[]
  moverSounds : Array (Nat × FloorMover.Sound) := #[]

/-- EV_StartLightStrobing appends in sector order; active lights are not replaced. -/
def World.startStrobing (initial : World) (tag : Nat) : World := Id.run do
  let mut world := initial
  for i in [:world.map.sectors.size] do
    let sector := world.map.sectors[i]!
    if sector.tag != tag || world.busy.contains i then continue
    let some (thinker,special,rng) := spawn 3 (Int32.ofInt sector.light) (minimumAround world.map i) world.rng
      | continue
    world := { world with
      map := { world.map with sectors := world.map.sectors.set! i { sector with special } }
      thinkers := world.thinkers.push { thinker with sector := i }, rng }
  return world

/-- Lighting subset of P_CrossSpecialLine, DOOM 1.9. Both crossing directions
activate; nonplayers never activate these eight types. One-shot lines clear even
when no sector matches or every strobe target has specialdata. -/
def World.cross (world : World) (lineIndex : Nat) (player : Bool) : World := Id.run do
  let some line := world.map.lines[lineIndex]? | return world
  if !player then return world
  let mut world := world
  match line.special with
  | 12 | 80 => world := { world with map := turnOn world.map line.tag 0 }
  | 13 | 81 => world := { world with map := turnOn world.map line.tag 255 }
  | 35 | 79 => world := { world with map := turnOn world.map line.tag 35 }
  | 104 => world := { world with map := turnOff world.map line.tag }
  | 17 => world := world.startStrobing line.tag
  | _ => return world
  if #[12,13,17,35,104].contains line.special then
    world := { world with map := { world.map with lines := world.map.lines.set! lineIndex { line with special := 0 } } }
  return world

/-- Immediate crossing dispatch for the supported lighting and E1M1 movers. -/
def World.crossAll (world : World) (line : Nat) (player : Bool) : Except String World := do
  let result ← FloorMover.cross world.map world.movers world.busy line player
  let world := { world with
    map := result.map, movers := result.thinkers
    moverSounds := world.moverSounds ++ result.sounds
    busy := world.busy ++ result.thinkers.map (fun (t : FloorMover.Thinker) => t.sector) }
  return world.cross line player

end Doom.SectorLights
