/-
E1M1 turboLower floors and downWaitUpStay platforms, from Chocolate Doom 3.1.1
p_floor.c, p_plats.c and p_spec.c, commit 410d96855b5df5410ff591a90efeafa889119224.
Derived from id Software (1993-1996), Simon Howard (2005-2014).
SPDX-License-Identifier: GPL-2.0-or-later. See COPYING.md.
-/
import Doom.Plane
import Doom.Map

namespace Doom.FloorMover

inductive Kind where
  | turboLower | lift
  deriving BEq, Repr, Inhabited

inductive Status where
  | up | down | waiting | stasis
  deriving BEq, Repr, Inhabited

inductive Sound where
  | move | stop | start
  deriving BEq, Repr, Inhabited

inductive Event where
  | sound (value : Sound)
  | remove
  deriving BEq, Repr

structure Thinker where
  sector : Nat := 0
  kind : Kind := .turboLower
  speed : Fixed := Fixed.ofInt 4
  low : Fixed := ⟨0⟩
  high : Fixed := ⟨0⟩
  status : Status := .down
  wait : Int32 := 105
  count : Int32 := 0
  deriving BEq, Repr, Inhabited

def turbo (floor highest : Fixed) : Thinker :=
  { low := if highest == floor then highest else highest + Fixed.ofInt 8 }

def lift (floor lowest : Fixed) : Thinker :=
  { kind := .lift, low := ⟨min lowest.raw floor.raw⟩, high := floor }

structure Step (σ : Type) where
  thinker : Thinker
  heights : Plane.Heights
  state : σ
  events : Array Event := #[]
  removed : Bool := false

/-- The original floor/platform thinkers restricted to these two non-crushing
kinds. Plane callback effects persist through rollback; completion/removal and
sound requests retain their original order. -/
def Thinker.tick (t : Thinker) (heights : Plane.Heights) (levelTime : Int32) (state : σ)
    (change : Plane.Heights → Bool → σ → Bool × σ) : Step σ := Id.run do
  let mut out : Step σ := ⟨t,heights,state,#[],false⟩
  if t.kind == .lift && t.status == .stasis then return out
  if t.kind == .lift && t.status == .waiting then
    let count := t.count-1
    let status := if count == 0 then (if heights.floor == t.low then .up else .down) else .waiting
    return { out with thinker := { t with count, status }, events := if count == 0 then #[.sound .start] else #[] }
  let up := t.kind == .lift && t.status == .up
  let result := Plane.move heights t.speed (if up then t.high else t.low) false .floor
    (if up then 1 else -1) state change
  out := { out with heights := result.heights, state := result.state }
  if t.kind == .turboLower then
    if levelTime &&& 7 == 0 then out := { out with events := #[.sound .move] }
    if result.result == .pastDestination then
      out := { out with removed := true, events := out.events ++ #[.remove,.sound .stop] }
  else if up && result.result == .crushed then
    out := { out with thinker := { t with status := .down, count := t.wait }, events := #[.sound .start] }
  else if result.result == .pastDestination then
    out := { out with
      thinker := { t with status := .waiting, count := t.wait }
      removed := up, events := if up then #[.sound .stop,.remove] else #[.sound .stop] }
  return out

/-- Original getNextSector/P_Find*FloorSurrounding. Highest deliberately starts
at -500, not the sector's own floor; lowest starts at the current floor. -/
def surrounding (map : Map) (sector : Nat) : Fixed × Fixed := Id.run do
  let mut lowest := Fixed.ofInt map.sectors[sector]!.floor
  let mut highest := Fixed.ofInt (-500)
  for line in map.lines do
    if line.flags &&& 4 == 0 then continue
    let some front := map.sides[line.front]? | continue
    let some back := map.sides[line.back]? | continue
    let neighbor := if front.sector == sector then some back.sector
      else if back.sector == sector then some front.sector else none
    if let some id := neighbor then
      let height := Fixed.ofInt map.sectors[id]!.floor
      lowest := ⟨min lowest.raw height.raw⟩
      highest := ⟨max highest.raw height.raw⟩
  return (lowest,highest)

structure SpawnResult where
  map : Map
  thinkers : Array Thinker
  sounds : Array (Nat × Sound) := #[]

/-- Original DOOM 1.9 crossing gates/cases 36 and 88 plus their selected EV_Do*
spawn branches. Side is immaterial. `projectile` means one of the six excluded
original projectile types. Busy sectors include all supported plane movers.
Thirty active lifts is the original MAXPLATS limit; overflow is an explicit error. -/
def cross (map : Map) (thinkers : Array Thinker) (busy : Array Nat) (lineIndex : Nat)
    (player : Bool) (projectile : Bool := false) : Except String SpawnResult := do
  let some line := map.lines[lineIndex]? | throw "floor mover: invalid trigger line"
  let mut out : SpawnResult := ⟨map,thinkers,#[]⟩
  if line.special != 36 && line.special != 88 then return out
  if !player && (projectile || line.special != 88) then return out
  for i in [:map.sectors.size] do
    let sector := map.sectors[i]!
    if sector.tag != line.tag || busy.contains i || out.thinkers.any (·.sector == i) then continue
    let (lowest,highest) := surrounding map i
    let floor := Fixed.ofInt sector.floor
    let thinker := if line.special == 36 then turbo floor highest else lift floor lowest
    if thinker.kind == .lift then
      if (out.thinkers.filter (·.kind == .lift)).size ≥ 30 then
        throw "floor mover: no more active platforms (MAXPLATS=30)"
      out := { out with sounds := out.sounds.push (i,.start) }
    out := { out with thinkers := out.thinkers.push { thinker with sector := i } }
  if line.special == 36 then
    out := { out with map := { map with lines := map.lines.set! lineIndex { line with special := 0 } } }
  return out

end Doom.FloorMover
