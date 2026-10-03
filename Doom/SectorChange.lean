/-
Non-crushing P_ChangeSector/PIT_ChangeSector and P_GroupLines block bounds,
Chocolate Doom 3.1.1, commit 410d96855b5df5410ff591a90efeafa889119224.
Derived from id Software (1993-1996), Simon Howard (2005-2014).
SPDX-License-Identifier: GPL-2.0-or-later. See COPYING.md.
-/
import Doom.HeightClip

namespace Doom.Collision

structure SectorBlocks where
  left : Int
  right : Int
  bottom : Int
  top : Int
  deriving BEq, Repr, Inhabited

/-- P_GroupLines expands by MAXRADIUS and clamps each bound on only one side.
Subtraction/addition wrap before the arithmetic shift. -/
def sectorBlocks (box : Box) (grid : Blockmap) : SectorBlocks :=
  let x := Fixed.ofInt grid.origin.x
  let y := Fixed.ofInt grid.origin.y
  let margin := Fixed.ofInt 32
  { left := max 0 (blockCoordinate (box.left - margin) x)
    right := min (Int.ofNat grid.width - 1) (blockCoordinate (box.right + margin) x)
    bottom := max 0 (blockCoordinate (box.bottom - margin) y)
    top := min (Int.ofNat grid.height - 1) (blockCoordinate (box.top + margin) y) }

def mapSectorBlocks (map : Map) (sector : Nat) : Except String SectorBlocks := do
  if sector ≥ map.sectors.size then throw "sector change: invalid sector"
  let mut box : Box := ⟨⟨-2147483648⟩,⟨2147483647⟩,⟨2147483647⟩,⟨-2147483648⟩⟩
  for line in map.lines do
    let front := (map.sides[line.front]?).map (·.sector)
    let back := (map.sides[line.back]?).map (·.sector)
    if front != some sector && back != some sector then continue
    for index in #[line.v1,line.v2] do
      let some vertex := map.vertices[index]? | throw "sector change: invalid vertex"
      let x := (Fixed.ofInt vertex.x).raw
      let y := (Fixed.ofInt vertex.y).raw
      box := ⟨⟨max box.top.raw y⟩,⟨min box.bottom.raw y⟩,⟨min box.left.raw x⟩,⟨max box.right.raw x⟩⟩
  return Collision.sectorBlocks box map.blockmap

inductive SectorEvent where
  | gib (actor : Nat)
  | remove (actor : Nat)
  deriving BEq, Repr

structure SectorChangeResult where
  scene : Scene
  blocked : Bool := false
  visited : Array Nat := #[]
  events : Array SectorEvent := #[]

/-- DOOM 1.9 non-crushing sector change. Traversal follows current bnext links:
queries may remove a future pickup, while removal of the current dropped object
retains its saved successor. No actor spawning/relinking occurs in this domain.
The damage/blood branch for crunch=true is deliberately a separate pending port. -/
def Scene.changeSectorNoCrush (initial : Scene) (bounds : SectorBlocks) (sectorAt : SectorAt)
    (player : Option Nat) : Except String SectorChangeResult := do
  let mut out : SectorChangeResult := { scene := initial }
  let width := initial.grid.width
  let height := initial.grid.height
  for x in [(max 0 bounds.left).toNat:(max 0 (min (Int.ofNat width) (bounds.right+1))).toNat] do
    for y in [(max 0 bounds.bottom).toNat:(max 0 (min (Int.ofNat height) (bounds.top+1))).toNat] do
      let cell := y*width+x
      let some ids := out.scene.links[cell]? | throw "sector change: missing block cell"
      let mut cursor := ids[0]?
      let mut fuel := initial.things.size+1
      while let some id := cursor do
        if fuel == 0 then throw "sector change: cyclic actor links"
        fuel := fuel-1
        let some ids := out.scene.links[cell]? | throw "sector change: missing block cell"
        let some index := ids.findIdx? (· == id) | throw "sector change: stale actor link"
        let successor := ids[index+1]?
        let clipped ← out.scene.heightClip id sectorAt (player == some id)
        out := { out with scene := clipped.scene, visited := out.visited.push id }
        let thing := out.scene.things[id]!
        if !clipped.fits then
          if thing.health ≤ 0 then
            let thing := { thing with solid := false, height := ⟨0⟩, radius := ⟨0⟩, gibbed := true }
            out := { out with
              scene := { out.scene with things := out.scene.things.set! id thing }
              events := out.events.push (.gib id) }
          else if thing.dropped || thing.pickup.any (·.dropped) then
            let scene ← out.scene.unlinkThing id
            out := { out with
              scene := { scene with things := scene.things.set! id { thing with removed := true } }
              events := out.events.push (.remove id) }
          else if thing.shootable then out := { out with blocked := true }
        if out.scene.things[id]!.removed then cursor := successor
        else
          let ids := out.scene.links[cell]!
          let some index := ids.findIdx? (· == id) | throw "sector change: actor unexpectedly unlinked"
          cursor := ids[index+1]?
  return out

end Doom.Collision
