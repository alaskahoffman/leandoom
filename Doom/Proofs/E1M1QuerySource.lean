import Doom.Proofs.E1M1QueryInit
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1QuerySource
open Collision

/-- All data actually supplied by the live query to its collection loop. -/
structure Start where
  trace : Divline
  grid : E1M1PathAdvance.Cell
  seen : Array Bool
  result : PathResult

def supported (scene : Scene) : Bool :=
  let grid := scene.grid
  !(!grid.vanillaOffsets || grid.width == 0 || grid.height == 0 ||
    grid.width ≥ 32768 || grid.height ≥ 32768 ||
    grid.cells.size != grid.width * grid.height || scene.links.size != grid.cells.size)

def prepared (scene : Scene) (p : PathStart) (xout yout : Int32 × Fixed × Fixed) : Start :=
  ⟨p.trace,E1M1FiringGridState.initial p xout yout,
    Array.replicate scene.lines.size false,{trace:=p.trace}⟩

/-- Profile check precedes X setup, which precedes Y setup, including errors. -/
def prepare (scene : Scene) (sx sy ex ey : Fixed) : Except String Start := do
  if !supported scene then throw "path: unsupported BLOCKMAP profile"
  let p := pathStart (Fixed.ofInt scene.grid.origin.x) (Fixed.ofInt scene.grid.origin.y) sx sy ex ey
  let xout ← p.xStep
  let yout ← p.yStep
  return prepared scene p xout yout

/-- Exact production ordered-hit tail; its DOS correspondence is still separate. -/
def visitHits (initial : PathResult) (visit : Intercept → Nat → Bool) : Except String PathResult := do
  let mut result := initial
  -- Use the original strict-min selection rather than a sort with unspecified ties.
  let mut work := result.collected
  for _ in [:work.size] do
    let mut distance : Int32 := 2147483647
    let mut chosen := none
    for i in [:work.size] do
      if work[i]!.frac.raw < distance then
        distance := work[i]!.frac.raw; chosen := some i
    if distance > 65536 then break
    let some i := chosen | throw "path: missing finite intercept"
    let hit := work[i]!
    result := { result with visited := result.visited.push hit }
    if !visit hit (result.visited.size - 1) then return { result with completed := false }
    work := work.set! i { hit with frac := ⟨2147483647⟩ }
  return result


def runPrepared (scene : Scene) (start : Start) (visit : Intercept → Nat → Bool) : Except String PathResult := do
  let out ← E1M1LiveWalk.source scene start.trace 64 start.grid start.seen start.result
  match out.1 with
  | some stop => return stop
  | none => visitHits out.2.1 visit

attribute [local irreducible] ForIn.forIn Array.append Array.push

/-- This is an equality of the whole production aiming query, including rejected
profiles, axis errors, collection errors and the ordered visitor tail. -/
theorem live (scene : Scene) (sx sy ex ey : Fixed) (visit : Intercept → Nat → Bool) :
    scene.pathTraverse sx sy ex ey 3 visit =
      (do let start ← prepare scene sx sy ex ey; runPrepared scene start visit) := by
  rw [E1M1TraversalLoop.live_aiming]
  set_option smartUnfolding false in
    simp only [E1M1TraversalLoop.withLoop,prepare,supported,Bool.not_not]
    split
    · rfl
    · cases hx : (pathStart (Fixed.ofInt scene.grid.origin.x) (Fixed.ofInt scene.grid.origin.y) sx sy ex ey).xStep with
      | error e => rfl
      | ok xout =>
        rcases xout with ⟨dx,portion,ys⟩
        cases hy : (pathStart (Fixed.ofInt scene.grid.origin.x) (Fixed.ofInt scene.grid.origin.y) sx sy ex ey).yStep with
        | error e => rfl
        | ok yout =>
          rcases yout with ⟨dy,portionY,xs⟩
          rfl

/-- Successful preparation supplies exactly the geometry and clean source state
used by the machine initialization theorem. -/
theorem prepare_ok (scene : Scene) (sx sy ex ey : Fixed)
    (profile : supported scene=true) (xout yout : Int32 × Fixed × Fixed)
    (okX : (pathStart (Fixed.ofInt scene.grid.origin.x) (Fixed.ofInt scene.grid.origin.y) sx sy ex ey).xStep=.ok xout)
    (okY : (pathStart (Fixed.ofInt scene.grid.origin.x) (Fixed.ofInt scene.grid.origin.y) sx sy ex ey).yStep=.ok yout) :
    prepare scene sx sy ex ey=.ok (prepared scene
      (pathStart (Fixed.ofInt scene.grid.origin.x) (Fixed.ofInt scene.grid.origin.y) sx sy ex ey) xout yout) := by
  simp [prepare,profile,okX,okY]
  rfl

open Verification X86 X86Memory

/-- Source preparation and DOS initialization agree on the loop's numeric state,
empty hit buffer and initial visit history. All memory premises are at query
entry; this does not yet assemble the map/payload images or execution prefix. -/
theorem initialized (s : X86Memory.State) (scene : Scene) (sx sy ex ey : Fixed)
    (profile : supported scene=true)
    (geometry : OriginalPathInit.Inputs s (Fixed.ofInt scene.grid.origin.x)
      (Fixed.ofInt scene.grid.origin.y) sx sy ex ey)
    (xout yout : Int32 × Fixed × Fixed)
    (okX : (pathStart (Fixed.ofInt scene.grid.origin.x) (Fixed.ofInt scene.grid.origin.y) sx sy ex ey).xStep=.ok xout)
    (okY : (pathStart (Fixed.ofInt scene.grid.origin.x) (Fixed.ofInt scene.grid.origin.y) sx sy ex ey).yStep=.ok yout)
    (lines : Word) (resolve : Intercept → Word)
    (cursorSafe : E1M1PathMapSetup.StackSafe (s.regs 4-60) 0x2c028)
    (epochSafe : E1M1PathMapSetup.StackSafe (s.regs 4-60) 0x13580)
    (stampSafe : ∀ j<scene.lines.size, E1M1PathMapSetup.Safe s (OriginalLineVisits.stamp lines j))
    (fresh : ∀ j<scene.lines.size, load32 s.memory (OriginalLineVisits.stamp lines j)≠load32 s.memory 0x13580+1) :
    let start := prepared scene
      (pathStart (Fixed.ofInt scene.grid.origin.x) (Fixed.ofInt scene.grid.origin.y) sx sy ex ey) xout yout
    let out := E1M1PathMapSetup.grid s
    prepare scene sx sy ex ey=.ok start ∧
    E1M1PathAdvance.observe out.core=start.grid ∧
    OriginalLineCollection.Tracks out.core 0x2ba20 resolve start.result.collected 0 ∧
    OriginalLineVisits.Represents out.core.memory lines (load32 s.memory 0x13580+1) start.seen ∧
    out.pc=0x2ca7f ∧ out.core.regs 4=s.regs 4-60 := by
  have numeric := E1M1QueryInit.numeric s _ _ sx sy ex ey geometry xout yout okX okY
  exact ⟨prepare_ok scene sx sy ex ey profile xout yout okX okY,numeric.1,
    E1M1QueryInit.empty_collection s _ _ sx sy ex ey geometry cursorSafe resolve,
    E1M1QueryInit.initial_visits s _ _ sx sy ex ey geometry lines scene.lines.size epochSafe stampSafe fresh,
    numeric.2⟩
end Doom.Proofs.E1M1QuerySource
