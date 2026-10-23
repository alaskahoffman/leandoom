import Doom.Proofs.E1M1LineSourceScan
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1TraversalSource
open Collision

/-- The line loop's control result: an early return, current result, and visits. -/
abbrev LineState := Option PathResult × PathResult × Array Bool

def lineFlow (flags : Nat) (trace : Divline) (lines : Array Line) (ids : Array Nat)
    (seen : Array Bool) (r : PathResult) : Except String LineState :=
  forIn ids (none,r,seen) fun id state => do
    if id ≥ 32768 then throw "path: signed linedef index is unverified"
    let some line := lines[id]? | do
      throw "path: invalid linedef"
      pure (.yield (none,state.2.1,state.2.2))
    if state.2.2[id]! then return .yield (none,state.2.1,state.2.2)
    let seen := state.2.2.set! id true
    if let some frac ← lineIntercept trace line then
      if flags &&& 4 != 0 && frac.raw < 65536 && line.back.isNone then
        return .done (some {state.2.1 with completed:=false},state.2.1,seen)
      let next ← appendIntercept state.2.1 ⟨frac,true,id⟩
      return .yield (none,next,seen)
    return .yield (none,state.2.1,seen)

/-- Exact enclosing traversal with a replaceable line scan. All profile checks,
block logging, object iteration, grid steps and ordered visitation remain here.
`live` checks this against the production definition for every flag setting. -/
def withLines (scene : Scene) (startX startY endX endY : Fixed)
    (scan : Divline → Array Line → Array Nat → Array Bool → PathResult → Except String (Option PathResult × PathResult × Array Bool))
    (flags : Nat) (visit : Intercept → Nat → Bool) : Except String PathResult := do
  let grid := scene.grid
  if !grid.vanillaOffsets || grid.width == 0 || grid.height == 0 ||
      grid.width ≥ 32768 || grid.height ≥ 32768 ||
      grid.cells.size != grid.width * grid.height || scene.links.size != grid.cells.size then
    throw "path: unsupported BLOCKMAP profile"
  let ox := Fixed.ofInt grid.origin.x
  let oy := Fixed.ofInt grid.origin.y
  let initial := pathStart ox oy startX startY endX endY
  let trace := initial.trace
  let mut result : PathResult := { trace }
  let x1 := initial.x1; let y1 := initial.y1
  let xt1 := initial.startBlockX; let yt1 := initial.startBlockY
  let xt2 := initial.endBlockX; let yt2 := initial.endBlockY
  let (mapxstep, portion, ystep) ← initial.xStep
  let mut yi := pathFirstIntercept y1 portion ystep
  let (mapystep, portion, xstep) ← initial.yStep
  let mut xi := pathFirstIntercept x1 portion xstep
  let mut mapx := xt1; let mut mapy := yt1
  let mut seen := Array.replicate scene.lines.size false
  for _ in [:64] do
    let inside := pathCellInside mapx mapy grid.width grid.height
    let cell := pathCellIndex mapx mapy grid.width
    if flags &&& 1 != 0 then
      result := { result with blocks := result.blocks.push (true, mapx, mapy) }
      if inside then
        let some ids := grid.cells[cell]? | throw "path: missing line cell"
        let out ← scan trace scene.lines (#[0] ++ ids) seen result
        result := out.2.1; seen := out.2.2
        match out.1 with
        | some stop => return stop
        | none => pure ()
    if flags &&& 2 != 0 then
      result := { result with blocks := result.blocks.push (false, mapx, mapy) }
      if inside then
        let some ids := scene.links[cell]? | throw "path: missing thing cell"
        for id in ids do
          let some thing := scene.things[id]? | throw "path: invalid actor link"
          if let some frac ← thingIntercept trace thing then
            result ← appendIntercept result ⟨frac, false, id⟩
    if mapx == xt2 && mapy == yt2 then break
    if yi.raw >>> 16 == mapy then
      yi := yi + ystep; mapx := mapx + mapxstep
    else if xi.raw >>> 16 == mapx then
      xi := xi + xstep; mapy := mapy + mapystep
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

/-- Definition-level equality to the live function, including failure and early
return behavior. Smart unfolding is disabled to normalize generated matchers. -/
theorem live (scene : Scene) (sx sy ex ey : Fixed) (flags : Nat) (visit : Intercept → Nat → Bool) :
    scene.pathTraverse sx sy ex ey flags visit=withLines scene sx sy ex ey (lineFlow flags) flags visit := by
  set_option smartUnfolding false in rfl

/-- At aiming flags, the control wrapper never returns early; it carries exactly
our checked seen-array line collector, including any error result. -/
theorem aiming_flow_list (trace : Divline) (lines : Array Line) (ids : List Nat)
    (seen : Array Bool) (r : PathResult) :
    lineFlow 3 trace lines ids.toArray seen r =
      (E1M1LineSourceLoop.lineCell trace lines ids.toArray seen r).map
        (fun out => (none,out.2,out.1)) := by
  unfold lineFlow E1M1LineSourceLoop.lineCell
  simp only [List.forIn_toArray]
  induction ids generalizing seen r with
  | nil => rfl
  | cons id ids ih =>
    simp only [List.forIn_cons]
    by_cases signed : id≥32768
    · simp [signed,Bind.bind,Except.bind,Except.map]; rfl
    · simp only [if_neg signed]
      cases lookup : lines[id]? with
      | none => rfl
      | some line =>
        by_cases duplicate : seen[id]! =true
        · simp only [if_pos duplicate,Bind.bind,Except.bind]
          exact ih seen r
        · simp only [if_neg duplicate]
          cases hit : lineIntercept trace line with
          | error e => rfl
          | ok frac =>
            cases frac with
            | none => exact ih (seen.set! id true) r
            | some frac =>
              simp only [show (3 : Nat) &&& 4=0 by decide,Bind.bind,Except.bind]
              cases appended : appendIntercept r ⟨frac,true,id⟩ with
              | error e => rfl
              | ok after => exact ih (seen.set! id true) after

/-- The interface used by the enclosing loop, specialized to the checked source
collector. The optional early return is absent at aiming flags. -/
def aimingScan (trace : Divline) (lines : Array Line) (ids : Array Nat)
    (seen : Array Bool) (r : PathResult) : Except String LineState :=
  (E1M1LineSourceLoop.lineCell trace lines ids seen r).map
    (fun out => (none,out.2,out.1))

theorem aiming_flow (trace : Divline) (lines : Array Line) (ids : Array Nat)
    (seen : Array Bool) (r : PathResult) :
    lineFlow 3 trace lines ids seen r=aimingScan trace lines ids seen r := by
  simpa [aimingScan] using aiming_flow_list trace lines ids.toList seen r

/-- The actual production aiming traversal uses precisely the proved collector
inside its complete enclosing control flow. No map-validity, capacity, fraction
or successful-result hypothesis is needed for this source-to-source equality.
DOS execution correspondence still needs the separately stated machine contracts. -/
theorem live_aiming (scene : Scene) (sx sy ex ey : Fixed) (visit : Intercept → Nat → Bool) :
    scene.pathTraverse sx sy ex ey 3 visit=withLines scene sx sy ex ey aimingScan 3 visit := by
  rw [live]
  have eq : lineFlow 3=aimingScan := by
    funext trace lines ids seen r
    exact aiming_flow trace lines ids seen r
  rw [eq]
end Doom.Proofs.E1M1TraversalSource
