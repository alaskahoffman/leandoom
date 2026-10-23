import Doom.Proofs.E1M1GeneratedWalk
import Doom.Proofs.E1M1TraversalSource
import Init.Data.Range.Lemmas
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1TraversalLoop
open Collision
abbrev LoopState := Option PathResult × PathResult × Fixed × Fixed × Int32 × Int32 × Array Bool
abbrev Scan := Divline → Array Line → Array Nat → Array Bool → PathResult → Except String E1M1TraversalSource.LineState

/-- The production loop's control tuple, including its early-return channel. -/
def finish (ex ey dx dy : Int32) (xs ys : Fixed) (r : PathResult)
    (yi xi : Fixed) (x y : Int32) (seen : Array Bool) : Except String (ForInStep LoopState) :=
  if x==ex && y==ey then pure (.done (none,r,yi,xi,x,y,seen))
  else if yi.raw >>> 16==y then pure (.yield (none,r,yi+ys,xi,x+dx,y,seen))
  else if xi.raw >>> 16==x then pure (.yield (none,r,yi,xi+xs,x,y+dy,seen))
  else pure (.yield (none,r,yi,xi,x,y,seen))

/-- The exact object-array loop, shared to keep generated matchers out of joins. -/
def objectLoop (scene : Scene) (trace : Divline) (ids : Array Nat) (r : PathResult) :
    Except String PathResult :=
  forIn ids r fun id r => do
    let some thing := scene.things[id]? | do
      throw "path: invalid actor link"
      pure (.yield r)
    if let some frac ← thingIntercept trace thing then
      let r ← appendIntercept r ⟨frac,false,id⟩
      return .yield r
    return .yield r

/-- One iteration, extracted without altering the live line/object order or errors. -/
def body (scene : Scene) (trace : Divline) (scan : Scan) (flags : Nat)
    (ex ey dx dy : Int32) (xs ys : Fixed) (_ : Nat) (s : LoopState) :
    Except String (ForInStep LoopState) := do
  let r := s.2.1
  let yi := s.2.2.1
  let xi := s.2.2.2.1
  let x := s.2.2.2.2.1
  let y := s.2.2.2.2.2.1
  let seen := s.2.2.2.2.2.2
  let inside := pathCellInside x y scene.grid.width scene.grid.height
  let cell := pathCellIndex x y scene.grid.width
  let objects (r : PathResult) (seen : Array Bool) := do
    let mut r := r
    if flags &&& 2 != 0 then
      r := {r with blocks:=r.blocks.push (false,x,y)}
      if inside then
        let some ids := scene.links[cell]? | throw "path: missing thing cell"
        r ← objectLoop scene trace ids r
    finish ex ey dx dy xs ys r yi xi x y seen
  if flags &&& 1 != 0 then
    let r := {r with blocks:=r.blocks.push (true,x,y)}
    if inside then
      let some ids := scene.grid.cells[cell]? | throw "path: missing line cell"
      let out ← scan trace scene.lines (#[0] ++ ids) seen r
      match out.1 with
      | some stop => return .done (some stop,out.2.1,yi,xi,x,y,out.2.2)
      | none => objects out.2.1 out.2.2
    else objects r seen
  else objects r seen

abbrev Walker := Scene → Divline → Int32 → Int32 → Int32 → Int32 → Fixed → Fixed → LoopState → Except String LoopState

def walk (scan : Scan) (flags fuel : Nat) : Walker := fun scene trace ex ey dx dy xs ys s =>
  forIn [:fuel] s (body scene trace scan flags ex ey dx dy xs ys)

def withLoop (scene : Scene) (startX startY endX endY : Fixed)
    (loop : Walker) (visit : Intercept → Nat → Bool) : Except String PathResult := do
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
  let out ← loop scene trace xt2 yt2 mapxstep mapystep xstep ystep
    (none,result,yi,xi,mapx,mapy,seen)
  result := out.2.1
  match out.1 with
  | some stop => return stop
  | none => pure ()
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


attribute [local irreducible] ForIn.forIn Array.append Array.push

/-- Exact equality to the complete live traversal with its grid loop exposed. -/
theorem live (scene : Scene) (sx sy ex ey : Fixed) (flags : Nat) (visit : Intercept → Nat → Bool) :
    scene.pathTraverse sx sy ex ey flags visit=
      withLoop scene sx sy ex ey (walk (E1M1TraversalSource.lineFlow flags) flags 64) visit := by
  set_option smartUnfolding false in rfl
/-- The live aiming traversal uses the checked source scan in this exact loop. -/
theorem live_aiming (scene : Scene) (sx sy ex ey : Fixed) (visit : Intercept → Nat → Bool) :
    scene.pathTraverse sx sy ex ey 3 visit=
      withLoop scene sx sy ex ey (walk E1M1TraversalSource.aimingScan 3 64) visit := by
  rw [live]
  have scan : E1M1TraversalSource.lineFlow 3=E1M1TraversalSource.aimingScan := by
    funext trace lines ids seen r
    exact E1M1TraversalSource.aiming_flow trace lines ids seen r
  rw [scan]
end Doom.Proofs.E1M1TraversalLoop
