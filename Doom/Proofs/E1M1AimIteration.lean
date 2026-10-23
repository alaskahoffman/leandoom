import Doom.Proofs.E1M1AimWindow
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1AimIteration
open Collision E1M1AimSource

/-- Exact state threaded by the production loop (early result, top, bottom, portals). -/
abbrev LoopState := Option AimResult × Fixed × Fixed × Array AutoAim.Portal

/-- A single iteration of the production post-path loop, exposed for proofs. -/
def visit (scene : Scene) (shooter : Nat) (thing : SolidThing)
    (path : PathResult) (distance : Fixed) (i : Nat) (state : LoopState) :
    Except String (ForInStep LoopState) := do
  let z := thing.shootHeight
  let mut top := state.2.1
  let mut bottom := state.2.2.1
  let mut portals := state.2.2.2
  let hit := path.visited[i]!
  let dist := distance * hit.frac
  if hit.isLine then
    let line := scene.lines[hit.id]!
    if !line.twoSided then return .done (some {path:=stopped path (i+1)},top,bottom,portals)
    let some back := line.back | throw "hitscan: missing two-sided back sector is unverified"
    let low : Fixed := ⟨max line.front.floor.raw back.floor.raw⟩
    let high : Fixed := ⟨min line.front.ceiling.raw back.ceiling.raw⟩
    if low.raw ≥ high.raw then return .done (some {path:=stopped path (i+1)},top,bottom,portals)
    portals := portals.push { distance := dist, bottom := low, top := high, line := hit.id }
    if line.front.floor != back.floor then bottom := ⟨max bottom.raw (← checkedPathDiv (low-z) dist).raw⟩
    if line.front.ceiling != back.ceiling then top := ⟨min top.raw (← checkedPathDiv (high-z) dist).raw⟩
    if top.raw ≤ bottom.raw then return .done (some {path:=stopped path (i+1)},top,bottom,portals)
  else
    let target := scene.things[hit.id]!
    if hit.id == shooter || !target.shootable then return .yield (none,top,bottom,portals)
    let ttop ← checkedPathDiv (target.z + target.height - z) dist
    if ttop.raw < bottom.raw then return .yield (none,top,bottom,portals)
    let tbottom ← checkedPathDiv (target.z-z) dist
    if tbottom.raw > top.raw then return .yield (none,top,bottom,portals)
    let window : AutoAim.Window := { portalBottom := bottom.raw, portalTop := top.raw, targetBottom := tbottom.raw, targetTop := ttop.raw, distance := dist, shootZ := z, target := hit.id, targetZ := target.z, targetHeight := target.height, portals }
    return .done (some { slope := AutoAim.center window.bottom window.top, target := some hit.id, path := stopped path (i+1), window := some window },top,bottom,portals)
  return .yield (none,top,bottom,portals)

/-- Proof-only continuation of the live hit loop; no engine code is replaced. -/
def remaining (scene : Scene) (shooter : Nat) (thing : SolidThing)
    (path : PathResult) (distance : Fixed) (indices : List Nat)
    (lower upper : Fixed) (history : Array AutoAim.Portal) : Except String AimResult := do
  let state ← forIn indices (none,upper,lower,history) (visit scene shooter thing path distance)
  match state.1 with
  | some result => return result
  | none => return {path}

/-- Exposing the continuation preserves the actual live loop definition. -/
theorem live (scene : Scene) (shooter : Nat) (thing : SolidThing)
    (path : PathResult) (distance : Fixed) :
    afterPath scene shooter thing path distance =
      remaining scene shooter thing path distance (List.range' 0 path.visited.size)
        aimBottomSlope aimTopSlope #[] := by
  simp only [afterPath,remaining,Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  congr 2
  funext state
  cases state.1 <;> rfl

def bottomAfter (front back : Heights) (lower slope : Fixed) : Fixed :=
  if front.floor=back.floor then lower else ⟨max lower.raw slope.raw⟩
def topAfter (front back : Heights) (upper slope : Fixed) : Fixed :=
  if front.ceiling=back.ceiling then upper else ⟨min upper.raw slope.raw⟩
def portal (front back : Heights) (distance : Fixed) (hit : Intercept) : AutoAim.Portal :=
  {distance := distance*hit.frac, bottom := ⟨max front.floor.raw back.floor.raw⟩,
   top := ⟨min front.ceiling.raw back.ceiling.raw⟩, line := hit.id}

theorem fixed_bne (a b : Fixed) : (a != b)=decide (a≠b) := by
  cases a with | mk a =>
    cases b with | mk b =>
      change (!(a == b))=decide (Fixed.mk a≠Fixed.mk b)
      simp
      rfl

theorem visit_line (scene : Scene) (shooter : Nat) (thing : SolidThing)
    (path : PathResult) (distance : Fixed) (i : Nat)
    (lower upper floorSlope ceilingSlope : Fixed) (history : Array AutoAim.Portal)
    (hit : Intercept) (back : Heights)
    (selected : path.visited[i]! = hit) (isLine : hit.isLine=true)
    (two : scene.lines[hit.id]!.twoSided=true) (backSector : scene.lines[hit.id]!.back=some back)
    (pass : max scene.lines[hit.id]!.front.floor.raw back.floor.raw <
      min scene.lines[hit.id]!.front.ceiling.raw back.ceiling.raw)
    (floorOk : scene.lines[hit.id]!.front.floor≠back.floor →
      checkedPathDiv (⟨max scene.lines[hit.id]!.front.floor.raw back.floor.raw⟩-thing.shootHeight)
        (distance*hit.frac)=.ok floorSlope)
    (ceilingOk : scene.lines[hit.id]!.front.ceiling≠back.ceiling →
      checkedPathDiv (⟨min scene.lines[hit.id]!.front.ceiling.raw back.ceiling.raw⟩-thing.shootHeight)
        (distance*hit.frac)=.ok ceilingSlope) :
    visit scene shooter thing path distance i (none,upper,lower,history) =
      if (bottomAfter scene.lines[hit.id]!.front back lower floorSlope).raw <
         (topAfter scene.lines[hit.id]!.front back upper ceilingSlope).raw then
        .ok (.yield (none,topAfter scene.lines[hit.id]!.front back upper ceilingSlope,
          bottomAfter scene.lines[hit.id]!.front back lower floorSlope,
          history.push (portal scene.lines[hit.id]!.front back distance hit)))
      else .ok (.done (some {path := stopped path (i+1)},
        topAfter scene.lines[hit.id]!.front back upper ceilingSlope,
        bottomAfter scene.lines[hit.id]!.front back lower floorSlope,
        history.push (portal scene.lines[hit.id]!.front back distance hit))) := by
  have notClosed : ¬ min scene.lines[hit.id]!.front.ceiling.raw back.ceiling.raw ≤
    max scene.lines[hit.id]!.front.floor.raw back.floor.raw := by
    simp only [Int32.lt_iff_toInt_lt] at pass
    simp only [Int32.le_iff_toInt_le]; omega
  have flip (a b : Int32) : (a≤b)=(¬b<a) := by
    apply propext
    simp only [Int32.le_iff_toInt_le,Int32.lt_iff_toInt_lt]
    omega
  by_cases hf : scene.lines[hit.id]!.front.floor=back.floor <;>
    by_cases hc : scene.lines[hit.id]!.front.ceiling=back.ceiling <;>
    by_cases go : (bottomAfter scene.lines[hit.id]!.front back lower floorSlope).raw <
      (topAfter scene.lines[hit.id]!.front back upper ceilingSlope).raw
  all_goals
    simp only [portal,visit,selected,isLine,two,Bool.not_true,Bool.false_eq_true,
      ↓reduceIte,backSector,fixed_bne,decide_eq_true_eq,notClosed]
    simp only [hf,hc,ne_eq,not_true_eq_false,not_false_eq_true] at floorOk ceilingOk
    simp only [bottomAfter,topAfter,hf,hc,↓reduceIte] at go
    simp only [ne_eq,eq_self,hf,hc,not_true_eq_false,not_false_eq_true,↓reduceIte,floorOk,ceilingOk,
      Except.bind,Except.pure,pure,bind,bottomAfter,topAfter,flip,go]
  all_goals rfl

/-- One arbitrary open line in the actual loop: clip both bounds, stop on a
closed window (including equality), otherwise carry bounds and portal history
into precisely the remaining hit indices. Divisions are required only when the
corresponding heights differ. -/
theorem next_line (scene : Scene) (shooter : Nat) (thing : SolidThing)
    (path : PathResult) (distance : Fixed) (i : Nat) (rest : List Nat)
    (lower upper floorSlope ceilingSlope : Fixed) (history : Array AutoAim.Portal)
    (hit : Intercept) (back : Heights)
    (selected : path.visited[i]! = hit) (isLine : hit.isLine=true)
    (two : scene.lines[hit.id]!.twoSided=true) (backSector : scene.lines[hit.id]!.back=some back)
    (pass : max scene.lines[hit.id]!.front.floor.raw back.floor.raw <
      min scene.lines[hit.id]!.front.ceiling.raw back.ceiling.raw)
    (floorOk : scene.lines[hit.id]!.front.floor≠back.floor →
      checkedPathDiv (⟨max scene.lines[hit.id]!.front.floor.raw back.floor.raw⟩-thing.shootHeight)
        (distance*hit.frac)=.ok floorSlope)
    (ceilingOk : scene.lines[hit.id]!.front.ceiling≠back.ceiling →
      checkedPathDiv (⟨min scene.lines[hit.id]!.front.ceiling.raw back.ceiling.raw⟩-thing.shootHeight)
        (distance*hit.frac)=.ok ceilingSlope) :
    remaining scene shooter thing path distance (i::rest) lower upper history =
      if (bottomAfter scene.lines[hit.id]!.front back lower floorSlope).raw <
         (topAfter scene.lines[hit.id]!.front back upper ceilingSlope).raw then
        remaining scene shooter thing path distance rest
          (bottomAfter scene.lines[hit.id]!.front back lower floorSlope)
          (topAfter scene.lines[hit.id]!.front back upper ceilingSlope)
          (history.push (portal scene.lines[hit.id]!.front back distance hit))
      else .ok {path := stopped path (i+1)} := by
  unfold remaining
  rw [List.forIn_cons,visit_line scene shooter thing path distance i lower upper floorSlope ceilingSlope history
    hit back selected isLine two backSector pass floorOk ceilingOk]
  split <;> rfl
end Doom.Proofs.E1M1AimIteration
