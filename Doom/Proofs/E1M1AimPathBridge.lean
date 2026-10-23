import Doom.Proofs.E1M1AimPathOrder
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1AimPathBridge
open Verification X86 X86Memory Collision E1M1SelectionHistory
open E1M1HistoryDispatch (Selection)
open E1M1AimIteration E1M1AimSource

/-- The reached DOS callback and the source precomputed path select the same
original record. Its array index is the chronological callback count. -/
theorem selected (result path : PathResult) (work : Array Intercept)
    (seen : List Nat) (visits : Array Intercept) (resolve : Intercept → Word)
    (target sp : Word) (s : X86Control.State) (fraction : Int32) (j : Nat)
    (history : History result.collected work seen visits)
    (selection : Selection result.collected work seen resolve target sp s fraction j)
    (empty : result.visited=#[])
    (run : E1M1QuerySource.visitHits result (fun _ _ => true)=.ok path) :
    seen.length < path.visited.size ∧ path.visited[seen.length]! = work[j]! ∧
      path.visited[seen.length]! = result.collected[j]! := by
  have aligned := E1M1AimPathOrder.next_hit result path work seen visits history fraction j
    selection.chosen selection.within run
  simp only [empty,Array.size_empty,Nat.zero_add] at aligned
  exact ⟨aligned.1,aligned.2,aligned.2.trans selection.original⟩

/-- Advance the exact post-path source aiming loop using the record selected by
DOS. Hit identity is derived here rather than assumed as a source-loop premise. -/
theorem next_line (scene : Scene) (shooter : Nat) (thing : SolidThing)
    (path : PathResult) (distance : Fixed) (rest : List Nat)
    (lower upper floorSlope ceilingSlope : Fixed) (portals : Array AutoAim.Portal)
    (back : Heights) (result : PathResult) (work : Array Intercept)
    (seen : List Nat) (visits : Array Intercept) (resolve : Intercept → Word)
    (target sp : Word) (s : X86Control.State) (fraction : Int32) (j : Nat)
    (history : History result.collected work seen visits)
    (selection : Selection result.collected work seen resolve target sp s fraction j)
    (empty : result.visited=#[])
    (run : E1M1QuerySource.visitHits result (fun _ _ => true)=.ok path) (isLine : (work[j]!).isLine=true)
    (two : scene.lines[(work[j]!).id]!.twoSided=true) (backSector : scene.lines[(work[j]!).id]!.back=some back)
    (pass : max scene.lines[(work[j]!).id]!.front.floor.raw back.floor.raw <
      min scene.lines[(work[j]!).id]!.front.ceiling.raw back.ceiling.raw)
    (floorOk : scene.lines[(work[j]!).id]!.front.floor≠back.floor →
      checkedPathDiv (⟨max scene.lines[(work[j]!).id]!.front.floor.raw back.floor.raw⟩-thing.shootHeight)
        (distance*(work[j]!).frac)=.ok floorSlope)
    (ceilingOk : scene.lines[(work[j]!).id]!.front.ceiling≠back.ceiling →
      checkedPathDiv (⟨min scene.lines[(work[j]!).id]!.front.ceiling.raw back.ceiling.raw⟩-thing.shootHeight)
        (distance*(work[j]!).frac)=.ok ceilingSlope) :
    remaining scene shooter thing path distance (seen.length::rest) lower upper portals =
      if (bottomAfter scene.lines[(work[j]!).id]!.front back lower floorSlope).raw <
         (topAfter scene.lines[(work[j]!).id]!.front back upper ceilingSlope).raw then
        remaining scene shooter thing path distance rest
          (bottomAfter scene.lines[(work[j]!).id]!.front back lower floorSlope)
          (topAfter scene.lines[(work[j]!).id]!.front back upper ceilingSlope)
          (portals.push (portal scene.lines[(work[j]!).id]!.front back distance work[j]!))
      else .ok {path := stopped path (seen.length+1)} := by
  have aligned := selected result path work seen visits resolve target sp s fraction j history selection empty run
  exact E1M1AimIteration.next_line scene shooter thing path distance seen.length rest
    lower upper floorSlope ceilingSlope portals work[j]! back aligned.2.1 isLine two backSector pass floorOk ceilingOk

/-- At either normal traversal exit, the production aim suffix has no
iterations left and returns the path without inventing a target. -/
theorem finished (scene : Scene) (shooter : Nat) (thing : SolidThing)
    (path result : PathResult) (distance lower upper : Fixed) (portals : Array AutoAim.Portal)
    (work : Array Intercept) (seen : List Nat) (visits : Array Intercept)
    (history : History result.collected work seen visits) (empty : result.visited=#[])
    (done : seen.length=result.collected.size ∨
      ∃ best, E1M1InterceptMinimum.minimum work=.ok best ∧ best.1>65536)
    (run : E1M1QuerySource.visitHits result (fun _ _ => true)=.ok path) :
    path.visited.size=seen.length ∧
      remaining scene shooter thing path distance
        (List.range' seen.length (path.visited.size-seen.length)) lower upper portals = .ok {path:=path} := by
  have finish := E1M1AimPathOrder.terminal result path work seen visits history done run
  have size : path.visited.size=seen.length := by simpa only [empty,Array.size_empty,Nat.zero_add] using finish.2
  refine ⟨size,?_⟩
  rw [size,Nat.sub_self,List.range'_zero]
  rfl

end Doom.Proofs.E1M1AimPathBridge
