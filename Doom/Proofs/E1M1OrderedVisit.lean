import Doom.Proofs.E1M1AimRepeatSource
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1OrderedVisit
open Collision E1M1InterceptMinimum
open E1M1InterceptMark (consume)

abbrev State := Option PathResult × PathResult × Array Intercept

def step (visit : Intercept → Nat → Bool) (_ : Nat) (state : State) : Except String (ForInStep State) := do
  let mut result := state.2.1
  let work := state.2.2
  let (distance,chosen) ← minimum work
  if distance > 65536 then return .done (none,result,work)
  let some i := chosen | throw "path: missing finite intercept"
  let hit := work[i]!
  result := { result with visited := result.visited.push hit }
  if !visit hit (result.visited.size-1) then
    return .done (some {result with completed:=false},result,work)
  return .yield (none,result,consume work i)

def finish (state : State) : PathResult := state.1.getD state.2.1

def folded (fuel : Nat) (result : PathResult) (work : Array Intercept)
    (visit : Intercept → Nat → Bool) : Except String PathResult := do
  let state ← forIn (List.range' 0 fuel) (none,result,work) (step visit)
  return finish state

/-- Extract the exact mutable production loop, including early callback return. -/
theorem live (result : PathResult) (visit : Intercept → Nat → Bool) :
    E1M1QuerySource.visitHits result visit=folded result.collected.size result result.collected visit := by
  rw [E1M1InterceptMinimum.live]
  simp only [withMinimum,folded,Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  congr 1
  funext state
  unfold finish
  cases state.1 <;> rfl

/-- Structural recursion exposes precisely the remaining traversal iterations. -/
def walk : Nat → PathResult → Array Intercept → (Intercept → Nat → Bool) → Except String PathResult
  | 0,result,_,_ => .ok result
  | fuel+1,result,work,visit => do
    let (distance,chosen) ← minimum work
    if distance > 65536 then return result
    let some i := chosen | throw "path: missing finite intercept"
    let hit := work[i]!
    let result := {result with visited:=result.visited.push hit}
    if !visit hit (result.visited.size-1) then return {result with completed:=false}
    walk fuel result (consume work i) visit

theorem replay (fuel start : Nat) (result : PathResult) (work : Array Intercept)
    (visit : Intercept → Nat → Bool) :
    (do let state ← forIn (List.range' start fuel) (none,result,work) (step visit)
        pure (finish state) : Except String PathResult) = walk fuel result work visit := by
  induction fuel generalizing start result work with
  | zero => simp [walk,finish]; rfl
  | succ fuel ih =>
    simp only [List.range'_succ,List.forIn_cons,step,walk]
    cases hm : minimum work with
    | error e => rfl
    | ok best =>
      rcases best with ⟨distance,chosen⟩
      simp only [Except.bind,bind,pure,Except.pure]
      by_cases far : distance>65536
      · simp [far,finish]
      · simp only [if_neg far]
        cases chosen with
        | none => rfl
        | some i =>
          simp only [Array.size_push,Nat.add_sub_cancel]
          cases hv : visit work[i]! result.visited.size with
          | false => simp [hv,finish]
          | true => simpa [hv,finish,Except.bind,Functor.map,Except.map] using
              (ih (start+1) {result with visited:=result.visited.push work[i]!} (consume work i))

/-- The finite recursive traversal is the live ordered visitor, not a new sort. -/
theorem live_walk (result : PathResult) (visit : Intercept → Nat → Bool) :
    E1M1QuerySource.visitHits result visit=walk result.collected.size result result.collected visit := by
  rw [live]
  exact replay _ 0 _ _ _
end Doom.Proofs.E1M1OrderedVisit
