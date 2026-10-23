import Doom.Proofs.OriginalInterceptMinimum
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1InterceptMinimum
open Collision
abbrev Best := Int32 × Option Nat

def update (hits : Array Intercept) (best : Best) (i : Nat) : Best :=
  if hits[i]!.frac.raw < best.1 then (hits[i]!.frac.raw,some i) else best

/-- Exact inner loop used by the production ordered-hit visitor. -/
def minimum (hits : Array Intercept) : Except String Best :=
  forIn [:hits.size] ((2147483647 : Int32),none) fun i best =>
    if hits[i]!.frac.raw < best.1 then pure (.yield (hits[i]!.frac.raw,some i)) else pure (.yield best)

def withMinimum (choose : Array Intercept → Except String Best) (initial : PathResult) (visit : Intercept → Nat → Bool) : Except String PathResult := do
  let mut result := initial
  -- Use the original strict-min selection rather than a sort with unspecified ties.
  let mut work := result.collected
  for _ in [:work.size] do
    let (distance,chosen) ← choose work
    if distance > 65536 then break
    let some i := chosen | throw "path: missing finite intercept"
    let hit := work[i]!
    result := { result with visited := result.visited.push hit }
    if !visit hit (result.visited.size - 1) then return { result with completed := false }
    work := work.set! i { hit with frac := ⟨2147483647⟩ }
  return result


attribute [local irreducible] ForIn.forIn Array.push Array.set!
/-- Exposing the selector preserves the complete live visitor tail. -/
theorem live (r : PathResult) (visit : Intercept → Nat → Bool) :
    E1M1QuerySource.visitHits r visit=withMinimum minimum r visit := by
  set_option smartUnfolding false in rfl
attribute [local semireducible] ForIn.forIn

/-- Structural replay keeps strict comparison, signed fractions and tie order. -/
def selectFrom (hits : Array Intercept) : Nat → Nat → Best → Best
  | 0,_,best => best
  | fuel+1,i,best => selectFrom hits fuel (i+1) (update hits best i)

theorem replay (hits : Array Intercept) (fuel start : Nat) (best : Best) :
    (forIn (List.range' start fuel) best fun i best =>
      pure (.yield (update hits best i)) : Except String Best)=.ok (selectFrom hits fuel start best) := by
  induction fuel generalizing start best with
  | zero => simp [selectFrom]; rfl
  | succ fuel ih =>
    simpa only [List.range'_succ,List.forIn_cons,pure_bind,selectFrom] using
      ih (start+1) (update hits best start)

theorem minimum_replay (hits : Array Intercept) :
    minimum hits=.ok (selectFrom hits hits.size 0 (2147483647,none)) := by
  have body : (fun i best => if hits[i]!.frac.raw < best.1 then pure (.yield (hits[i]!.frac.raw,some i)) else pure (.yield best)) =
      (fun i best => pure (.yield (update hits best i)) : Nat → Best → Except String (ForInStep Best)) := by
    funext i best
    unfold update
    split <;> rfl
  unfold minimum
  rw [body,Std.Legacy.Range.forIn_eq_forIn_range']
  simpa [Std.Legacy.Range.size] using replay hits hits.size 0 (2147483647,none)

/-- An equal-distance later hit cannot replace the earlier choice. -/
theorem tie (hits : Array Intercept) (best : Best) (i : Nat)
    (same : hits[i]!.frac.raw=best.1) : update hits best i=best := by
  simp [update,same]

private theorem none_origin (hits : Array Intercept) (fuel i : Nat) (best : Best)
    (noneSelected : (selectFrom hits fuel i best).2=none) :
    best.2=none ∧ (selectFrom hits fuel i best).1=best.1 := by
  induction fuel generalizing i best with
  | zero => exact ⟨noneSelected,rfl⟩
  | succ fuel ih =>
    have h := ih (i+1) (update hits best i) noneSelected
    by_cases better : hits[i]!.frac.raw<best.1
    · simp [update,better] at h
    · simpa only [selectFrom,update,if_neg better] using h

/-- No selected hit means the sentinel survived. In particular it cannot pass
the live aiming query's 65536 distance cutoff. -/
theorem minimum_none (hits : Array Intercept) (distance : Int32)
    (noneSelected : minimum hits=.ok (distance,none)) : distance=2147483647 := by
  rw [minimum_replay] at noneSelected
  have eq := Except.ok.inj noneSelected
  have origin := (none_origin hits hits.size 0 (2147483647,none) (congrArg Prod.snd eq)).2
  exact (congrArg Prod.fst eq).symm.trans origin
end Doom.Proofs.E1M1InterceptMinimum
