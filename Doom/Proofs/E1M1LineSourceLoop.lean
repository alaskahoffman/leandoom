import Doom.Proofs.E1M1LineCollect
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1LineSourceLoop
open Verification X86 X86Memory X86Control BlockSummary
open OriginalLineMixedInvariant (Candidate)

/-- The line-cell for-loop from Path.pathTraverse specialized to aiming flags 3
(no early-out bit). ID validation and lookup precede duplicate rejection, as in
the live code. Block logging and the enclosing grid loop are separate. -/
def lineCell (trace : Collision.Divline) (lines : Array Collision.Line) (ids : Array Nat)
    (seen : Array Bool) (r : Collision.PathResult) : Except String (Array Bool × Collision.PathResult) := do
  let mut seen := seen
  let mut result := r
  for id in ids do
    if id ≥ 32768 then throw "path: signed linedef index is unverified"
    let some line := lines[id]? | throw "path: invalid linedef"
    if seen[id]! then continue
    seen := seen.set! id true
    if let some frac ← Collision.lineIntercept trace line then
      result ← Collision.appendIntercept result ⟨frac,true,id⟩
  return (seen,result)

/-- Full source-loop result, including errors: no sorting or deduplication of
the input list is introduced, and its lookup-before-duplicate order is retained. -/
theorem source_collect (trace : Collision.Divline) (lines : Array Collision.Line)
    (cs : List Candidate) (seen : Array Bool) (r : Collision.PathResult)
    (traces : ∀ c∈cs, c.trace=trace) (ids : ∀ c∈cs, c.id<32768)
    (lookup : ∀ c∈cs, lines[c.id]?=some c.line) :
    lineCell trace lines (cs.map Candidate.id).toArray seen r=E1M1LineCollect.collect cs seen r := by
  unfold lineCell
  simp only [List.forIn_toArray,List.forIn_map]
  induction cs generalizing seen r with
  | nil => rfl
  | cons c rest ih =>
    have id := ids c (by simp)
    have tr := traces c (by simp)
    simp only [List.forIn_cons,E1M1LineCollect.collect,show ¬c.id≥32768 by omega,ite_false,lookup c (by simp)]
    unfold E1M1LineCollect.visit
    rw [tr]
    by_cases duplicate : seen[c.id]! =true
    · simp only [duplicate,ite_true,Bind.bind,Except.bind]
      exact ih seen r (fun d hd => traces d (by simp [hd])) (fun d hd => ids d (by simp [hd])) (fun d hd => lookup d (by simp [hd]))
    · simp only [if_neg duplicate]
      cases hit : Collision.lineIntercept trace c.line with
      | error e => rfl
      | ok value =>
        cases value with
        | none =>
          exact ih (seen.set! c.id true) r (fun d hd => traces d (by simp [hd])) (fun d hd => ids d (by simp [hd])) (fun d hd => lookup d (by simp [hd]))
        | some frac =>
          simp only [Bind.bind,Except.bind]
          cases app : Collision.appendIntercept r ⟨frac,true,c.id⟩ with
          | error e => rfl
          | ok after =>
            exact ih (seen.set! c.id true) after (fun d hd => traces d (by simp [hd])) (fun d hd => ids d (by simp [hd])) (fun d hd => lookup d (by simp [hd]))
end Doom.Proofs.E1M1LineSourceLoop
