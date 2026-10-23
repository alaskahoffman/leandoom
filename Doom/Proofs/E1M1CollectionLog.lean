import Doom.Proofs.E1M1CellLineSource
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1CollectionLog
open Collision

def log (block : Bool × Int32 × Int32) (r : PathResult) : PathResult :=
  { r with blocks:=r.blocks.push block }

theorem append_log (b : Bool × Int32 × Int32) (r : PathResult) (hit : Intercept) :
    appendIntercept (log b r) hit=(appendIntercept r hit).map (log b) := by
  unfold appendIntercept log
  split <;> rfl

/-- Logging changes neither duplicate checks, intersections nor capacity. Errors
are retained, and successful results acquire exactly the same log entry. -/
theorem line_log_list (b : Bool × Int32 × Int32) (trace : Divline) (lines : Array Line)
    (ids : List Nat) (seen : Array Bool) (r : PathResult) :
    E1M1LineSourceLoop.lineCell trace lines ids.toArray seen (log b r)=
      (E1M1LineSourceLoop.lineCell trace lines ids.toArray seen r).map
        (fun out => (out.1,log b out.2)) := by
  unfold E1M1LineSourceLoop.lineCell
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
              simp only [Bind.bind,Except.bind,append_log]
              cases appended : appendIntercept r ⟨frac,true,id⟩ with
              | error e => rfl
              | ok after => exact ih (seen.set! id true) after

theorem line_log (b : Bool × Int32 × Int32) (trace : Divline) (lines : Array Line)
    (ids : Array Nat) (seen : Array Bool) (r : PathResult) :
    E1M1LineSourceLoop.lineCell trace lines ids seen (log b r)=
      (E1M1LineSourceLoop.lineCell trace lines ids seen r).map
        (fun out => (out.1,log b out.2)) := by
  simpa using line_log_list b trace lines ids.toList seen r

/-- Diagnostic block logs do not alter the machine record/visit relation. -/
theorem state_log (q : E1M1CellWalkInvariant.Context) (s : Verification.X86Control.State)
    (r : PathResult) (seen : Array Bool) (b : Bool × Int32 × Int32)
    (h : E1M1CellWalkInvariant.State q s r seen) :
    E1M1CellWalkInvariant.State q s (log b r) seen :=
  ⟨h.stack,h.maps,h.tracked,h.represented,h.size⟩
end Doom.Proofs.E1M1CollectionLog
