import Doom.Proofs.E1M1AimTraversalInvariant
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1AimPathOrder
open Collision E1M1InterceptMinimum E1M1SelectionHistory E1M1OrderedVisit E1M1OrderedTraversal
open E1M1InterceptMark (consume)

/-- Replaying any admitted selection history reaches the corresponding suffix
of the production all-accepting visitor, with its original iteration budget. -/
theorem replay (initial work : Array Intercept) (seen : List Nat) (visits : Array Intercept)
    (history : History initial work seen visits) (result : PathResult) :
    walk initial.size result initial (fun _ _ => true) =
      walk (initial.size-seen.length) {result with visited:=result.visited++visits}
        work (fun _ _ => true) := by
  induction history with
  | nil => simp
  | @push work seen visits prior distance j chosen within ih =>
    rw [ih]
    have budget := E1M1TraversalBudget.remaining_step prior distance j chosen within
    have fuel : initial.size-seen.length = (initial.size-seen.length-1)+1 := by omega
    rw [fuel,continue_step _ _ _ _ distance j chosen within (by rfl)]
    rw [← budget.2]
    congr 1
    simp only [appended,Array.append_push]

/-- Later iterations only append to the log. This is about the actual source
visitor; no sorting algorithm or independently specified path is substituted. -/
theorem suffix (fuel : Nat) (result : PathResult) (work : Array Intercept) :
    ∃ out tail, walk fuel result work (fun _ _ => true)=.ok out ∧
      out.visited=result.visited++tail := by
  induction fuel generalizing result work with
  | zero => exact ⟨result,#[],rfl,by simp⟩
  | succ fuel ih =>
    let best := selectFrom work work.size 0 (2147483647,none)
    have selected : minimum work=.ok best := minimum_replay work
    by_cases far : best.1>65536
    · exact ⟨result,#[],range_step fuel result work _ best selected far,by simp⟩
    · obtain ⟨j,chosen,_⟩ := E1M1InterceptGate.admitted work best selected far
      have pair : best=(best.1,some j) := Prod.ext rfl chosen
      have chosen' := selected.trans (congrArg Except.ok pair)
      obtain ⟨out,tail,run,log⟩ := ih (appended result work[j]!) (consume work j)
      refine ⟨out,#[work[j]!]++tail,
        (continue_step fuel result work _ best.1 j chosen' far rfl).trans run,?_⟩
      simpa only [appended,Array.push_eq_append,Array.append_assoc] using log

/-- Every admitted next selection is present at exactly its callback index in
Lean's precomputed all-hit path, including tied distances and original records. -/
theorem next_hit (result out : PathResult) (work : Array Intercept)
    (seen : List Nat) (visits : Array Intercept)
    (history : History result.collected work seen visits)
    (distance : Int32) (j : Nat)
    (chosen : minimum work=.ok (distance,some j)) (within : ¬distance>65536)
    (run : E1M1QuerySource.visitHits result (fun _ _ => true)=.ok out) :
    result.visited.size+seen.length < out.visited.size ∧
      out.visited[result.visited.size+seen.length]! = work[j]! := by
  rw [live_walk,replay _ _ _ _ history] at run
  have budget := E1M1TraversalBudget.remaining_step history distance j chosen within
  have fuel : result.collected.size-seen.length = (result.collected.size-seen.length-1)+1 := by omega
  rw [fuel,continue_step _ _ _ _ distance j chosen within rfl] at run
  obtain ⟨final,tail,done,log⟩ := suffix (result.collected.size-seen.length-1)
    (appended {result with visited:=result.visited++visits} work[j]!) (consume work j)
  have eq : final=out := by rw [run] at done; exact (Except.ok.inj done).symm
  subst final
  have size := count history
  simp only [appended] at log
  rw [log]
  constructor
  · simp only [Array.size_append,Array.size_push]; omega
  · simp only [← size,← Array.size_append]
    rw [getElem!_pos _ _ (by simp only [Array.size_append,Array.size_push]; omega),Array.getElem_append_left (by simp),Array.getElem_push_eq]

/-- Both normal DOS traversal exits exhaust the source all-hit log: consuming
all records, or rejecting the remaining minimum beyond the query range. -/
theorem terminal (result out : PathResult) (work : Array Intercept)
    (seen : List Nat) (visits : Array Intercept)
    (history : History result.collected work seen visits)
    (done : seen.length=result.collected.size ∨
      ∃ best, minimum work=.ok best ∧ best.1>65536)
    (run : E1M1QuerySource.visitHits result (fun _ _ => true)=.ok out) :
    out.visited=result.visited++visits ∧
      out.visited.size=result.visited.size+seen.length := by
  rw [live_walk,replay _ _ _ _ history] at run
  have finish : walk (result.collected.size-seen.length)
      {result with visited:=result.visited++visits} work (fun _ _ => true) =
      .ok {result with visited:=result.visited++visits} := by
    rcases done with exhausted|⟨best,chosen,far⟩
    · simp only [exhausted,Nat.sub_self,walk]
    · cases fuel : result.collected.size-seen.length with
      | zero => rfl
      | succ n => exact range_step n _ work _ best chosen far
  have eq := Except.ok.inj (run.symm.trans finish)
  rw [eq]
  exact ⟨rfl,by simp only [Array.size_append,count history]⟩

end Doom.Proofs.E1M1AimPathOrder
