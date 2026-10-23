import Doom.Proofs.E1M1SelectionHistory
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1OrderedTraversal
open Collision E1M1InterceptMinimum E1M1OrderedVisit E1M1SelectionHistory
open E1M1InterceptMark (consume)

def appended (result : PathResult) (hit : Intercept) : PathResult :=
  {result with visited:=result.visited.push hit}

theorem continue_step (fuel : Nat) (result : PathResult) (work : Array Intercept)
    (visit : Intercept → Nat → Bool) (distance : Int32) (j : Nat)
    (selected : minimum work=.ok (distance,some j)) (within : ¬distance>65536)
    (accept : visit work[j]! result.visited.size=true) :
    walk (fuel+1) result work visit=walk fuel (appended result work[j]!) (consume work j) visit := by
  simp [walk,selected,within,accept,appended,bind,pure,Except.bind,Except.pure]

theorem stop_step (fuel : Nat) (result : PathResult) (work : Array Intercept)
    (visit : Intercept → Nat → Bool) (distance : Int32) (j : Nat)
    (selected : minimum work=.ok (distance,some j)) (within : ¬distance>65536)
    (reject : visit work[j]! result.visited.size=false) :
    walk (fuel+1) result work visit=.ok {appended result work[j]! with completed:=false} := by
  simp [walk,selected,within,reject,appended,bind,pure,Except.bind,Except.pure]

theorem range_step (fuel : Nat) (result : PathResult) (work : Array Intercept)
    (visit : Intercept → Nat → Bool) (best : Best)
    (selected : minimum work=.ok best) (far : best.1>65536) :
    walk (fuel+1) result work visit=.ok result := by
  simp [walk,selected,far,bind,pure,Except.bind,Except.pure]

/-- Induct over the actual remaining source iterations. Selection history and
visit bookkeeping extend together; the initial collection is never rewritten.
A final rejected callback is logged, but its logical mark is not a machine store. -/
theorem traversal (fuel : Nat) (initial work priorVisits visits : Array Intercept) (seen : List Nat)
    (result : PathResult) (visit : Intercept → Nat → Bool)
    (history : History initial work seen visits) (log : result.visited=priorVisits++visits) :
    ∃ out finalWork finalSeen finalVisits,
      walk fuel result work visit=.ok out ∧ History initial finalWork finalSeen finalVisits ∧
      out.visited=priorVisits++finalVisits ∧ seen.length≤finalSeen.length ∧
      finalSeen.length≤seen.length+fuel ∧ out.collected=result.collected := by
  induction fuel generalizing work visits seen result with
  | zero => exact ⟨result,work,seen,visits,rfl,history,log,by omega,by omega,rfl⟩
  | succ fuel ih =>
    let best := selectFrom work work.size 0 (2147483647,none)
    have selected : minimum work=.ok best := minimum_replay work
    by_cases far : best.1>65536
    · exact ⟨result,work,seen,visits,range_step fuel result work visit best selected far,
        history,log,by omega,by omega,rfl⟩
    · obtain ⟨j,chosen,inside⟩ := E1M1InterceptGate.admitted work best selected far
      have pair : best=(best.1,some j) := Prod.ext rfl chosen
      have selected' : minimum work=.ok (best.1,some j) := selected.trans (congrArg Except.ok pair)
      have nextHistory := History.push history best.1 j selected' far
      have nextLog : (appended result work[j]!).visited=priorVisits++(visits.push work[j]!) := by
        change result.visited.push work[j]! = _
        rw [log,Array.append_push]
      cases accepted : visit work[j]! result.visited.size with
      | false =>
        exact ⟨{appended result work[j]! with completed:=false},consume work j,j::seen,visits.push work[j]!,
          stop_step fuel result work visit best.1 j selected' far accepted,nextHistory,nextLog,
          by simp,by simp,rfl⟩
      | true =>
        obtain ⟨out,fw,fs,fv,run,done,finalLog,lower,upper,collected⟩ :=
          ih (consume work j) (visits.push work[j]!) (j::seen) (appended result work[j]!) nextHistory nextLog
        exact ⟨out,fw,fs,fv,(continue_step fuel result work visit best.1 j selected' far accepted).trans run,
          done,finalLog,(by simp only [List.length_cons] at lower; omega),
          (by simp only [List.length_cons] at upper; omega),collected⟩

/-- For any callback and any finite initial collection, the live ordered visitor
returns a unique-index prefix of original records in the exact strict-min order.
This proves source traversal bookkeeping, not the callback's DOS equivalence. -/
theorem live_history (initial : PathResult) (visit : Intercept → Nat → Bool) :
    ∃ out work seen visits,
      E1M1QuerySource.visitHits initial visit=.ok out ∧
      History initial.collected work seen visits ∧ seen.Nodup ∧
      out.visited=initial.visited++visits ∧ visits.toList=seen.reverse.map (fun i => initial.collected[i]!) ∧
      visits.size=seen.length ∧ seen.length≤initial.collected.size ∧ out.collected=initial.collected := by
  obtain ⟨out,work,seen,visits,run,history,log,_,bound,collected⟩ :=
    traversal initial.collected.size initial.collected initial.collected initial.visited #[] [] initial visit
      (.nil) (by simp)
  rw [← E1M1OrderedVisit.live_walk] at run
  exact ⟨out,work,seen,visits,run,history,distinct history,log,original_log history,count history,
    by simpa using bound,collected⟩
end Doom.Proofs.E1M1OrderedTraversal
