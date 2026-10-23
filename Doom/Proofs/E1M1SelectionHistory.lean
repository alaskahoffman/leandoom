import Doom.Proofs.E1M1OrderedVisit
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1SelectionHistory
open Collision E1M1InterceptMinimum
open E1M1InterceptMark (consume)

/-- A selected minimum's value belongs to that selected record. -/
theorem scan_value (hits : Array Intercept) (fuel start : Nat) (best : Best)
    (initial : ∀ j, best.2=some j → hits[j]!.frac.raw=best.1) :
    ∀ j, (selectFrom hits fuel start best).2=some j →
      hits[j]!.frac.raw=(selectFrom hits fuel start best).1 := by
  induction fuel generalizing start best with
  | zero => exact initial
  | succ fuel ih =>
    apply ih (start+1) (update hits best start)
    intro j chosen
    by_cases better : hits[start]!.frac.raw<best.1
    · have same : start=j := by simpa [update,better] using chosen
      subst j
      simp [update,better]
    · simpa only [update,if_neg better] using initial j (by simpa [update,better] using chosen)

theorem selected_value (hits : Array Intercept) (distance : Int32) (j : Nat)
    (chosen : minimum hits=.ok (distance,some j)) : hits[j]!.frac.raw=distance := by
  have run := minimum_replay hits
  rw [chosen] at run
  have eq := (Except.ok.inj run).symm
  have val := scan_value hits hits.size 0 (2147483647,none) (by intro j bad; cases bad)
  rw [eq] at val
  exact val j rfl

/-- The buffer after a sequence of marks: old records stay intact at unvisited
indices, and visited fractions are MAXINT. Indices are stored newest first. -/
structure Image (initial work : Array Intercept) (seen : List Nat) : Prop where
  size : work.size=initial.size
  inside : ∀ i∈seen, i<initial.size
  marked : ∀ i∈seen, work[i]!.frac.raw=2147483647
  untouched : ∀ i, i∉seen → work[i]! = initial[i]!

theorem initial_image (initial : Array Intercept) : Image initial initial [] := by
  exact ⟨rfl,by simp,by simp,by simp⟩

theorem mark_image (initial work : Array Intercept) (seen : List Nat)
    (image : Image initial work seen) (j : Nat) (inside : j<work.size) :
    Image initial (consume work j) (j::seen) := by
  refine ⟨(E1M1InterceptMark.size work j).trans image.size,?_,?_,?_⟩
  · intro i hi
    rcases List.mem_cons.mp hi with rfl|hi
    · rw [←image.size]; exact inside
    · exact image.inside i hi
  · intro i hi
    by_cases same : j=i
    · subst i
      rw [E1M1InterceptMark.selected work j inside]
    · rw [E1M1InterceptMark.other work j i same]
      exact image.marked i (by simpa [Ne.symm same] using hi)
  · intro i unseen
    have different : j≠i := by intro eq; subst i; simp at unseen
    rw [E1M1InterceptMark.other work j i different]
    exact image.untouched i (by simp_all)

/-- A consumed MAXINT record cannot be selected again within the aiming range. -/
theorem fresh (initial work : Array Intercept) (seen : List Nat)
    (image : Image initial work seen) (distance : Int32) (j : Nat)
    (chosen : minimum work=.ok (distance,some j)) (within : ¬distance>65536) : j∉seen := by
  intro old
  have val := selected_value work distance j chosen
  rw [image.marked j old] at val
  have bad : (2147483647 : Int32)>65536 := by decide
  exact within (val ▸ bad)

/-- Exact admitted selection history, including original strict tie ordering.
The associated work buffer marks every recorded selection; a stopped callback
may use the final mark only as logical bookkeeping, never as a machine claim. -/
inductive History (initial : Array Intercept) : Array Intercept → List Nat → Array Intercept → Prop
  | nil : History initial initial [] #[]
  | push {work seen visits} (prior : History initial work seen visits)
      (distance : Int32) (j : Nat)
      (chosen : minimum work=.ok (distance,some j)) (within : ¬distance>65536) :
      History initial (consume work j) (j::seen) (visits.push work[j]!)

theorem image {initial work : Array Intercept} {seen : List Nat} {visits : Array Intercept}
    (history : History initial work seen visits) : Image initial work seen := by
  induction history with
  | nil => exact initial_image _
  | @push work seen visits prior distance j chosen within ih =>
    obtain ⟨k,hk,inside⟩ := E1M1InterceptGate.admitted work (distance,some j) chosen within
    have eq : j=k := Option.some.inj hk
    subst k
    exact mark_image _ _ _ ih j inside

theorem distinct {initial work : Array Intercept} {seen : List Nat} {visits : Array Intercept}
    (history : History initial work seen visits) : seen.Nodup := by
  induction history with
  | nil => simp
  | @push work seen visits prior distance j chosen within ih =>
    exact List.nodup_cons.mpr ⟨fresh _ _ _ (image prior) distance j chosen within,ih⟩

theorem count {initial work : Array Intercept} {seen : List Nat} {visits : Array Intercept}
    (history : History initial work seen visits) : visits.size=seen.length := by
  induction history <;> simp_all

/-- The visit log contains original records, never the sentinel-marked copies. -/
theorem original_log {initial work : Array Intercept} {seen : List Nat} {visits : Array Intercept}
    (history : History initial work seen visits) :
    visits.toList=seen.reverse.map (fun i => initial[i]!) := by
  induction history with
  | nil => rfl
  | @push work seen visits prior distance j chosen within ih =>
    have same := (image prior).untouched j (fresh _ _ _ (image prior) distance j chosen within)
    simp [List.reverse_cons,ih,same]
/-- Two traversals of the same collection agree after the same number of
admitted selections, regardless of the callback that requested those selections. -/
theorem same_count {initial work₁ work₂ : Array Intercept} {seen₁ seen₂ : List Nat}
    {visits₁ visits₂ : Array Intercept}
    (first : History initial work₁ seen₁ visits₁) (second : History initial work₂ seen₂ visits₂)
    (length : seen₁.length=seen₂.length) : work₁=work₂ ∧ seen₁=seen₂ ∧ visits₁=visits₂ := by
  induction first generalizing work₂ seen₂ visits₂ with
  | nil =>
    cases second with
    | nil => exact ⟨rfl,rfl,rfl⟩
    | push prior distance j chosen within => simp at length
  | @push work seen visits prior distance j chosen within ih =>
    cases second with
    | nil => simp at length
    | @push otherWork otherSeen otherVisits otherPrior otherDistance k otherChosen otherWithin =>
      have before : seen.length=otherSeen.length := by simpa only [List.length_cons,Nat.add_right_cancel_iff] using length
      obtain ⟨rfl,rfl,rfl⟩ := ih otherPrior before
      have eq := Except.ok.inj (chosen.symm.trans otherChosen)
      have index : j=k := Option.some.inj (congrArg Prod.snd eq)
      subst k
      exact ⟨rfl,rfl,rfl⟩
end Doom.Proofs.E1M1SelectionHistory
