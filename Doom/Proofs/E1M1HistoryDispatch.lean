import Doom.Proofs.E1M1NextCallbackState
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1HistoryDispatch
open Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1MinimumScan (address)
open E1M1InterceptMinimum (Best minimum)
open E1M1SelectionHistory
open E1M1InterceptMark (consume)
open E1M1AimRepeatProgram (program ReadFrame)
open E1M1AimNextSelection (head)
open E1M1OrderedTraversal (appended)
open E1M1OrderedVisit (walk)
attribute [local irreducible] load32 store32

/-- The reached callback still reads the unmarked original hit. Its counter is
already decremented for this invocation; no callback outcome is assumed here. -/
structure Selection (initial work : Array Intercept) (seen : List Nat)
    (resolve : Intercept → Word) (target sp : Word) (out : X86Control.State)
    (distance : Int32) (j : Nat) : Prop where
  ready : E1M1NextCallbackState.Ready work resolve target sp out
  chosen : minimum work=.ok (distance,some j)
  within : ¬distance>65536
  inside : j<initial.size
  fresh : j∉seen
  original : work[j]! = initial[j]!
  argument : out.core.regs 0=address j
  counter : out.core.regs 6=BitVec.ofNat 32 (initial.size-(j::seen).length)
  maximum : out.core.regs 7=65536

def Outcome (s : X86Memory.State) (initial work : Array Intercept) (seen : List Nat)
    (resolve : Intercept → Word) (out : X86Control.State) : Prop :=
  (seen.length=initial.size ∧ out=head s ∧ out.core.regs 6=0xffffffff) ∨
  (∃ best, minimum work=.ok best ∧ best.1>65536 ∧ out.pc=0x2c887 ∧
    out.core.regs 6=BitVec.ofNat 32 (initial.size-seen.length-1)) ∨
  (∃ distance j, Selection initial work seen resolve
    (load32 s.memory (s.regs 4)) (s.regs 4) out distance j)

/-- Join source selection history to the original repeat head, full scan and
indirect CALL. This derives the next entry facts from one continuous execution. -/
theorem execution (s : X86Memory.State) (f : Option Flags)
    (initial work : Array Intercept) (seen : List Nat) (visits : Array Intercept)
    (resolve : Intercept → Word) (history : History initial work seen visits)
    (bounded : initial.size≤128)
    (counter : s.regs 6=BitVec.ofNat 32 (initial.size-seen.length))
    (limit : s.regs 1=address work.size)
    (encoded : OriginalLineFinish.Encodes s.memory 0x2ba20 resolve work)
    (maximum : s.regs 7=65536) (targetSafe : Apart (s.regs 4) 0x2c028)
    (cursorSafe : Apart 0x2c028 (s.regs 4-4))
    (recordSafe : ∀ i<work.size, ∀ off∈[(0#32),4,8],
      Apart (OriginalLineCollection.slot 0x2ba20 i off) (s.regs 4-4)) :
    ∃ n≤13+7*work.size, ∃ out,
      X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2c83a⟩ out ∧
      ReadFrame s out ∧ Outcome s initial work seen resolve out := by
  have image := E1M1SelectionHistory.image history
  have size := image.size
  obtain ⟨run,pc,budget⟩ := E1M1TraversalBudget.head_budget s f initial work seen visits history bounded counter
  by_cases exhausted : seen.length=initial.size
  · exact ⟨4,by omega,head s,run,(by intro a hc hs; rfl),
      Or.inl ⟨exhausted,rfl,by simpa only [if_pos exhausted] using budget⟩⟩
  · have cap := E1M1TraversalBudget.capacity history
    have nonempty : work.size≠0 := by have := image.size; omega
    have budget := (if_neg exhausted ▸ budget).1
    obtain ⟨n,hn,out,tail,done,frame,count,maxOut⟩ := E1M1NextCallbackState.dispatch
      (head s) work resolve (by omega)
      (by simpa [head,put,write] using limit) encoded
      (by simpa [head,put,write] using maximum)
      (by simpa only [if_neg exhausted,if_neg nonempty] using pc)
      targetSafe cursorSafe recordSafe
    refine ⟨4+n,by omega,out,E1M1PspriteStep.prefix_trans run tail,frame,?_⟩
    rcases done with empty|far|ready
    · exact False.elim (nonempty empty.1)
    · obtain ⟨best,chosen,far,exit⟩ := far
      exact Or.inr (Or.inl ⟨best,chosen,far,exit,count.trans budget⟩)
    · obtain ⟨best,j,chosen,within,index,inside,arg⟩ := ready.selected
      have pair : best=(best.1,some j) := Prod.ext rfl index
      have choice : minimum work=.ok (best.1,some j) := chosen.trans (congrArg Except.ok pair)
      have fresh := E1M1SelectionHistory.fresh initial work seen image best.1 j choice within
      have remaining := (E1M1TraversalBudget.remaining_step history best.1 j choice within).2
      exact Or.inr (Or.inr ⟨best.1,j,ready,choice,within,(by omega),fresh,
        image.untouched j fresh,arg,(count.trans budget).trans (congrArg (BitVec.ofNat 32) remaining),maxOut⟩)

/-- For the reached machine argument, the source calls the same original hit at
the same visit count. A true callback advances the source history and fuel.
This statement does not claim the callback itself has executed on the machine. -/
theorem source_continue (initial work priorVisits visits : Array Intercept) (seen : List Nat)
    (resolve : Intercept → Word) (target sp : Word) (out : X86Control.State)
    (distance : Int32) (j : Nat) (selection : Selection initial work seen resolve target sp out distance j)
    (history : History initial work seen visits) (result : PathResult)
    (log : result.visited=priorVisits++visits) (visit : Intercept → Nat → Bool)
    (accept : visit initial[j]! (priorVisits.size+seen.length)=true) :
    walk (initial.size-seen.length) result work visit=
      walk (initial.size-(j::seen).length) (appended result initial[j]!) (consume work j) visit ∧
    History initial (consume work j) (j::seen) (visits.push initial[j]!) ∧
    (appended result initial[j]!).visited=priorVisits++(visits.push initial[j]!) := by
  have index := E1M1TraversalBudget.callback_index history result log
  have ⟨positive,remaining⟩ := E1M1TraversalBudget.remaining_step history distance j selection.chosen selection.within
  have fuel : initial.size-seen.length=(initial.size-(j::seen).length)+1 := by omega
  refine ⟨?_,?_,?_⟩
  · rw [fuel]
    simpa only [selection.original] using E1M1OrderedTraversal.continue_step
      (initial.size-(j::seen).length) result work visit distance j selection.chosen selection.within
      (by rw [selection.original,index]; exact accept)
  · simpa only [selection.original] using History.push history distance j selection.chosen selection.within
  · change result.visited.push initial[j]! = _
    rw [log,Array.append_push]

/-- A false callback includes the selected original hit in the source log and
stops; it does not execute the continuing-branch sentinel store. -/
theorem source_stop (initial work priorVisits visits : Array Intercept) (seen : List Nat)
    (resolve : Intercept → Word) (target sp : Word) (out : X86Control.State)
    (distance : Int32) (j : Nat) (selection : Selection initial work seen resolve target sp out distance j)
    (history : History initial work seen visits) (result : PathResult)
    (log : result.visited=priorVisits++visits) (visit : Intercept → Nat → Bool)
    (reject : visit initial[j]! (priorVisits.size+seen.length)=false) :
    walk (initial.size-seen.length) result work visit=
      .ok {appended result initial[j]! with completed:=false} := by
  have index := E1M1TraversalBudget.callback_index history result log
  have positive := (E1M1TraversalBudget.remaining_step history distance j selection.chosen selection.within).1
  have fuel : initial.size-seen.length=(initial.size-seen.length-1)+1 := by omega
  rw [fuel]
  simpa only [selection.original] using E1M1OrderedTraversal.stop_step
    (initial.size-seen.length-1) result work visit distance j selection.chosen selection.within
    (by rw [selection.original,index]; exact reject)
end Doom.Proofs.E1M1HistoryDispatch
