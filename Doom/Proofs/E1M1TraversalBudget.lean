import Doom.Proofs.E1M1OrderedTraversal
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1TraversalBudget
open Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1SelectionHistory E1M1InterceptMinimum
open E1M1InterceptMark (consume)
open E1M1AimNextSelection (head)
attribute [local irreducible] load32 store32

theorem capacity {initial work : Array Intercept} {seen : List Nat} {visits : Array Intercept}
    (history : History initial work seen visits) : seen.length≤initial.size := by
  have bound := (distinct history).length_le_of_subset (l₂:=List.range initial.size) (by
    intro i hi
    exact List.mem_range.mpr ((image history).inside i hi))
  simpa only [List.length_range] using bound

theorem remaining_step {initial work : Array Intercept} {seen : List Nat} {visits : Array Intercept}
    (history : History initial work seen visits) (distance : Int32) (j : Nat)
    (chosen : minimum work=.ok (distance,some j)) (within : ¬distance>65536) :
    0<initial.size-seen.length ∧
    initial.size-seen.length-1=initial.size-(j::seen).length := by
  have bound := capacity (History.push history distance j chosen within)
  simp only [List.length_cons] at bound ⊢
  omega

/-- The production visitor passes the size of the prior log, including any
initial visits, rather than the record-buffer index or reversed-history index. -/
theorem callback_index {initial work priorVisits visits : Array Intercept} {seen : List Nat}
    (history : History initial work seen visits) (result : PathResult)
    (log : result.visited=priorVisits++visits) :
    result.visited.size=priorVisits.size+seen.length := by
  rw [log,Array.size_append,count history]

/-- Relate the original repeat head to the remaining source iteration budget.
The original zero-budget case still decrements ESI to MAXUINT before exiting. -/
theorem head_budget (s : X86Memory.State) (f : Option Flags)
    (initial work : Array Intercept) (seen : List Nat) (visits : Array Intercept)
    (history : History initial work seen visits) (bounded : initial.size≤128)
    (counter : s.regs 6=BitVec.ofNat 32 (initial.size-seen.length)) :
    X86CodeMemory.Prefix FloorCaller.cm E1M1AimRepeatProgram.program [] 4 ⟨s,f,0x2c83a⟩ (head s) ∧
    (head s).pc=(if seen.length=initial.size then 0x2c887 else 0x2c841) ∧
    (if seen.length=initial.size then (head s).core.regs 6=0xffffffff
     else (head s).core.regs 6=BitVec.ofNat 32 (initial.size-seen.length-1) ∧
       ((head s).core.regs 6).toNat + seen.length + 1 = initial.size) := by
  have cap := capacity history
  have small : initial.size-seen.length<2^32 := by omega
  have zero : BitVec.ofNat 32 (initial.size-seen.length)=(0#32) ↔ seen.length=initial.size := by
    constructor
    · intro h
      have h := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small] at h
      omega
    · intro eq
      rw [eq,Nat.sub_self]
  refine ⟨E1M1AimRepeatProgram.head_execution s f,?_,?_⟩
  · simp only [head,counter]
    change (if BitVec.ofNat 32 (initial.size-seen.length)=(0#32) then _ else _)=_
    simp only [zero]
  · by_cases exhausted : seen.length=initial.size
    · simp [head,put,write,counter,exhausted]
    · have positive : 1≤initial.size-seen.length := by omega
      simp only [if_neg exhausted]
      have reg : (head s).core.regs 6=BitVec.ofNat 32 (initial.size-seen.length-1) := by
        change s.regs 6-1=_
        rw [counter]
        exact BitVec.ofNat_sub_ofNat_of_le _ 1 (by decide) positive
      refine ⟨reg,?_⟩
      rw [reg]
      simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show initial.size-seen.length-1<2^32 by omega)]
      omega

/-- The callback and parent restore the count used by the budget theorem.
This starts at their previously proved actual resume state; scan/callback entry
contracts for arbitrary subsequent iterations are still a separate obligation. -/
theorem resumed_budget (s : X86Memory.State) (hit : Intercept) (line front back ff fc bf bc : Word)
    (h : E1M1AimMapped.Inputs s hit line front back ff fc bf bc)
    (returnSafe : E1M1AimReturnFrame.Safe s) (cursorSafe : E1M1AimRecordFrame.ReadSafe s 0x2c028)
    (go : (E1M1AimWindow.result s).core.regs 0≠0)
    (initial work : Array Intercept) (seen : List Nat) (visits : Array Intercept)
    (history : History initial work seen visits) (bounded : initial.size≤128)
    (counter : s.regs 6=BitVec.ofNat 32 (initial.size-seen.length)) :
    X86CodeMemory.Prefix FloorCaller.cm E1M1AimRepeatProgram.program [] 4
      (E1M1AimResume.result s) (head (E1M1AimResume.result s).core) ∧
    (head (E1M1AimResume.result s).core).pc=(if seen.length=initial.size then 0x2c887 else 0x2c841) := by
  have restored := (E1M1AimRecordFrame.registers s hit line front back ff fc bf bc h returnSafe cursorSafe).2.2.1
  have budget := head_budget (E1M1AimResume.result s).core (E1M1AimResume.result s).flags
    initial work seen visits history bounded (restored.trans counter)
  have pc : (E1M1AimResume.result s).pc=0x2c83a := by
    simp only [E1M1AimResume.result,OriginalInterceptGate.resumed,if_neg go]
  rw [OriginalPathXStep.at_pc _ _ pc] at budget
  exact ⟨budget.1,budget.2.1⟩
end Doom.Proofs.E1M1TraversalBudget
