import Doom.Proofs.OriginalLineStop
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.OriginalLineTraversal
open Verification X86 X86Memory X86Control BlockSummary
abbrev program := OriginalLineDispatch.program

/-- A finite original traversal. All callback outcomes are included. Each fresh
entry still needs its reached-state contract; invariant closure is separate.
The stop constructor is terminal and imposes no conditions on a later list item. -/
inductive Runs : X86Control.State → X86Control.State → Nat → Prop where
  | sentinel (s : X86Control.State) (pc : s.pc=0x2c57f)
      (last : OriginalLineCell.item s.core=(0xffff#16)) :
      Runs s (OriginalLineBounds.returned (OriginalLineCell.header s.core).core) 0
  | duplicate (s out : X86Control.State) (n : Nat) (pc : s.pc=0x2c57f)
      (last : OriginalLineCell.itemWord s.core≠(0xffffffff#32))
      (seen : OriginalLineCell.already (OriginalLineCell.header s.core).core)
      (tail : Runs (OriginalLineCell.visit s.core) out n) : Runs s out (n+1)
  | rejected (s out : X86Control.State) (n : Nat) (pc : s.pc=0x2c57f)
      (trace : Collision.Divline) (line : Collision.Line) (p v w : Word)
      (h : OriginalLineReject.Ready s.core trace line p v w)
      (tail : Runs (OriginalLineReject.result s.core) out n) : Runs s out (n+1)
  | crossing (s out : X86Control.State) (n : Nat) (pc : s.pc=0x2c57f)
      (trace : Collision.Divline) (line : Collision.Line) (frac : Fixed) (flags : Nat) (p v w : Word)
      (h : OriginalLineDispatch.Ready s.core trace line frac flags p v w)
      (saved : OriginalLineTail.RecordSafe (OriginalLineDispatch.view s.core) ((OriginalLineDispatch.view s.core).regs 4-(12#32)))
      (keep : frac.raw<0 ∨ (flags &&& 4 != 0 && frac.raw<65536 && line.back.isNone)=false)
      (tail : Runs (OriginalLineDispatch.result s.core) out n) : Runs s out (n+1)
  | stopped (s : X86Control.State) (pc : s.pc=0x2c57f)
      (trace : Collision.Divline) (line : Collision.Line) (frac : Fixed) (flags : Nat) (p v w : Word)
      (h : OriginalLineDispatch.Ready s.core trace line frac flags p v w)
      (stop : OriginalLineStop.Stops frac flags line) : Runs s (OriginalLineDispatch.result s.core) 1

theorem execution (s out : X86Control.State) (n : Nat) (h : Runs s out n) :
    ∃ steps≤281*n+7, X86Routine.Prefix program [] steps s out := by
  induction h with
  | sentinel s pc last =>
    have path := OriginalLineResume.sentinel_execution s.core s.flags last
    rw [OriginalPathXStep.at_pc _ _ pc] at path
    exact ⟨7,by omega,path.transfer program [] E1M1LineResume.contains_resume (by simp)⟩
  | duplicate s out n pc last seen tail ih =>
    have dup : OriginalLineResume.Duplicates 1 s := ⟨last,seen,trivial⟩
    obtain ⟨a,ha,head⟩ := OriginalLineResume.skip_execution 1 s pc dup
    have head := head.transfer program [] E1M1LineResume.contains_resume (by simp)
    obtain ⟨b,hb,next⟩ := ih
    exact ⟨a+b,by omega,OriginalGroupBounds.prefix_join head next⟩
  | rejected s out n pc trace line p v w ready tail ih =>
    obtain ⟨a,ha,head⟩ := OriginalLineReject.execution s.core trace line p v w ready s.flags
    rw [OriginalPathXStep.at_pc _ _ pc] at head
    obtain ⟨b,hb,next⟩ := ih
    exact ⟨a+b,by omega,OriginalGroupBounds.prefix_join head next⟩
  | crossing s out n pc trace line frac flags p v w ready saved keep tail ih =>
    obtain ⟨a,ha,head⟩ := OriginalLineDispatch.execution s.core trace line frac flags p v w ready s.flags
    rw [OriginalPathXStep.at_pc _ _ pc] at head
    obtain ⟨b,hb,next⟩ := ih
    exact ⟨a+b,by omega,OriginalGroupBounds.prefix_join head next⟩
  | stopped s pc trace line frac flags p v w ready stop =>
    obtain ⟨a,ha,head⟩ := OriginalLineDispatch.execution s.core trace line frac flags p v w ready s.flags
    rw [OriginalPathXStep.at_pc _ _ pc] at head
    exact ⟨a,by omega,head⟩

theorem return_value (s out : X86Control.State) (n : Nat) (h : Runs s out n) :
    out.core.regs 0=(0#32) ∨ out.core.regs 0=(1#32) := by
  induction h with
  | sentinel s pc last =>
    right
    simp [OriginalLineBounds.returned,OriginalLineBounds.r3,OriginalLineBounds.r2,OriginalLineBounds.r1,put,write]
  | duplicate s out n pc last seen tail ih => exact ih
  | rejected s out n pc trace line p v w ready tail ih => exact ih
  | crossing s out n pc trace line frac flags p v w ready saved keep tail ih => exact ih
  | stopped s pc trace line frac flags p v w ready stop =>
    exact Or.inl (OriginalLineStop.observed s.core trace line frac flags p v w ready stop).1

/-- Every admitted traversal restores the iterator's stack frame, whether its
last event is a sentinel or an early-stop callback. -/
theorem stack (s out : X86Control.State) (n : Nat) (h : Runs s out n) :
    out.core.regs 4=s.core.regs 4+(12#32) := by
  induction h with
  | sentinel s pc last =>
    simp [OriginalLineBounds.returned,OriginalLineBounds.r3,OriginalLineBounds.r2,OriginalLineBounds.r1,
      OriginalLineCell.header,OriginalLineCell.h1,put,write]
  | duplicate s out n pc last seen tail ih =>
    have keep := (OriginalLineResume.skip_observe 1 s ⟨last,seen,trivial⟩).2.2
    simp only [OriginalLineResume.skipMany] at keep
    rw [keep] at ih
    exact ih
  | rejected s out n pc trace line p v w ready tail ih =>
    rw [(OriginalLineReject.continued s.core trace line p v w ready).2.2.1] at ih
    exact ih
  | crossing s out n pc trace line frac flags p v w ready saved keep tail ih =>
    rw [(OriginalLineDispatch.continued s.core trace line frac flags p v w ready saved keep).2.2] at ih
    exact ih
  | stopped s pc trace line frac flags p v w ready stop =>
    exact (OriginalLineStop.observed s.core trace line frac flags p v w ready stop).2.1

/-- The previous crossing/duplicate loop embeds into the complete outcome
relation without any new per-entry assumptions. -/
theorem of_mixed (n : Nat) (s : X86Control.State) (pc : s.pc=0x2c57f)
    (h : OriginalLineMixed.Admitted n s)
    (last : OriginalLineCell.item (OriginalLineMixed.run n s).core=(0xffff#16)) :
    Runs s (OriginalLineBounds.returned
      (OriginalLineCell.header (OriginalLineMixed.run n s).core).core) n := by
  induction n generalizing s with
  | zero => exact .sentinel s pc last
  | succ n ih =>
    obtain ⟨item,fresh,remaining⟩ := h
    have nextpc := (OriginalLineMixed.step_execution s pc item fresh).2.1
    have tail := ih (OriginalLineMixed.step s.core) nextpc remaining last
    change Runs s (OriginalLineBounds.returned
      (OriginalLineCell.header (OriginalLineMixed.run n (OriginalLineMixed.step s.core)).core).core) (n+1)
    by_cases seen : OriginalLineCell.already (OriginalLineCell.header s.core).core
    · have eq : OriginalLineMixed.step s.core=OriginalLineCell.visit s.core := if_pos seen
      rw [eq] at tail ⊢
      exact .duplicate s _ n pc item seen tail
    · obtain ⟨trace,line,frac,flags,p,v,w,ready,saved,keep⟩ := fresh seen
      have eq : OriginalLineMixed.step s.core=OriginalLineDispatch.result s.core := if_neg seen
      rw [eq] at tail ⊢
      exact .crossing s _ n pc trace line frac flags p v w ready saved keep tail

end Doom.Proofs.OriginalLineTraversal
