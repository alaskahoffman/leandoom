import Doom.Proofs.OriginalLineDispatch
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.OriginalLineMixed
open Verification X86 X86Memory X86Control BlockSummary
abbrev program := OriginalLineDispatch.program

def Crossing (s : X86Memory.State) : Prop :=
  ∃ (trace : Collision.Divline) (line : Collision.Line) (frac : Fixed) (flags : Nat) (p v w : Word),
    OriginalLineDispatch.Ready s trace line frac flags p v w ∧
    OriginalLineTail.RecordSafe (OriginalLineDispatch.view s) ((OriginalLineDispatch.view s).regs 4-(12#32)) ∧
    (frac.raw<0 ∨ (flags &&& 4 != 0 && frac.raw<65536 && line.back.isNone)=false)

/-- Use the current stamp memory at each iteration, including previous writes. -/
def step (s : X86Memory.State) : X86Control.State :=
  if OriginalLineCell.already (OriginalLineCell.header s).core then OriginalLineCell.visit s
  else OriginalLineDispatch.result s

def run : Nat → X86Control.State → X86Control.State
  | 0,s => s
  | n+1,s => run n (step s.core)

/-- Conditional loop domain. Fresh crossing contracts must still be supplied at
each reached state. Same-side callbacks and early stops are not admitted here. -/
def Admitted : Nat → X86Control.State → Prop
  | 0,_ => True
  | n+1,s => OriginalLineCell.itemWord s.core≠(0xffffffff#32) ∧
      (¬OriginalLineCell.already (OriginalLineCell.header s.core).core → Crossing s.core) ∧
      Admitted n (step s.core)

theorem step_execution (s : X86Control.State) (atHeader : s.pc=0x2c57f)
    (last : OriginalLineCell.itemWord s.core≠(0xffffffff#32))
    (fresh : ¬OriginalLineCell.already (OriginalLineCell.header s.core).core → Crossing s.core) :
    (∃ n≤281, X86Routine.Prefix program [] n s (step s.core)) ∧
    (step s.core).pc=0x2c57f ∧ (step s.core).core.regs 2=s.core.regs 2+(2#32) ∧
    (step s.core).core.regs 4=s.core.regs 4 := by
  by_cases seen : OriginalLineCell.already (OriginalLineCell.header s.core).core
  · have dup : OriginalLineResume.Duplicates 1 s := ⟨last,seen,trivial⟩
    obtain ⟨n,hn,path⟩ := OriginalLineResume.skip_execution 1 s atHeader dup
    have path := path.transfer program [] E1M1LineResume.contains_resume (by simp)
    have obs := OriginalLineResume.skip_observe 1 s dup
    have pc := OriginalLineResume.skip_pc 1 s atHeader dup
    simp only [step,if_pos seen]
    refine ⟨⟨n,by omega,?_⟩,?_,?_,?_⟩
    · simpa only [OriginalLineResume.skipMany] using path
    · simpa only [OriginalLineResume.skipMany] using pc
    · simpa only [OriginalLineResume.skipMany] using obs.2.1
    · simpa only [OriginalLineResume.skipMany] using obs.2.2
  · obtain ⟨trace,line,frac,flags,p,v,w,ready,saved,keep⟩ := fresh seen
    obtain ⟨n,hn,path⟩ := OriginalLineDispatch.execution s.core trace line frac flags p v w ready s.flags
    rw [OriginalPathXStep.at_pc _ _ atHeader] at path
    have obs := OriginalLineDispatch.continued s.core trace line frac flags p v w ready saved keep
    simpa only [step,if_neg seen] using And.intro (Exists.intro n (And.intro hn path)) obs

theorem execution (n : Nat) (s : X86Control.State) (atHeader : s.pc=0x2c57f) (h : Admitted n s) :
    (∃ steps≤281*n, X86Routine.Prefix program [] steps s (run n s)) ∧
    (run n s).pc=0x2c57f ∧ (run n s).core.regs 2=s.core.regs 2+BitVec.ofNat 32 (2*n) ∧
    (run n s).core.regs 4=s.core.regs 4 := by
  induction n generalizing s with
  | zero => exact ⟨⟨0,by omega,.nil s⟩,atHeader,by simp [run],rfl⟩
  | succ n ih =>
    obtain ⟨last,fresh,tail⟩ := h
    obtain ⟨⟨a,ha,head⟩,pc,cursor,stack⟩ := step_execution s atHeader last fresh
    obtain ⟨⟨b,hb,next⟩,npc,ncursor,nstack⟩ := ih (step s.core) pc tail
    refine ⟨⟨a+b,by omega,OriginalGroupBounds.prefix_join head next⟩,npc,?_,nstack.trans stack⟩
    change (run n (step s.core)).core.regs 2=_
    rw [ncursor,cursor]
    simp only [Nat.mul_succ,BitVec.ofNat_add]
    bv_decide

theorem through_sentinel (n : Nat) (s : X86Control.State) (atHeader : s.pc=0x2c57f)
    (h : Admitted n s) (last : OriginalLineCell.item (run n s).core=(0xffff#16)) :
    ∃ steps≤281*n+7, X86Routine.Prefix program [] steps s
      (OriginalLineBounds.returned (OriginalLineCell.header (run n s).core).core) := by
  obtain ⟨⟨m,hm,head⟩,pc,_,_⟩ := execution n s atHeader h
  have tail := OriginalLineResume.sentinel_execution (run n s).core (run n s).flags last
  rw [OriginalPathXStep.at_pc _ _ pc] at tail
  have tail := tail.transfer program [] E1M1LineResume.contains_resume (by simp)
  exact ⟨m+7,by omega,OriginalGroupBounds.prefix_join head tail⟩

end Doom.Proofs.OriginalLineMixed
