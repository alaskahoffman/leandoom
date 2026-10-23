import Doom.Proofs.OriginalLineFinish
import Doom.Proofs.OriginalLineCell
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.OriginalLineResume
open Verification X86 X86Memory X86Control BlockSummary

/-- Reuse the already pinned iterator and epilogue bytes. -/
def program (pc : Nat) :=
  match OriginalLineCell.program pc with
  | some op => some op
  | none => OriginalLineBounds.program pc

theorem contains_cell (pc : Nat) (h : OriginalLineCell.program pc≠none) :
    program pc=OriginalLineCell.program pc := by
  unfold program
  cases hp : OriginalLineCell.program pc <;> simp_all

theorem contains_bounds (pc : Nat) (h : OriginalLineBounds.program pc≠none) :
    program pc=OriginalLineBounds.program pc := by
  by_cases entry : 0x2c520≤pc ∧ pc<0x2c541
  · simp [program,OriginalLineCell.program,OriginalLineCell.bytesProgram,show ¬(0x2c541≤pc ∧ pc<0x2c587) by omega]
  by_cases ret : 0x2c587≤pc ∧ pc<0x2c591
  · simp [program,OriginalLineCell.program,OriginalLineCell.bytesProgram,show ¬(0x2c541≤pc ∧ pc<0x2c587) by omega]
  simp [OriginalLineBounds.program,OriginalLineBounds.bytesProgram,entry,ret] at h

/-- The early-stop epilogue preserves EAX; the sentinel path sets it to one. -/
def exit1 (s : X86Memory.State) := put s 4 (s.regs 4+(4#32))
def exit2 (s : X86Memory.State) := put (put (exit1 s) 4 (s.regs 4+(8#32))) 7 (load32 s.memory (s.regs 4+(4#32)))
def exited (s : X86Memory.State) : X86Control.State :=
  ⟨put (exit2 s) 4 (s.regs 4+(12#32)),none,(load32 s.memory (s.regs 4+(8#32))).toNat⟩

theorem exit_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 3 ⟨s,f,0x2c58c⟩ (exited s) := by
  have path : X86Routine.Prefix OriginalLineBounds.listed [] 3 ⟨s,f,0x2c58c⟩ (exited s) := by
    apply X86Routine.Prefix.step (middle:=⟨exit1 s,none,0x2c58f⟩) (by simp) (by rfl) (by rfl)
    apply X86Routine.Prefix.step (middle:=⟨exit2 s,none,0x2c590⟩) (by simp) (by rfl) (by simp [X86Routine.execute,exit1,exit2,put,write,BitVec.add_assoc])
    apply X86Routine.Prefix.step (middle:=exited s) (by simp) (by rfl) (by simp [X86Routine.execute,exited,exit1,exit2,put,write,BitVec.add_assoc])
    exact .nil _
  exact (path.transfer OriginalLineBounds.program [] OriginalLineBounds.decoded (by simp)).transfer program [] contains_bounds (by simp)

def result (s : X86Memory.State) :=
  if s.regs 0=(0#32) then exited s else OriginalLineCell.advance s

theorem execution (s : X86Memory.State) (f : Option Flags) :
    ∃ n≤5, X86Routine.Prefix program [] n ⟨s,f,0x2c578⟩ (result s) := by
  have head := (OriginalLineCell.resume_execution s f).transfer program [] contains_cell (by simp)
  by_cases stop : s.regs 0=(0#32)
  · have pc : (OriginalLineCell.resumed s).pc=0x2c58c := by simp [OriginalLineCell.resumed,stop]
    have tail := exit_execution s (some (logical32 (s.regs 0)))
    change X86Routine.Prefix _ _ _ ⟨(OriginalLineCell.resumed s).core,(OriginalLineCell.resumed s).flags,0x2c58c⟩ _ at tail
    rw [OriginalPathXStep.at_pc _ _ pc] at tail
    exact ⟨5,by omega,by simpa only [result,if_pos stop] using OriginalGroupBounds.prefix_join head tail⟩
  · have pc : (OriginalLineCell.resumed s).pc=0x2c57c := by simp [OriginalLineCell.resumed,stop]
    have tail := (OriginalLineCell.advance_execution s (some (logical32 (s.regs 0)))).transfer program [] contains_cell (by simp)
    change X86Routine.Prefix _ _ _ ⟨(OriginalLineCell.resumed s).core,(OriginalLineCell.resumed s).flags,0x2c57c⟩ _ at tail
    rw [OriginalPathXStep.at_pc _ _ pc] at tail
    exact ⟨3,by omega,by simpa only [result,if_neg stop] using OriginalGroupBounds.prefix_join head tail⟩

theorem memory (s : X86Memory.State) : (result s).core.memory=s.memory := by
  unfold result; split <;> rfl

theorem continued (s : X86Memory.State) (nonzero : s.regs 0≠(0#32)) :
    (result s).pc=0x2c57f ∧ (result s).core.regs 2=s.regs 2+(2#32) ∧
    (result s).core.regs 4=s.regs 4 := by
  simp [result,nonzero,OriginalLineCell.advance,put,write]

theorem stopped (s : X86Memory.State) (zero : s.regs 0=(0#32)) :
    (result s).core.regs 0=(0#32) ∧ (result s).core.regs 4=s.regs 4+(12#32) ∧
    (result s).core.regs 7=load32 s.memory (s.regs 4+(4#32)) ∧
    (result s).pc=(load32 s.memory (s.regs 4+(8#32))).toNat := by
  simp [result,zero,exited,exit1,exit2,put,write]

/-- The callback restores the iterator cursor from its actual saved word,
including possible effects of intercept writes on that word. -/
theorem finish_cursor (s : X86Memory.State) :
    (OriginalLineFinish.result s).core.regs 2=
      load32 (OriginalLineFinish.result s).core.memory (s.regs 4+(24#32)) := by
  have unwind (t : X86Memory.State) : (OriginalLineFinish.unwind t).core.regs 2=load32 t.memory (t.regs 4+(24#32)) := by
    simp [OriginalLineSecondPoint.unwind,OriginalLineSecondPoint.unwind5,OriginalLineSecondPoint.unwind4,
      OriginalLineSecondPoint.unwind3,OriginalLineSecondPoint.unwind2,OriginalLineSecondPoint.unwind1,
      OriginalLineSecondPoint.unwind0,put,write]
  simp only [OriginalLineFinish.result,OriginalLineFinish.selected]
  split <;> (try split) <;>
    simp [OriginalLineFinish.rejected,OriginalLineFinish.stopped,OriginalLineFinish.accepted,
      unwind,OriginalLineFinish.unwind_memory,OriginalLineFinish.inserted_regs,OriginalLineFinish.start,put,write]

/-- Connect a real callback return to its iterator, keeping both the return
word and the saved list cursor explicit. No callback return address is assumed
by the instruction semantics. -/
theorem finish_continue (s : X86Memory.State) (list : Word)
    (ret : load32 s.memory (s.regs 4+(36#32))=(0x2c578#32))
    (saved : load32 s.memory (s.regs 4+(24#32))=list)
    (safe : ∀ a∈[s.regs 4+(24#32),s.regs 4+(36#32)],
      ∀ w∈[OriginalLineFinish.cursor s,OriginalLineFinish.cursor s+(4#32),OriginalLineFinish.cursor s+(8#32),(0x2c028#32)], Apart a w)
    (keepGoing : ¬(¬(s.regs 0).toInt<0 ∧ OriginalLineFinish.early s)) :
    (OriginalLineFinish.result s).pc=0x2c578 ∧
    (result (OriginalLineFinish.result s).core).pc=0x2c57f ∧
    (result (OriginalLineFinish.result s).core).core.regs 2=list+(2#32) := by
  have pc := OriginalLineFinish.returned s (safe _ (by simp))
  rw [ret] at pc
  have cursor := finish_cursor s
  rw [OriginalLineFinish.frame s _ (safe _ (by simp)),saved] at cursor
  have nz : (OriginalLineFinish.result s).core.regs 0≠(0#32) := by
    rw [OriginalLineFinish.result_value,if_neg keepGoing]; decide
  exact ⟨pc,(continued _ nz).1,by rw [(continued _ nz).2.1,cursor]⟩

/-- Iterate genuine duplicate-skip executions. The condition is checked on each
successive machine state, not supplied as a claim about the final result. -/
def skipMany : Nat → X86Control.State → X86Control.State
  | 0,s => s
  | n+1,s => skipMany n (OriginalLineCell.visit s.core)
def Duplicates : Nat → X86Control.State → Prop
  | 0,_ => True
  | n+1,s => OriginalLineCell.itemWord s.core≠(0xffffffff#32) ∧
      OriginalLineCell.already (OriginalLineCell.header s.core).core ∧
      Duplicates n (OriginalLineCell.visit s.core)

theorem skip_execution (n : Nat) (s : X86Control.State) (atHeader : s.pc=0x2c57f)
    (seen : Duplicates n s) :
    ∃ steps≤10*n, X86Routine.Prefix program [] steps s (skipMany n s) := by
  induction n generalizing s with
  | zero => exact ⟨0,by omega,.nil _⟩
  | succ n ih =>
    rcases seen with ⟨last,seen,tail⟩
    have obs := OriginalLineCell.skip_observe s.core last seen
    have head := (OriginalLineCell.header_execution s.core s.flags).transfer program [] contains_cell (by simp)
    have dp := (OriginalLineCell.duplicate_execution (OriginalLineCell.header s.core).core (OriginalLineCell.header s.core).flags).transfer program [] contains_cell (by simp)
    have hpc : (OriginalLineCell.header s.core).pc=0x2c55c := by simp [OriginalLineCell.header,last]
    rw [OriginalPathXStep.at_pc _ _ hpc] at dp
    have adv := (OriginalLineCell.advance_execution (OriginalLineCell.duplicate (OriginalLineCell.header s.core).core).core (OriginalLineCell.duplicate (OriginalLineCell.header s.core).core).flags).transfer program [] contains_cell (by simp)
    have dpc : (OriginalLineCell.duplicate (OriginalLineCell.header s.core).core).pc=0x2c57c := by simp [OriginalLineCell.duplicate,seen]
    rw [OriginalPathXStep.at_pc _ _ dpc] at adv
    have one : X86Routine.Prefix program [] 10 s (OriginalLineCell.visit s.core) := by
      rw [← OriginalPathXStep.at_pc _ _ atHeader]
      simpa only [OriginalLineCell.visit,if_neg last,if_pos seen] using
        OriginalGroupBounds.prefix_join (OriginalGroupBounds.prefix_join head dp) adv
    obtain ⟨m,hm,hp⟩ := ih (OriginalLineCell.visit s.core) obs.2.2 tail
    exact ⟨10+m,by omega,OriginalGroupBounds.prefix_join one hp⟩

theorem skip_observe (n : Nat) (s : X86Control.State) (seen : Duplicates n s) :
    (skipMany n s).core.memory=s.core.memory ∧
    (skipMany n s).core.regs 2=s.core.regs 2+BitVec.ofNat 32 (2*n) ∧
    (skipMany n s).core.regs 4=s.core.regs 4 := by
  induction n generalizing s with
  | zero => simp [skipMany]
  | succ n ih =>
    rcases seen with ⟨last,seen,tail⟩
    have obs := OriginalLineCell.skip_observe s.core last seen
    have sp : (OriginalLineCell.visit s.core).core.regs 4=s.core.regs 4 := by
      simp only [OriginalLineCell.visit,if_neg last,if_pos seen]
      simp [OriginalLineCell.advance,OriginalLineCell.duplicate,
        OriginalLineCell.d4,OriginalLineCell.d3,OriginalLineCell.d2,OriginalLineCell.d1,
        OriginalLineCell.header,OriginalLineCell.h1,put,write]
    have next := ih (OriginalLineCell.visit s.core) tail
    simp only [skipMany]
    refine ⟨next.1.trans obs.1,?_,next.2.2.trans sp⟩
    rw [next.2.1,obs.2.1]
    simp only [Nat.mul_succ,BitVec.ofNat_add]
    bv_decide

/-- The next signed-short is read from the unchanged list at exactly 2*n bytes. -/
theorem next_item (n : Nat) (s : X86Control.State) (seen : Duplicates n s) :
    OriginalLineCell.item (skipMany n s).core=
      load16 s.core.memory (s.core.regs 2+BitVec.ofNat 32 (2*n)) := by
  simp only [OriginalLineCell.item,(skip_observe n s seen).1,(skip_observe n s seen).2.1]

theorem sentinel_execution (s : X86Memory.State) (f : Option Flags)
    (last : OriginalLineCell.item s=(0xffff#16)) :
    X86Routine.Prefix program [] 7 ⟨s,f,0x2c57f⟩ (OriginalLineBounds.returned (OriginalLineCell.header s).core) := by
  have head := (OriginalLineCell.header_execution s f).transfer program [] contains_cell (by simp)
  have pc : (OriginalLineCell.header s).pc=0x2c587 := by rw [OriginalLineCell.header_pc,if_pos last]
  have tail := (OriginalLineBounds.return_execution (OriginalLineCell.header s).core (OriginalLineCell.header s).flags).transfer program [] contains_bounds (by simp)
  rw [OriginalPathXStep.at_pc _ _ pc] at tail
  exact OriginalGroupBounds.prefix_join head tail

/-- A list word and its linedef's valid-count stamp, expressed in the initial
byte memory. Signed-short addressing is retained exactly. -/
def SeenAt (m : Memory) (p : Word) : Prop :=
  load16 m p≠(0xffff#16) ∧ load32 m (0x13580#32)=
    load32 m ((load16 m p).signExtend 32*(62#32)+load32 m (0x2c120#32)+(54#32))

theorem seen_at (s : X86Memory.State) : SeenAt s.memory (s.regs 2) ↔
    OriginalLineCell.itemWord s≠(0xffffffff#32) ∧
    OriginalLineCell.already (OriginalLineCell.header s).core := by
  simp [SeenAt,OriginalLineCell.itemWord,OriginalLineCell.item,OriginalLineCell.sentinel,
    OriginalLineCell.already,OriginalLineCell.header,OriginalLineCell.h1,
    OriginalLineCell.epoch,OriginalLineCell.lineAddress,OriginalLineCell.lineBase,put,write]

/-- All per-iteration duplicate conditions follow from one initial memory
window. Earlier duplicate skips do not require the caller to restate them. -/
theorem duplicates_from_memory (n : Nat) (s : X86Control.State)
    (window : ∀ i<n, SeenAt s.core.memory (s.core.regs 2+BitVec.ofNat 32 (2*i))) :
    Duplicates n s := by
  induction n generalizing s with
  | zero => trivial
  | succ n ih =>
    have first : SeenAt s.core.memory (s.core.regs 2) := by simpa using window 0 (by omega)
    obtain ⟨last,seen⟩ := (seen_at s.core).mp first
    have obs := OriginalLineCell.skip_observe s.core last seen
    refine ⟨last,seen,ih (OriginalLineCell.visit s.core) ?_⟩
    intro i hi
    rw [obs.1,obs.2.1]
    have address : s.core.regs 2+2+BitVec.ofNat 32 (2*i)=s.core.regs 2+BitVec.ofNat 32 (2*(i+1)) := by
      simp only [Nat.mul_add,BitVec.ofNat_add]
      bv_decide
    rw [address]
    exact window (i+1) (by omega)

theorem skip_pc (n : Nat) (s : X86Control.State) (atHeader : s.pc=0x2c57f)
    (seen : Duplicates n s) : (skipMany n s).pc=0x2c57f := by
  induction n generalizing s with
  | zero => exact atHeader
  | succ n ih =>
    rcases seen with ⟨last,seen,tail⟩
    exact ih _ (OriginalLineCell.skip_observe s.core last seen).2.2 tail

/-- Any finite already-visited prefix followed by -1 returns success through
the actual iterator epilogue, with no callbacks and no memory writes. -/
theorem through_sentinel (n : Nat) (s : X86Control.State) (atHeader : s.pc=0x2c57f)
    (window : ∀ i<n, SeenAt s.core.memory (s.core.regs 2+BitVec.ofNat 32 (2*i)))
    (last : load16 s.core.memory (s.core.regs 2+BitVec.ofNat 32 (2*n))=(0xffff#16)) :
    ∃ steps≤10*n+7, X86Routine.Prefix program [] steps s
      (OriginalLineBounds.returned (OriginalLineCell.header (skipMany n s).core).core) := by
  have seen := duplicates_from_memory n s window
  obtain ⟨m,hm,head⟩ := skip_execution n s atHeader seen
  have tail := sentinel_execution (skipMany n s).core (skipMany n s).flags
    (by rw [next_item n s seen]; exact last)
  rw [OriginalPathXStep.at_pc _ _ (skip_pc n s atHeader seen)] at tail
  exact ⟨m+7,by omega,OriginalGroupBounds.prefix_join head tail⟩

/-- Observable iterator return after the proved duplicate run. -/
theorem sentinel_observe (n : Nat) (s : X86Control.State) (seen : Duplicates n s) :
    let out := OriginalLineBounds.returned (OriginalLineCell.header (skipMany n s).core).core
    out.core.memory=s.core.memory ∧ out.core.regs 0=(1#32) ∧
    out.core.regs 4=s.core.regs 4+(12#32) ∧
    out.core.regs 7=load32 s.core.memory (s.core.regs 4+(4#32)) ∧
    out.pc=(load32 s.core.memory (s.core.regs 4+(8#32))).toNat := by
  have obs := skip_observe n s seen
  simp [OriginalLineBounds.returned,OriginalLineBounds.r3,OriginalLineBounds.r2,OriginalLineBounds.r1,
    OriginalLineCell.header,OriginalLineCell.h1,put,write,obs.1,obs.2.2]

end Doom.Proofs.OriginalLineResume
