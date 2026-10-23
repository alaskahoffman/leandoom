import Doom.Proofs.OriginalGroupScan
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace Doom.Proofs.OriginalGroupFrame
open Verification X86 X86Memory X86Control BlockSummary OriginalGroupStep OriginalGroupScan

/-- A protected word is disjoint from all five stack words written by a scan. -/
structure StackApart (a sp : Word) : Prop where
  ret : Apart a (sp-4)
  top : Apart a sp
  bottom : Apart a (sp+4)
  left : Apart a (sp+8)
  right : Apart a (sp+12)

theorem helper_frame (s : X86Memory.State) (ret a : Word)
    (box : s.regs 0=s.regs 4) (h : StackApart a (s.regs 4)) :
    load32 (OriginalGroupBounds.boxResult (X86Routine.pushWord s ret)).core.memory a=load32 s.memory a := by
  let t := X86Routine.pushWord s ret
  have reg : t.regs 0=s.regs 4 := by simp [t,X86Routine.pushWord,put,write,box]
  have horizontal := OriginalGroupBounds.horizontal_frame t a (by simpa [reg] using h.left) (by simpa [reg] using h.right)
  have vertical := OriginalGroupBounds.vertical_frame (OriginalGroupBounds.horizontal t).core a
    (by simpa [reg] using h.bottom) (by simpa [reg] using h.top)
  change load32 (OriginalGroupBounds.vertical (OriginalGroupBounds.horizontal t).core).core.memory a=_
  rw [vertical,horizontal]
  exact load_store_apart _ _ _ _ h.ret

theorem first_frame (s : X86Memory.State) (a : Word) (h : StackApart a (s.regs 4)) :
    load32 (OriginalGroupBounds.firstDone s).core.memory a=load32 s.memory a :=
  helper_frame (OriginalGroupBounds.firstInput s) _ a
    (by simp [OriginalGroupBounds.firstInput,put,write])
    (by simpa [OriginalGroupBounds.firstInput,put,write] using h)
theorem second_frame (s : X86Memory.State) (a : Word) (h : StackApart a (s.regs 4)) :
    load32 (OriginalGroupBounds.secondDone s).core.memory a=load32 s.memory a :=
  helper_frame (OriginalGroupBounds.secondInput s) _ a
    (by simp [OriginalGroupBounds.secondInput,put,write])
    (by simpa [OriginalGroupBounds.secondInput,put,write] using h)

theorem continuation_frame (s : X86Memory.State) (a : Word) (h : StackApart a (s.regs 4)) :
    load32 (OriginalGroupBounds.result s).core.memory a=load32 s.memory a := by
  have f := first_frame s a h
  have g := second_frame (OriginalGroupBounds.firstDone s).core a
    (by simpa [(OriginalGroupBounds.first_return s).2] using h)
  exact g.trans f

theorem iteration_frame (s : X86Memory.State) (a : Word)
    (stack : StackApart a (s.regs 4)) (output : Apart a (s.regs 6)) :
    load32 (body s).core.memory a=load32 s.memory a := by
  have frame := continuation_frame (OriginalGroupLines.selected s).core a
    (by simpa [selected_regs] using stack)
  have selection : load32 (OriginalGroupLines.selected s).core.memory a=load32 s.memory a := by
    simp only [OriginalGroupLines.selected,OriginalGroupLines.emitted]
    split
    · exact load_store_apart _ _ _ _ output
    · split
      · exact load_store_apart _ _ _ _ output
      · rfl
  cases h : hit s
  · simp [body,h,OriginalGroupBounds.advanced,put]
  · simpa only [body,h,↓reduceIte] using frame.trans selection

theorem iteration_written (s : X86Memory.State) (yes : hit s=true)
    (safe : StackApart (s.regs 6) (s.regs 4)) :
    load32 (body s).core.memory (s.regs 6)=s.regs 1 := by
  have frame := continuation_frame (OriginalGroupLines.selected s).core (s.regs 6)
    (by simpa [selected_regs] using safe)
  simpa only [body,yes,↓reduceIte] using frame.trans (OriginalGroupLines.selected_pointer s yes).2

/-- Pure iteration of the proved body; an instruction-path theorem below connects
this value to execution rather than assuming its agreement with the machine. -/
def after : Nat → X86Memory.State → X86Memory.State
  | 0,s => s
  | n+1,s => after n (body s).core

theorem after_stack (n : Nat) (s : X86Memory.State) : (after n s).regs 4=s.regs 4 := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => exact (ih (body s).core).trans (iteration_registers s).2.2.2.1

theorem scan_after (remaining total : Nat) (sp base : Word) (layout : Layout total sp base)
    (i : Nat) (s : X86Memory.State) (f : Option Flags) (ready : Ready total sp base i s)
    (sum : i+remaining=total) (positive : 0<remaining) :
    ∃ n out, n≤43*remaining ∧ X86Routine.Prefix program [0x2e6af] n ⟨s,f,0x2e676⟩ out ∧
      out.pc=0x2e6af ∧ out.core=after remaining s := by
  induction remaining generalizing i s f with
  | zero => omega
  | succ remaining ih =>
    obtain ⟨n,hn,path⟩ := iteration_path s f
    have path := path.transfer program [0x2e6af] (fun _ _ => rfl) (by
      intro pc hp; simp only [List.mem_singleton]; intro eq; subst pc; exact hp (by decide))
    obtain ⟨next,pc⟩ := ready_step layout ready (by omega)
    by_cases last : remaining=0
    · refine ⟨n,body s,by omega,path,?_,?_⟩
      · have final : i+1=total := by omega
        simpa [final] using pc
      · simp [after,last]
    · have more : i+1<total := by omega
      have atLoop : (body s).pc=0x2e676 := by simpa [more] using pc
      obtain ⟨m,out,hm,tail,done,final⟩ := ih (i+1) (body s).core (body s).flags next (by omega) (by omega)
      have eta : (⟨(body s).core,(body s).flags,0x2e676⟩ : X86Control.State)=body s := by rw [←atLoop]
      rw [eta] at tail
      exact ⟨n+m,out,by omega,OriginalGroupBounds.prefix_join path tail,done,final⟩

end Doom.Proofs.OriginalGroupFrame
