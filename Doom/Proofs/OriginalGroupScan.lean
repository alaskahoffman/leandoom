import Doom.Proofs.OriginalGroupStep
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalGroupScan
open Verification X86 X86Memory X86Control BlockSummary OriginalGroupStep

/-- The output cursor after j emitted pointers, with the original 32-bit wrap. -/
def cursor (base : Word) : Nat → Word
  | 0 => base
  | j+1 => cursor base j+4

/-- Static storage conditions sufficient for scan termination. Only the finite
output region that this scan can visit is constrained; no all-address disjointness
or successful trace is assumed. -/
structure Layout (total : Nat) (sp base : Word) : Prop where
  small : total<2147483648
  stack : StackSafe sp
  output : ∀ j, j<total → Apart 0x2c134 (cursor base j)

structure Ready (total : Nat) (sp base : Word) (i : Nat) (s : X86Memory.State) : Prop where
  index : (s.regs 7).toNat=i
  count : (load32 s.memory 0x2c134).toNat=total
  stack : s.regs 4=sp
  output : ∃ j, j≤i ∧ s.regs 6=cursor base j

theorem ready_safe {total sp base i s} (layout : Layout total sp base)
    (ready : Ready total sp base i s) (inside : i<total) : CountSafe s := by
  obtain ⟨j,hj,cursor⟩ := ready.output
  exact ⟨by rw [cursor]; exact layout.output j (by omega),by rw [ready.stack]; exact layout.stack⟩

/-- Every selected line emits one pointer; a skipped line emits none. Thus at
most i pointer slots are consumed after i iterations, which closes the frame
condition for the next iteration using the same finite layout certificate. -/
theorem ready_step {total sp base i s} (layout : Layout total sp base)
    (ready : Ready total sp base i s) (inside : i<total) :
    Ready total sp base (i+1) (body s).core ∧
    (body s).pc=(if i+1<total then 0x2e676 else 0x2e6af) := by
  have safe := ready_safe layout ready inside
  obtain ⟨index,pc⟩ := iteration_progress s safe i total ready.index ready.count inside layout.small
  obtain ⟨ri,rl,rs,rsp,rc⟩ := iteration_registers s
  obtain ⟨j,hj,cur⟩ := ready.output
  refine ⟨⟨index,?_,rsp.trans ready.stack,?_⟩,pc⟩
  · rw [iteration_count s safe,ready.count]
  · cases h : hit s
    · refine ⟨j,by omega,?_⟩
      simpa [h,cur] using rc
    · refine ⟨j+1,by omega,?_⟩
      simpa [h,cur,cursor] using rc

private theorem active (pc : Nat) (h : program pc≠none) : pc∉[0x2e6af] := by
  simp only [List.mem_singleton]
  intro eq; subst pc; exact h (by decide)

/-- Construct the complete original instruction path by induction on the
remaining linedefs. Each iteration's state and branch are proved, not supplied
as a trace or assumed termination of an interpreter. -/
theorem scan_path (remaining : Nat) (total : Nat) (sp base : Word)
    (layout : Layout total sp base) (i : Nat) (s : X86Memory.State) (f : Option Flags)
    (ready : Ready total sp base i s) (sum : i+remaining=total) (positive : 0<remaining) :
    ∃ n out, n≤43*remaining ∧ X86Routine.Prefix program [0x2e6af] n ⟨s,f,0x2e676⟩ out ∧
      out.pc=0x2e6af ∧ Ready total sp base total out.core := by
  induction remaining generalizing i s f with
  | zero => omega
  | succ remaining ih =>
    obtain ⟨n,hn,path⟩ := iteration_path s f
    have path := path.transfer program [0x2e6af] (fun _ _ => rfl) active
    obtain ⟨next,pc⟩ := ready_step layout ready (by omega)
    by_cases last : remaining=0
    · have final : i+1=total := by omega
      refine ⟨n,body s,by omega,path,?_,?_⟩
      · simpa [final] using pc
      · simpa [final] using next
    · have more : i+1<total := by omega
      have atLoop : (body s).pc=0x2e676 := by simpa [more] using pc
      obtain ⟨m,out,hm,tail,done,final⟩ := ih (i+1) (body s).core (body s).flags next (by omega) (by omega)
      have eta : (⟨(body s).core,(body s).flags,0x2e676⟩ : X86Control.State)=body s := by rw [←atLoop]
      rw [eta] at tail
      exact ⟨n+m,out,by omega,OriginalGroupBounds.prefix_join path tail,done,final⟩

/-- Bounded execution from any in-range scan index, with a derived final state. -/
theorem scan_execution (total : Nat) (sp base : Word) (layout : Layout total sp base)
    (i : Nat) (s : X86Memory.State) (f : Option Flags) (ready : Ready total sp base i s)
    (inside : i<total) :
    ∃ out, X86Routine.run program [0x2e6af] (43*(total-i)) ⟨s,f,0x2e676⟩=some out ∧
      out.pc=0x2e6af ∧ Ready total sp base total out.core := by
  obtain ⟨n,out,hn,path,done,final⟩ := scan_path (total-i) total sp base layout i s f ready (by omega) (by omega)
  have stop : X86Routine.run program [0x2e6af] 0 out=some out := by simp [X86Routine.run,done]
  exact ⟨out,path.finish stop _ (by omega),done,final⟩

/-- Shareware E1M1 has 475 linedefs. This specializes the bound, retaining the
explicit physical layout and initial memory relation. -/
theorem e1m1_scan (sp base : Word) (layout : Layout 475 sp base)
    (s : X86Memory.State) (f : Option Flags) (ready : Ready 475 sp base 0 s) :
    ∃ out, X86Routine.run program [0x2e6af] 20425 ⟨s,f,0x2e676⟩=some out ∧
      out.pc=0x2e6af ∧ Ready 475 sp base 475 out.core :=
  scan_execution 475 sp base layout 0 s f ready (by decide)


/-- Publication of the sector array pointer may not overwrite the global count.
The remaining loader storage and cached line pointers are outside this theorem. -/
theorem entry_ready (total : Nat) (s : X86Memory.State)
    (count : (load32 s.memory 0x2c134).toNat=total)
    (safe : Apart 0x2c134 (s.regs 5+82)) :
    Ready total (s.regs 4) (s.regs 6) 0 (OriginalGroupLines.entry s).core := by
  constructor
  · simp [OriginalGroupLines.entry,OriginalGroupLines.prepared,put,write]
  · simpa only [OriginalGroupLines.entry,OriginalGroupLines.prepared,put,
      load_store_apart _ _ _ _ safe] using count
  · simp [OriginalGroupLines.entry,OriginalGroupLines.prepared,put,write]
  · exact ⟨0,Nat.le_refl _,by simp [OriginalGroupLines.entry,OriginalGroupLines.prepared,put,write,cursor]⟩

/-- Array publication, signed count gate, and the entire finite scan. Zero count
exits at the gate; positive counts execute every iteration, preserving the
selected and skipped paths. -/
theorem entry_execution (total : Nat) (s : X86Memory.State) (f : Option Flags)
    (layout : Layout total (s.regs 4) (s.regs 6))
    (count : (load32 s.memory 0x2c134).toNat=total)
    (safe : Apart 0x2c134 (s.regs 5+82)) :
    ∃ out, X86Routine.run program [0x2e6af] (6+43*total) ⟨s,f,0x2e661⟩=some out ∧
      out.pc=0x2e6af ∧ Ready total (s.regs 4) (s.regs 6) total out.core := by
  obtain ⟨n,hn,path,done⟩ := X86Routine.run_path (OriginalGroupLines.entry_execution s f)
  have path := path.transfer program [0x2e6af] selection_agrees (by
    intro pc hp
    simp only [List.mem_singleton]
    intro eq; subst pc; exact hp (by decide))
  have ready := entry_ready total s count safe
  change (load32 s.memory (0x2c134#32)).toNat=total at count
  have signed : (load32 s.memory (0x2c134#32)).toInt=(total : Int) := by
    simp only [BitVec.toInt_eq_toNat_cond,count]
    split <;> have := layout.small <;> omega
  by_cases zero : total=0
  · have pc : (OriginalGroupLines.entry s).pc=0x2e6af := by simp [OriginalGroupLines.entry,signed,zero]
    have stop : X86Routine.run program [0x2e6af] 0 (OriginalGroupLines.entry s)=some (OriginalGroupLines.entry s) := by simp [X86Routine.run,pc]
    exact ⟨OriginalGroupLines.entry s,path.finish stop _ (by omega),pc,by simpa [zero] using ready⟩
  · have pc : (OriginalGroupLines.entry s).pc=0x2e676 := by
      have pos : ¬(total : Int)≤0 := by omega
      simp [OriginalGroupLines.entry,signed,pos,zero]
    obtain ⟨out,run,last,final⟩ := scan_execution total (s.regs 4) (s.regs 6) layout 0
      (OriginalGroupLines.entry s).core (OriginalGroupLines.entry s).flags ready (by omega)
    have eta : (⟨(OriginalGroupLines.entry s).core,(OriginalGroupLines.entry s).flags,0x2e676⟩ : X86Control.State)=OriginalGroupLines.entry s := by rw [←pc]
    rw [eta] at run
    exact ⟨out,path.finish run _ (by omega),last,final⟩

end Doom.Proofs.OriginalGroupScan
