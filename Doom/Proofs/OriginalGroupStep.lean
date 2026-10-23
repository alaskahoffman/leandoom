import Doom.Proofs.OriginalGroupLines
import Doom.Proofs.OriginalGroupBounds
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalGroupStep
open Verification X86 X86Memory X86Control BlockSummary

def program : X86Routine.Program := fun pc =>
  if 0x2e661≤pc ∧ pc<0x2e682 then OriginalGroupLines.program pc else OriginalGroupBounds.program pc

theorem selection_agrees (pc : Nat) (h : OriginalGroupLines.program pc≠none) : program pc=OriginalGroupLines.program pc := by
  have inside : 0x2e661≤pc ∧ pc<0x2e682 := by
    by_cases yes : 0x2e661≤pc ∧ pc<0x2e682
    · exact yes
    · simp [OriginalGroupLines.program,OriginalGroupLines.bytesProgram,yes] at h
  simp [program,inside]
theorem bounds_agrees (pc : Nat) (h : OriginalGroupBounds.program pc≠none) : program pc=OriginalGroupBounds.program pc := by
  have outside : ¬(0x2e661≤pc ∧ pc<0x2e682) := by
    intro inside
    have a : ¬(0x241e0≤pc ∧ pc<0x24202) := by omega
    have b : ¬(0x2e682≤pc ∧ pc<0x2e690) := by omega
    have c : ¬(0x2e690≤pc ∧ pc<0x2e6a2) := by omega
    have d : ¬(0x2e6a2≤pc ∧ pc<0x2e6af) := by omega
    simp [OriginalGroupBounds.program,OriginalGroupBounds.bytesProgram,a,b,c,d] at h
  simp [program,outside]

def hit (s : X86Memory.State) : Bool := OriginalGroupLines.accepts (s.regs 5) (OriginalGroupLines.front s) (OriginalGroupLines.back s)
def body (s : X86Memory.State) : X86Control.State :=
  if hit s then OriginalGroupBounds.result (OriginalGroupLines.selected s).core else OriginalGroupBounds.advanced s

private theorem selected_hit (s : X86Memory.State) (h : hit s=true) :
    (OriginalGroupLines.selected s).pc=0x2e682 := (OriginalGroupLines.selected_pointer s h).1
private theorem selected_miss (s : X86Memory.State) (h : hit s=false) :
    (OriginalGroupLines.selected s).core=s ∧ (OriginalGroupLines.selected s).pc=0x2e6a2 := by
  simp only [hit,OriginalGroupLines.accepts,Bool.or_eq_false_iff,beq_eq_false_iff_ne] at h
  simp [OriginalGroupLines.selected,h.1,h.2]

/-- One whole scan iteration. Empty outer exits allow execution to start and
finish at the same loop PC; a stopped `run` at that PC would prove no progress. -/
theorem iteration_path (s : X86Memory.State) (f : Option Flags) :
    ∃ n, n≤43 ∧ X86Routine.Prefix program [] n ⟨s,f,0x2e676⟩ (body s) := by
  obtain ⟨a,ha,pa,_⟩ := X86Routine.run_path (OriginalGroupLines.selection_execution s f)
  have pa := pa.transfer program [] selection_agrees (by simp)
  cases h : hit s
  · obtain ⟨core,pc⟩ := selected_miss s h
    obtain ⟨b,hb,pb,_⟩ := X86Routine.run_path (OriginalGroupBounds.advance_execution s (OriginalGroupLines.selected s).flags)
    have eta : (⟨s,(OriginalGroupLines.selected s).flags,0x2e6a2⟩ : X86Control.State)=OriginalGroupLines.selected s := by
      calc _ = ⟨(OriginalGroupLines.selected s).core,(OriginalGroupLines.selected s).flags,(OriginalGroupLines.selected s).pc⟩ := by rw [core,pc]
           _ = OriginalGroupLines.selected s := rfl
    rw [eta] at pb
    have pb := pb.transfer program [] bounds_agrees (by simp)
    exact ⟨a+b,by omega,by simpa [body,h] using OriginalGroupBounds.prefix_join pa pb⟩
  · obtain ⟨b,hb,pb,_⟩ := X86Routine.run_path (OriginalGroupBounds.joined_execution (OriginalGroupLines.selected s).core (OriginalGroupLines.selected s).flags)
    have eta : (⟨(OriginalGroupLines.selected s).core,(OriginalGroupLines.selected s).flags,0x2e682⟩ : X86Control.State)=OriginalGroupLines.selected s := by
      rw [←selected_hit s h]
    rw [eta] at pb
    have pb := pb.transfer program [] bounds_agrees (by simp)
    exact ⟨a+b,by omega,by simpa [body,h] using OriginalGroupBounds.prefix_join pa pb⟩

/-- Registers needed by the next iteration survive the selection stores. -/
theorem selected_regs (s : X86Memory.State) : (OriginalGroupLines.selected s).core.regs=s.regs := by
  simp only [OriginalGroupLines.selected,OriginalGroupLines.emitted]; split <;> first | rfl | (split <;> rfl)

theorem first_regs (s : X86Memory.State) (r : Reg)
    (keep : r≠0 ∧ r≠2 ∧ r≠3 ∧ r≠4) : (OriginalGroupBounds.firstDone s).core.regs r=s.regs r := by
  simp [OriginalGroupBounds.firstDone,OriginalGroupBounds.boxResult,OriginalGroupBounds.returned,put,write,keep,OriginalGroupBounds.firstInput,X86Routine.pushWord]
theorem second_regs (s : X86Memory.State) (r : Reg)
    (keep : r≠0 ∧ r≠2 ∧ r≠3 ∧ r≠4 ∧ r≠6) : (OriginalGroupBounds.secondDone s).core.regs r=s.regs r := by
  simp [OriginalGroupBounds.secondDone,OriginalGroupBounds.boxResult,OriginalGroupBounds.returned,put,write,keep,OriginalGroupBounds.secondInput,X86Routine.pushWord]
theorem second_cursor (s : X86Memory.State) : (OriginalGroupBounds.secondDone s).core.regs 6=s.regs 6+4 := by
  simp [OriginalGroupBounds.secondDone,OriginalGroupBounds.boxResult,OriginalGroupBounds.returned,put,write,OriginalGroupBounds.secondInput,X86Routine.pushWord]

/-- Exact progress, independently of all memory aliasing and count values. -/
theorem iteration_registers (s : X86Memory.State) :
    (body s).core.regs 7=s.regs 7+1 ∧
    (body s).core.regs 1=s.regs 1+62 ∧
    (body s).core.regs 5=s.regs 5 ∧
    (body s).core.regs 4=s.regs 4 ∧
    (body s).core.regs 6=s.regs 6+(if hit s then 4 else 0) := by
  have f1 := first_regs (OriginalGroupLines.selected s).core 1 (by decide)
  have f5 := first_regs (OriginalGroupLines.selected s).core 5 (by decide)
  have f6 := first_regs (OriginalGroupLines.selected s).core 6 (by decide)
  have f7 := first_regs (OriginalGroupLines.selected s).core 7 (by decide)
  have s1 := second_regs (OriginalGroupBounds.firstDone (OriginalGroupLines.selected s).core).core 1 (by decide)
  have s5 := second_regs (OriginalGroupBounds.firstDone (OriginalGroupLines.selected s).core).core 5 (by decide)
  have s7 := second_regs (OriginalGroupBounds.firstDone (OriginalGroupLines.selected s).core).core 7 (by decide)
  cases h : hit s <;>
    simp [body,h,OriginalGroupBounds.result,OriginalGroupBounds.advanced,put,write,f1,f5,f6,f7,s1,s5,s7,
      (OriginalGroupBounds.first_return _).2,(OriginalGroupBounds.second_return _).2,second_cursor,selected_regs]

/-- Frame conditions for preserving the global count during one iteration.
Only possible writes are excluded; vertices and line fields may still alias. -/
structure StackSafe (sp : Word) : Prop where
  ret : Apart 0x2c134 (sp-4)
  top : Apart 0x2c134 sp
  bottom : Apart 0x2c134 (sp+4)
  left : Apart 0x2c134 (sp+8)
  right : Apart 0x2c134 (sp+12)

structure CountSafe (s : X86Memory.State) : Prop where
  output : Apart 0x2c134 (s.regs 6)
  stack : StackSafe (s.regs 4)

theorem box_count (s : X86Memory.State) (ret : Word)
    (box : s.regs 0=s.regs 4) (h : StackSafe (s.regs 4)) :
    load32 (OriginalGroupBounds.boxResult (X86Routine.pushWord s ret)).core.memory 0x2c134=load32 s.memory 0x2c134 := by
  let t := X86Routine.pushWord s ret
  have reg : t.regs 0=s.regs 4 := by simp [t,X86Routine.pushWord,put,write,box]
  have horizontal := OriginalGroupBounds.horizontal_frame t 0x2c134 (by simpa [reg] using h.left) (by simpa [reg] using h.right)
  have vertical := OriginalGroupBounds.vertical_frame (OriginalGroupBounds.horizontal t).core 0x2c134
    (by simpa [reg] using h.bottom) (by simpa [reg] using h.top)
  change load32 (OriginalGroupBounds.vertical (OriginalGroupBounds.horizontal t).core).core.memory 0x2c134=_
  rw [vertical,horizontal]
  exact load_store_apart _ _ _ _ h.ret


theorem first_count (s : X86Memory.State) (h : StackSafe (s.regs 4)) :
    load32 (OriginalGroupBounds.firstDone s).core.memory 0x2c134=load32 s.memory 0x2c134 := by
  exact box_count (OriginalGroupBounds.firstInput s) _
    (by simp [OriginalGroupBounds.firstInput,put,write])
    (by simpa [OriginalGroupBounds.firstInput,put,write] using h)
theorem second_count (s : X86Memory.State) (h : StackSafe (s.regs 4)) :
    load32 (OriginalGroupBounds.secondDone s).core.memory 0x2c134=load32 s.memory 0x2c134 := by
  exact box_count (OriginalGroupBounds.secondInput s) _
    (by simp [OriginalGroupBounds.secondInput,put,write])
    (by simpa [OriginalGroupBounds.secondInput,put,write] using h)

theorem selected_count (s : X86Memory.State) (h : Apart 0x2c134 (s.regs 6)) :
    load32 (OriginalGroupLines.selected s).core.memory 0x2c134=load32 s.memory 0x2c134 := by
  simp only [OriginalGroupLines.selected,OriginalGroupLines.emitted]
  split
  · exact load_store_apart _ _ _ _ h
  · split
    · exact load_store_apart _ _ _ _ h
    · rfl

/-- The memory premise excludes overlap with the count word, rather than
assuming that the count is preserved by execution. -/
theorem iteration_count (s : X86Memory.State) (h : CountSafe s) :
    load32 (body s).core.memory 0x2c134=load32 s.memory 0x2c134 := by
  have a := first_count (OriginalGroupLines.selected s).core (by simpa [selected_regs] using h.stack)
  have b := second_count (OriginalGroupBounds.firstDone (OriginalGroupLines.selected s).core).core
    (by simpa [(OriginalGroupBounds.first_return _).2,selected_regs] using h.stack)
  cases hh : hit s
  · simp [body,hh,OriginalGroupBounds.advanced,put]
  · change load32 (body s).core.memory 0x2c134=_
    simpa only [body,hh,↓reduceIte,OriginalGroupBounds.result,OriginalGroupBounds.advanced,put] using
      b.trans (a.trans (selected_count s h.output))

/-- The final branch reads the post-write count, even without the count-frame
premise. This distinction matters for deliberately aliased machine states. -/
theorem iteration_exit (s : X86Memory.State) :
    (body s).pc=if (s.regs 7+1).toInt<(load32 (body s).core.memory 0x2c134).toInt then 0x2e676 else 0x2e6af := by
  have a := first_regs (OriginalGroupLines.selected s).core 7 (by decide)
  have b := second_regs (OriginalGroupBounds.firstDone (OriginalGroupLines.selected s).core).core 7 (by decide)
  cases hh : hit s <;> simp [body,hh,OriginalGroupBounds.result,OriginalGroupBounds.advanced,put,write,a,b,selected_regs]

/-- Natural-number progress for a positive signed count: no counter wrap can
occur before this finite scan reaches its bound. -/
theorem iteration_progress (s : X86Memory.State) (h : CountSafe s) (i total : Nat)
    (index : (s.regs 7).toNat=i) (count : (load32 s.memory 0x2c134).toNat=total)
    (inside : i<total) (small : total<2147483648) :
    ((body s).core.regs 7).toNat=i+1 ∧
    (body s).pc=(if i+1<total then 0x2e676 else 0x2e6af) := by
  have next : (s.regs 7+1).toNat=i+1 := by
    simp only [BitVec.toNat_add,index]
    change (i+1)%4294967296=i+1
    omega
  have signedNext : (s.regs 7+1).toInt=(i+1 : Nat) := by
    simp only [BitVec.toInt_eq_toNat_cond,next]; split <;> omega
  have signedCount : (load32 s.memory 0x2c134).toInt=(total : Int) := by
    simp only [BitVec.toInt_eq_toNat_cond,count]; split <;> omega
  constructor
  · rw [(iteration_registers s).1,next]
  · rw [iteration_exit,iteration_count s h,signedNext,signedCount]
    have same : ((i+1 : Nat) : Int)<(total : Int) ↔ i+1<total := by omega
    simp only [same]

end Doom.Proofs.OriginalGroupStep
