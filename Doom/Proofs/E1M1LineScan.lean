import Doom.Proofs.E1M1LineFrame
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1LineScan
open Verification X86 X86Memory X86Control BlockSummary E1M1LineIteration

/-- Cursors retain x86's modular address arithmetic. -/
def cursor (base stride : Word) : Nat → Word
  | 0 => base
  | n+1 => cursor base stride n+stride

/-- Finite storage obligations for preserving the loop's signed count. -/
structure Layout (total : Nat) (line sp : Word) : Prop where
  small : total<2147483648
  count : ∀ i, i<total → E1M1LineFrame.Protected 0x2c134 (cursor line 62 i) sp

structure Ready (total : Nat) (raw line sp : Word) (i : Nat) (s : X86Memory.State) : Prop where
  index : (s.regs 5).toNat=i
  count : (load32 s.memory 0x2c134).toNat=total
  source : s.regs 1=cursor raw 14 i
  output : s.regs 3=cursor line 62 i
  stack : s.regs 4=sp

/-- The pure body already has a decoded-instruction correspondence theorem. -/
def states (s : X86Memory.State) (f : Option Flags) : Nat → X86Control.State
  | 0 => ⟨s,f,0x2e29a⟩
  | n+1 => result (states s f n).core

/-- Only successful diagonal IDIVs are required here. This is NOT a claim that
the pinned WAD certificate has already been linked to initial machine memory. -/
def Arithmetic (total : Nat) (s : X86Memory.State) (f : Option Flags) : Prop :=
  ∀ i, i<total → Safe (states s f i).core

theorem ready_step {total raw line sp i s} (layout : Layout total line sp)
    (ready : Ready total raw line sp i s) (inside : i<total) :
    Ready total raw line sp (i+1) (result s).core ∧
    (result s).pc=(if i+1<total then 0x2e29a else 0x2e3c1) := by
  have protect : E1M1LineFrame.Protected 0x2c134 (s.regs 3) (s.regs 4) := by
    rw [ready.output,ready.stack]; exact layout.count i inside
  have stable := E1M1LineFrame.frame s 0x2c134 protect
  have next : (s.regs 5+1).toNat=i+1 := by
    simp only [BitVec.toNat_add,ready.index]
    change (i+1)%4294967296=i+1
    have := layout.small; omega
  have signedNext : (s.regs 5+1).toInt=(i+1 : Nat) := by
    simp only [BitVec.toInt_eq_toNat_cond,next]
    have := layout.small; split <;> omega
  have signedCount : (load32 s.memory 0x2c134).toInt=(total : Int) := by
    simp only [BitVec.toInt_eq_toNat_cond,ready.count]
    have := layout.small; split <;> omega
  obtain ⟨rawStep,lineStep,indexStep,stackStep⟩ := E1M1LineFrame.progress s
  refine ⟨⟨?_,?_,?_,?_,stackStep.trans ready.stack⟩,?_⟩
  · rw [indexStep,next]
  · rw [stable,ready.count]
  · simpa only [ready.source,cursor] using rawStep
  · simpa only [ready.output,cursor] using lineStep
  · rw [E1M1LineFrame.exit_pc,stable,signedNext,signedCount]
    have same : ((i+1 : Nat) : Int)<(total : Int) ↔ i+1<total := by omega
    simp only [same]

/-- All cursor/count/stack invariants follow from finite layout separation.
No assumption of a successful machine trace or per-step invariant is used. -/
theorem states_ready {total raw line sp s f} (layout : Layout total line sp)
    (initial : Ready total raw line sp 0 s) (n : Nat) (bound : n≤total) :
    Ready total raw line sp n (states s f n).core ∧
      (states s f n).pc=(if n=0 ∨ n<total then 0x2e29a else 0x2e3c1) := by
  induction n with
  | zero => exact ⟨initial,by simp [states]⟩
  | succ n ih =>
    have before := (ih (by omega)).1
    obtain ⟨after,pc⟩ := ready_step layout before (by omega)
    exact ⟨after,by simpa only [states,Nat.add_one_ne_zero,false_or] using pc⟩

/-- Joining the actual instruction prefixes constructs the entire loop path.
Arithmetic safety remains explicit; termination and branch choices are derived. -/
theorem scan_path {total raw line sp s f} (layout : Layout total line sp)
    (initial : Ready total raw line sp 0 s) (arithmetic : Arithmetic total s f)
    (n : Nat) (bound : n≤total) :
    ∃ k≤104*n, X86Routine.Prefix program [0x2e3c1] k ⟨s,f,0x2e29a⟩ (states s f n) := by
  induction n with
  | zero => exact ⟨0,by omega,by constructor⟩
  | succ n ih =>
    obtain ⟨k,hk,path⟩ := ih (by omega)
    obtain ⟨m,hm,body,_⟩ := iteration (states s f n).core (states s f n).flags (arithmetic n (by omega))
    have body := body.transfer program [0x2e3c1] (fun _ _ => rfl) (by
      intro pc hp
      simp only [List.mem_singleton]
      intro eq; subst pc; exact hp (by decide))
    have atLoop : (states s f n).pc=0x2e29a := by
      rw [(states_ready layout initial n (by omega)).2,if_pos (Or.inr (by omega))]
    have eta : (⟨(states s f n).core,(states s f n).flags,0x2e29a⟩ : X86Control.State)=states s f n := by rw [←atLoop]
    rw [eta] at body
    exact ⟨k+m,by omega,OriginalGroupBounds.prefix_join path body⟩

/-- Starts at the first body instruction with a positive count. Allocation,
zero-count entry gate, and cleanup lie outside this interval. -/
theorem scan_execution {total raw line sp s f} (layout : Layout total line sp)
    (initial : Ready total raw line sp 0 s) (arithmetic : Arithmetic total s f)
    (positive : 0<total) :
    X86Routine.run program [0x2e3c1] (104*total) ⟨s,f,0x2e29a⟩=some (states s f total) ∧
    (states s f total).pc=0x2e3c1 ∧ Ready total raw line sp total (states s f total).core := by
  obtain ⟨n,hn,path⟩ := scan_path layout initial arithmetic total (by omega)
  obtain ⟨ready,pc⟩ := states_ready (f:=f) layout initial total (by omega)
  have done : (states s f total).pc=0x2e3c1 := by simpa [show total≠0 by omega] using pc
  have stop : X86Routine.run program [0x2e3c1] 0 (states s f total)=some (states s f total) := by
    simp [X86Routine.run,done]
  exact ⟨path.finish stop _ (by omega),done,ready⟩

/-- 475 original linedef iterations, at most 49,400 decoded instructions.
The byte program includes the actual FixedDiv call, body and return. -/
theorem e1m1_scan {raw line sp s f} (layout : Layout 475 line sp)
    (initial : Ready 475 raw line sp 0 s) (arithmetic : Arithmetic 475 s f) :
    X86Routine.run program [0x2e3c1] 49400 ⟨s,f,0x2e29a⟩=some (states s f 475) ∧
    (states s f 475).pc=0x2e3c1 ∧ Ready 475 raw line sp 475 (states s f 475).core :=
  scan_execution (total:=475) (raw:=raw) (line:=line) (sp:=sp) (s:=s) (f:=f) layout initial arithmetic (by decide)

/-- Any source or earlier output word separated from the remaining records and
stack writes survives their entire suffix. Works without arithmetic assumptions
for the pure states; scan_path connects those states to successful execution. -/
theorem suffix_frame {total raw line sp s f} (layout : Layout total line sp)
    (initial : Ready total raw line sp 0 s) (a : Word) (start count : Nat)
    (bound : start+count≤total)
    (protect : ∀ j, start≤j → j<start+count →
      E1M1LineFrame.Protected a (cursor line 62 j) sp) :
    load32 (states s f (start+count)).core.memory a=load32 (states s f start).core.memory a := by
  induction count with
  | zero => rfl
  | succ count ih =>
    have ready := (states_ready (f:=f) layout initial (start+count) (by omega)).1
    have safe : E1M1LineFrame.Protected a ((states s f (start+count)).core.regs 3)
        ((states s f (start+count)).core.regs 4) := by
      rw [ready.output,ready.stack]; exact protect (start+count) (by omega) (by omega)
    have frame := E1M1LineFrame.frame (states s f (start+count)).core a safe
    exact frame.trans (ih (by omega) (fun j lo hi => protect j lo (by omega)))
end Doom.Proofs.E1M1LineScan
