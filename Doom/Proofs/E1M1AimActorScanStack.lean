import Doom.Proofs.E1M1AimScanStack
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimActorScanStack
open Verification X86 X86Memory X86Control BlockSummary Collision E1M1SelectionHistory
open E1M1HistoryDispatch (Selection)
open E1M1MinimumScan (address)
open E1M1InterceptMark (consume)
open E1M1AimHistoryCycle (Frame)
attribute [local irreducible] load32 store32 SolidThing.shootHeight
theorem skipped (s : X86Memory.State) (f : Option Flags)
    (initial work : Array Intercept) (seen : List Nat) (visits : Array Intercept)
    (resolve : Intercept → Word) (target sp : Word) (fraction : Int32) (j : Nat)
    (selection : Selection initial work seen resolve target sp ⟨s,f,0x2b760⟩ fraction j)
    (layout : E1M1AimCycleInvariant.Layout s work) (bounded : initial.size≤128)
    (history : History initial (consume work j) (j::seen) (visits.push work[j]!))
    (encoded : OriginalLineFinish.Encodes (E1M1AimActorSkip.result s).core.memory 0x2ba20 resolve (consume work j)) :
    ∃ n≤13+7*work.size, ∃ out,
      X86CodeMemory.Prefix FloorCaller.cm E1M1AimActorSkip.program [] n (E1M1AimActorSkip.result s) out ∧
      E1M1AimRepeatProgram.ReadFrame (E1M1AimActorSkip.result s).core out ∧
      E1M1HistoryDispatch.Outcome (E1M1AimActorSkip.result s).core initial (consume work j) (j::seen) resolve out ∧
      E1M1AimScanStack.Position (load32 (E1M1AimActorSkip.result s).core.memory ((E1M1AimActorSkip.result s).core.regs 4))
        (s.regs 4+4) out := by
  have r := E1M1AimActorSkipCycle.registers s layout.cursorSafe.1
  obtain ⟨n,hn,out,run,keep,done,stack⟩ := E1M1AimScanStack.execution
    (E1M1AimActorSkip.result s).core (E1M1AimActorSkip.result s).flags initial (consume work j) (j::seen) (visits.push work[j]!) resolve
    history bounded (r.2.2.1.trans selection.counter)
    (by rw [E1M1InterceptMark.size]; exact r.1.trans selection.ready.cursor) encoded
    (r.2.2.2.1.trans selection.maximum) (by rw [r.2.1]; exact layout.targetSafe)
    (by rw [r.2.1]; simpa [BitVec.add_sub_cancel] using layout.cursorStore)
    (by rw [r.2.1]; simpa [E1M1InterceptMark.size,BitVec.add_sub_cancel] using layout.recordStore)
  have run := run.transfer E1M1AimActorSkip.program [] E1M1AimActorSkip.contains_repeat (by simp)
  rw [OriginalPathXStep.at_pc _ _ r.2.2.2.2.2] at run
  exact ⟨n,by simpa only [E1M1InterceptMark.size] using hn,out,run,keep,done,by simpa only [r.2.1] using stack⟩


theorem top_rejected (s : X86Memory.State) (f : Option Flags)
    (initial work : Array Intercept) (seen : List Nat) (visits : Array Intercept)
    (resolve : Intercept → Word) (target sp : Word) (fraction : Int32) (j : Nat)
    (history : History initial work seen visits)
    (selection : Selection initial work seen resolve target sp ⟨s,f,0x2b760⟩ fraction j)
    (layout : E1M1AimCycleInvariant.Layout s work) (bounded : initial.size≤128)
    (stable : resolve {work[j]! with frac:=⟨2147483647⟩}=resolve work[j]!) :
    ∃ n≤13+7*work.size, ∃ out,
      X86CodeMemory.Prefix FloorCaller.cm E1M1AimActorReject.program [] n (E1M1AimActorReject.result s) out ∧
      History initial (consume work j) (j::seen) (visits.push work[j]!) ∧
      E1M1AimRepeatProgram.ReadFrame (E1M1AimActorReject.result s).core out ∧ Frame s out ∧
      E1M1HistoryDispatch.Outcome (E1M1AimActorReject.result s).core initial (consume work j) (j::seen) resolve out ∧
      E1M1AimScanStack.Position (load32 (E1M1AimActorReject.result s).core.memory ((E1M1AimActorReject.result s).core.regs 4))
        (s.regs 4+4) out := by
  have r := E1M1AimActorReject.registers s
  have size := (E1M1SelectionHistory.image history).size
  have inside : j<work.size := by have := selection.inside; omega
  have ptr : s.regs 3=address j := selection.ready.pointer.trans selection.argument
  have encoded : OriginalLineFinish.Encodes (E1M1AimActorReject.result s).core.memory 0x2ba20 resolve (consume work j) := by
    rw [r.2.2.2.2.2.2,ptr]
    exact E1M1InterceptMark.encoded _ work resolve j inside (by omega)
      (E1M1AimActorRejectCycle.records s work resolve selection.ready.records layout.recordsSafe) stable
  have cursor := E1M1AimActorReject.read_frame s 0x2c028 (E1M1AimActorRejectCycle.read_safe s _ layout.cursorSafe)
  have advanced := History.push history fraction j selection.chosen selection.within
  obtain ⟨n,hn,out,run,keep,done,stack⟩ := E1M1AimScanStack.execution
    (E1M1AimActorReject.result s).core (E1M1AimActorReject.result s).flags initial (consume work j) (j::seen) (visits.push work[j]!) resolve
    advanced bounded (r.2.2.2.1.trans selection.counter)
    (by rw [E1M1InterceptMark.size]; exact r.2.2.2.2.2.1.trans (cursor.trans selection.ready.cursor)) encoded
    (r.2.2.2.2.1.trans selection.maximum) (by rw [r.2.1]; exact layout.targetSafe)
    (by rw [r.2.1]; simpa [BitVec.add_sub_cancel] using layout.cursorStore)
    (by rw [r.2.1]; simpa [E1M1InterceptMark.size,BitVec.add_sub_cancel] using layout.recordStore)
  have run := run.transfer E1M1AimActorReject.program [] E1M1AimActorReject.contains_repeat (by simp)
  rw [OriginalPathXStep.at_pc _ _ r.1] at run
  refine ⟨n,by simpa only [E1M1InterceptMark.size] using hn,out,run,advanced,keep,?_,done,by simpa only [r.2.1] using stack⟩
  intro a safe mark cursor stack
  exact (keep a cursor (by rw [r.2.1]; simpa [BitVec.add_sub_cancel] using stack)).trans
    (E1M1AimActorReject.frame s a (E1M1AimActorRejectCycle.read_safe s a safe) mark)


theorem bottom_rejected (s : X86Memory.State) (f : Option Flags)
    (initial work : Array Intercept) (seen : List Nat) (visits : Array Intercept)
    (resolve : Intercept → Word) (target sp : Word) (fraction : Int32) (j : Nat)
    (history : History initial work seen visits)
    (selection : Selection initial work seen resolve target sp ⟨s,f,0x2b760⟩ fraction j)
    (layout : E1M1AimCycleInvariant.Layout s work) (bounded : initial.size≤128)
    (stable : resolve {work[j]! with frac:=⟨2147483647⟩}=resolve work[j]!) :
    ∃ n≤13+7*work.size, ∃ out,
      X86CodeMemory.Prefix FloorCaller.cm E1M1AimActorBottom.program [] n (E1M1AimActorBottomReject.result s) out ∧
      History initial (consume work j) (j::seen) (visits.push work[j]!) ∧
      E1M1AimRepeatProgram.ReadFrame (E1M1AimActorBottomReject.result s).core out ∧ Frame s out ∧
      E1M1HistoryDispatch.Outcome (E1M1AimActorBottomReject.result s).core initial (consume work j) (j::seen) resolve out ∧
      E1M1AimScanStack.Position (load32 (E1M1AimActorBottomReject.result s).core.memory ((E1M1AimActorBottomReject.result s).core.regs 4))
        (s.regs 4+4) out := by
  have r := E1M1AimActorBottomReject.registers s
  have size := (E1M1SelectionHistory.image history).size
  have inside : j<work.size := by have := selection.inside; omega
  have ptr : s.regs 3=address j := selection.ready.pointer.trans selection.argument
  have encoded : OriginalLineFinish.Encodes (E1M1AimActorBottomReject.result s).core.memory 0x2ba20 resolve (consume work j) := by
    rw [r.2.2.2.2.2.2,ptr]
    exact E1M1InterceptMark.encoded _ work resolve j inside (by omega)
      (E1M1AimActorBottomCycle.records s work resolve selection.ready.records layout.recordsSafe) stable
  have cursor := E1M1AimActorBottomReject.read_frame s 0x2c028 (E1M1AimActorBottomCycle.read_safe s _ layout.cursorSafe)
  have advanced := History.push history fraction j selection.chosen selection.within
  obtain ⟨n,hn,out,run,keep,done,stack⟩ := E1M1AimScanStack.execution
    (E1M1AimActorBottomReject.result s).core (E1M1AimActorBottomReject.result s).flags initial (consume work j) (j::seen) (visits.push work[j]!) resolve
    advanced bounded (r.2.2.2.1.trans selection.counter)
    (by rw [E1M1InterceptMark.size]; exact r.2.2.2.2.2.1.trans (cursor.trans selection.ready.cursor)) encoded
    (r.2.2.2.2.1.trans selection.maximum) (by rw [r.2.1]; exact layout.targetSafe)
    (by rw [r.2.1]; simpa [BitVec.add_sub_cancel] using layout.cursorStore)
    (by rw [r.2.1]; simpa [E1M1InterceptMark.size,BitVec.add_sub_cancel] using layout.recordStore)
  have run := run.transfer E1M1AimActorBottom.program [] E1M1AimActorBottomReject.contains_repeat (by simp)
  rw [OriginalPathXStep.at_pc _ _ r.1] at run
  refine ⟨n,by simpa only [E1M1InterceptMark.size] using hn,out,run,advanced,keep,?_,done,by simpa only [r.2.1] using stack⟩
  intro a safe mark cursor stack
  exact (keep a cursor (by rw [r.2.1]; simpa [BitVec.add_sub_cancel] using stack)).trans
    (E1M1AimActorBottomReject.frame s a (E1M1AimActorBottomCycle.read_safe s a safe) mark)


open E1M1AimCatalog (Portal)
open E1M1AimTraversalInvariant (Persistent)

/-- Recover the real aiming destination from the incoming invariant and the
proved callback memory frame; it is not assumed at the reached scan state. -/
theorem skipped_position (s : X86Memory.State) (initial work : Array Intercept)
    (resolve : Intercept → Word) (portals : Nat → Option Portal) (distance z : Fixed)
    (out : X86Control.State) (marked : Nat)
    (before : Persistent s initial work resolve portals distance z)
    (pointer : s.regs 3=address marked) (inside : marked<initial.size)
    (stack : E1M1AimScanStack.Position
      (load32 (E1M1AimActorSkip.result s).core.memory ((E1M1AimActorSkip.result s).core.regs 4))
      (s.regs 4+4) out) :
    E1M1AimScanStack.Position 0x2b760 (s.regs 4+4) out := by
  have r := E1M1AimActorSkipCycle.registers s before.layout.cursorSafe.1
  have slot := E1M1AimActorSkipCycle.frame s (s.regs 4+4) before.layout.slotSafe.1
    (by rw [pointer]; exact before.slotMarks marked inside)
  rw [r.2.1,slot,before.callback] at stack
  exact stack

/-- Recover the real aiming destination from the incoming invariant and the
proved callback memory frame; it is not assumed at the reached scan state. -/
theorem top_rejected_position (s : X86Memory.State) (initial work : Array Intercept)
    (resolve : Intercept → Word) (portals : Nat → Option Portal) (distance z : Fixed)
    (out : X86Control.State) (marked : Nat)
    (before : Persistent s initial work resolve portals distance z)
    (pointer : s.regs 3=address marked) (inside : marked<initial.size)
    (stack : E1M1AimScanStack.Position
      (load32 (E1M1AimActorReject.result s).core.memory ((E1M1AimActorReject.result s).core.regs 4))
      (s.regs 4+4) out) :
    E1M1AimScanStack.Position 0x2b760 (s.regs 4+4) out := by
  have r := E1M1AimActorReject.registers s
  have slot := E1M1AimActorReject.frame s (s.regs 4+4) (E1M1AimActorRejectCycle.read_safe s _ before.layout.slotSafe)
    (by rw [pointer]; exact before.slotMarks marked inside)
  rw [r.2.1,slot,before.callback] at stack
  exact stack

/-- Recover the real aiming destination from the incoming invariant and the
proved callback memory frame; it is not assumed at the reached scan state. -/
theorem bottom_rejected_position (s : X86Memory.State) (initial work : Array Intercept)
    (resolve : Intercept → Word) (portals : Nat → Option Portal) (distance z : Fixed)
    (out : X86Control.State) (marked : Nat)
    (before : Persistent s initial work resolve portals distance z)
    (pointer : s.regs 3=address marked) (inside : marked<initial.size)
    (stack : E1M1AimScanStack.Position
      (load32 (E1M1AimActorBottomReject.result s).core.memory ((E1M1AimActorBottomReject.result s).core.regs 4))
      (s.regs 4+4) out) :
    E1M1AimScanStack.Position 0x2b760 (s.regs 4+4) out := by
  have r := E1M1AimActorBottomReject.registers s
  have slot := E1M1AimActorBottomReject.frame s (s.regs 4+4) (E1M1AimActorBottomCycle.read_safe s _ before.layout.slotSafe)
    (by rw [pointer]; exact before.slotMarks marked inside)
  rw [r.2.1,slot,before.callback] at stack
  exact stack
end Doom.Proofs.E1M1AimActorScanStack
