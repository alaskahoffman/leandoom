import Doom.Proofs.E1M1HistoryDispatch
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1AimHistoryCycle
open Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1MinimumScan (address)
open E1M1SelectionHistory (History)
open E1M1HistoryDispatch (Selection)
open E1M1InterceptMark (consume)
open E1M1AimRepeatProgram (program ReadFrame)
attribute [local irreducible] load32 store32

/-- Reads outside the callback's writes, selected-fraction mark, saved cursor
and next CALL's return word survive the complete cycle. -/
def Frame (s : X86Memory.State) (out : X86Control.State) : Prop :=
  ∀ a, E1M1AimRecordFrame.ReadSafe s a → Apart a (s.regs 3) →
    Apart a 0x2c028 → Apart a (s.regs 4) → load32 out.core.memory a=load32 s.memory a

/-- The next boundary names the original callback slot and parent stack. -/
def Next (s : X86Memory.State) (initial work : Array Intercept) (seen : List Nat)
    (resolve : Intercept → Word) (out : X86Control.State) : Prop :=
  (seen.length=initial.size ∧ out=E1M1AimNextSelection.head (E1M1AimResume.result s).core ∧
    out.core.regs 6=0xffffffff) ∨
  (∃ best, E1M1InterceptMinimum.minimum work=.ok best ∧ best.1>65536 ∧ out.pc=0x2c887 ∧
    out.core.regs 6=BitVec.ofNat 32 (initial.size-seen.length-1)) ∨
  (∃ distance j, Selection initial work seen resolve
    (load32 s.memory (s.regs 4+4)) (s.regs 4+4) out distance j)

/-- Resume from a proved selected hit, deriving the consumed image, cursor and
counter from the callback's real return state rather than new entry assumptions. -/
theorem next (s : X86Memory.State) (f : Option Flags)
    (initial hits : Array Intercept) (seen : List Nat) (visits : Array Intercept)
    (resolve : Intercept → Word) (target sp : Word) (fraction : Int32) (j : Nat)
    (history : History initial hits seen visits)
    (selection : Selection initial hits seen resolve target sp ⟨s,f,0x2b760⟩ fraction j)
    (line front back ff fc bf bc : Word)
    (h : E1M1AimMapped.Inputs s hits[j]! line front back ff fc bf bc)
    (bounded : initial.size≤128) (safe : E1M1AimRecordFrame.RecordsSafe s hits)
    (returnSafe : E1M1AimReturnFrame.Safe s)
    (go : (E1M1AimWindow.result s).core.regs 0≠0)
    (stable : resolve {hits[j]! with frac := ⟨2147483647⟩}=resolve hits[j]!)
    (cursorSafe : E1M1AimRecordFrame.ReadSafe s 0x2c028)
    (targetSafe : Apart (s.regs 4+4) 0x2c028)
    (cursorStore : Apart 0x2c028 (s.regs 4))
    (recordSafe : ∀ i<hits.size, ∀ off∈[(0#32),4,8],
      Apart (OriginalLineCollection.slot 0x2ba20 i off) (s.regs 4)) :
    ∃ n≤13+7*hits.size, ∃ out,
      X86CodeMemory.Prefix FloorCaller.cm program [] n (E1M1AimResume.result s) out ∧
      ReadFrame (E1M1AimResume.result s).core out ∧
      E1M1HistoryDispatch.Outcome (E1M1AimResume.result s).core initial (consume hits j) (j::seen) resolve out := by
  have size := (E1M1SelectionHistory.image history).size
  have inside : j<hits.size := by have := selection.inside; omega
  have pointer : s.regs 3=address j := selection.ready.pointer.trans selection.argument
  have r := E1M1AimRecordFrame.registers s hits[j]! line front back ff fc bf bc h returnSafe cursorSafe
  have encoded := E1M1AimRecordFrame.resumed_records s hits[j]! line front back ff fc bf bc h
    hits resolve j inside (by omega) selection.ready.records safe returnSafe pointer go stable
  have advanced := History.push history fraction j selection.chosen selection.within
  obtain ⟨n,hn,out,run,frame,done⟩ := E1M1HistoryDispatch.execution
    (E1M1AimResume.result s).core (E1M1AimResume.result s).flags
    initial (consume hits j) (j::seen) (visits.push hits[j]!) resolve advanced bounded
    (r.2.2.1.trans selection.counter)
    (by rw [E1M1InterceptMark.size]; exact r.1.trans selection.ready.cursor) encoded
    (r.2.2.2.trans selection.maximum) (by rw [r.2.1]; exact targetSafe)
    (by rw [r.2.1]; simpa [BitVec.add_sub_cancel] using cursorStore)
    (by rw [r.2.1]; simpa [E1M1InterceptMark.size,BitVec.add_sub_cancel] using recordSafe)
  have pc : (E1M1AimResume.result s).pc=0x2c83a := by
    simp only [E1M1AimResume.result,OriginalInterceptGate.resumed,if_neg go]
  rw [OriginalPathXStep.at_pc _ _ pc] at run
  exact ⟨n,by simpa only [E1M1InterceptMark.size] using hn,out,run,frame,done⟩

/-- Carry the indirect destination across the callback and its parent mark. -/
theorem carried (s : X86Memory.State) (hit : Intercept) (line front back ff fc bf bc : Word)
    (h : E1M1AimMapped.Inputs s hit line front back ff fc bf bc)
    (returnSafe : E1M1AimReturnFrame.Safe s) (cursorSafe : E1M1AimRecordFrame.ReadSafe s 0x2c028)
    (slotSafe : E1M1AimRecordFrame.ReadSafe s (s.regs 4+4))
    (slotMark : Apart (s.regs 4+4) (s.regs 3))
    (initial work : Array Intercept) (seen : List Nat) (resolve : Intercept → Word)
    (out : X86Control.State)
    (done : E1M1HistoryDispatch.Outcome (E1M1AimResume.result s).core initial work seen resolve out) :
    Next s initial work seen resolve out := by
  have r := E1M1AimRecordFrame.registers s hit line front back ff fc bf bc h returnSafe cursorSafe
  have slot := E1M1AimRecordFrame.resumed_frame s hit line front back ff fc bf bc
    (s.regs 4+4) h slotSafe returnSafe slotMark
  unfold E1M1HistoryDispatch.Outcome at done
  rw [r.2.1] at done
  change load32 (E1M1AimResume.result s).core.memory (s.regs 4+(4#32))=_ at slot
  rw [slot] at done
  exact done

/-- Execute the selected open two-sided line, both clipping branches, its real
return and parent decision, and the next selection. Only the continuing branch
advances the consumed-buffer history; both branches retain exact clipped bounds. -/
theorem execution (s : X86Memory.State) (f : Option Flags)
    (initial hits : Array Intercept) (seen : List Nat) (visits : Array Intercept)
    (resolve : Intercept → Word) (target sp : Word) (fraction : Int32) (j : Nat)
    (history : History initial hits seen visits)
    (selection : Selection initial hits seen resolve target sp ⟨s,f,0x2b760⟩ fraction j)
    (line front back ff fc bf bc : Word) (distance z lower upper floorSlope ceilingSlope : Fixed)
    (h : E1M1AimMapped.Inputs s hits[j]! line front back ff fc bf bc)
    (distanceReads : E1M1AimDistance.ReadSafe s) (floorReads : E1M1AimFloorEntry.ReadSafe s)
    (reads : E1M1AimCeilingEntry.ReadSafe s) (clip : E1M1AimCeilingEntry.ClipSafe s line front back)
    (range : load32 s.memory (0x2b9b8#32)=distance.raw.toBitVec)
    (eye : load32 s.memory (0x2b9a8#32)=z.raw.toBitVec)
    (bottom : load32 s.memory (0x2c1e4#32)=lower.raw.toBitVec)
    (top : load32 s.memory (0x2c1e8#32)=upper.raw.toBitVec)
    (pass : (if ff.toInt≤bf.toInt then bf else ff).toInt < (if bc.toInt≤fc.toInt then bc else fc).toInt)
    (floorOk : bf≠ff → checkedPathDiv (⟨Int32.ofBitVec (if ff.toInt≤bf.toInt then bf else ff)⟩-z)
      (distance*hits[j]!.frac)=.ok floorSlope)
    (ceilingOk : fc≠bc → checkedPathDiv (⟨Int32.ofBitVec (if bc.toInt≤fc.toInt then bc else fc)⟩-z)
      (distance*hits[j]!.frac)=.ok ceilingSlope)
    (returnSafe : E1M1AimReturnFrame.Safe s)
    (markSafe : Apart (0x2c1e4#32) (s.regs 3) ∧ Apart (0x2c1e8#32) (s.regs 3))
    (bounded : initial.size≤128)
    (safe : E1M1AimRecordFrame.RecordsSafe s hits)
    (stable : resolve {hits[j]! with frac := ⟨2147483647⟩}=resolve hits[j]!)
    (cursorSafe : E1M1AimRecordFrame.ReadSafe s 0x2c028)
    (targetSafe : Apart (s.regs 4+4) 0x2c028)
    (cursorStore : Apart 0x2c028 (s.regs 4))
    (recordSafe : ∀ i<hits.size, ∀ off∈[(0#32),4,8],
      Apart (OriginalLineCollection.slot 0x2ba20 i off) (s.regs 4))
    (boundsSafe : Apart (0x2c1e4#32) (s.regs 4) ∧ Apart (0x2c1e8#32) (s.regs 4))
    (slotSafe : E1M1AimRecordFrame.ReadSafe s (s.regs 4+4))
    (slotMark : Apart (s.regs 4+4) (s.regs 3)) :
    ∃ n≤157+7*hits.size, ∃ out,
      X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2b760⟩ out ∧
      (if (if bf=ff then lower.raw else max lower.raw floorSlope.raw).toInt <
          (if fc=bc then upper.raw else min upper.raw ceilingSlope.raw).toInt then
        History initial (consume hits j) (j::seen) (visits.push hits[j]!) ∧
        Next s initial (consume hits j) (j::seen) resolve out
       else out=E1M1AimResume.result s ∧ out.pc=0x2c88c) ∧
      load32 out.core.memory (0x2c1e4#32)=(if bf=ff then lower.raw else max lower.raw floorSlope.raw).toBitVec ∧
      load32 out.core.memory (0x2c1e8#32)=(if fc=bc then upper.raw else min upper.raw ceilingSlope.raw).toBitVec ∧ Frame s out := by
  have first := E1M1AimResume.execution s f hits[j]! line front back ff fc bf bc distance z lower upper floorSlope ceilingSlope
    h distanceReads floorReads reads clip range eye bottom top pass floorOk ceilingOk returnSafe selection.ready.returnWord markSafe
  obtain ⟨n,hn,run⟩ := first.1
  have run := run.transfer program [] E1M1AimRepeatProgram.contains_resume (by simp)
  have bounds := first.2.2.2.2.2
  by_cases openWindow : (if bf=ff then lower.raw else max lower.raw floorSlope.raw).toInt <
      (if fc=bc then upper.raw else min upper.raw ceilingSlope.raw).toInt
  · have go : (E1M1AimWindow.result s).core.regs 0≠0 := by
      intro zero
      have pc : (E1M1AimResume.result s).pc=0x2c88c := by
        simp only [E1M1AimResume.result,OriginalInterceptGate.resumed,if_pos zero]
      rw [first.2.1,if_pos openWindow] at pc
      contradiction
    obtain ⟨k,hk,out,tail,frame,done⟩ := next s f initial hits seen visits resolve target sp fraction j
      history selection line front back ff fc bf bc h bounded safe returnSafe go stable cursorSafe targetSafe cursorStore recordSafe
    have nextOut := carried s hits[j]! line front back ff fc bf bc h returnSafe cursorSafe
      slotSafe slotMark initial (consume hits j) (j::seen) resolve out done
    refine ⟨n+k,by omega,out,E1M1PspriteStep.prefix_trans run tail,?_,?_,?_,?_⟩
    · simpa only [if_pos openWindow] using
        And.intro (History.push history fraction j selection.chosen selection.within) nextOut
    · exact (frame (0x2c1e4#32) (by unfold Apart; decide) (by
        rw [first.2.2.1]; simpa [BitVec.add_sub_cancel] using boundsSafe.1)).trans bounds.1
    · exact (frame (0x2c1e8#32) (by unfold Apart; decide) (by
        rw [first.2.2.1]; simpa [BitVec.add_sub_cancel] using boundsSafe.2)).trans bounds.2
    · intro a read mark cursor stack
      exact (frame a cursor (by rw [first.2.2.1]; simpa [BitVec.add_sub_cancel] using stack)).trans
        (E1M1AimRecordFrame.resumed_frame s hits[j]! line front back ff fc bf bc a h read returnSafe mark)
  · refine ⟨n,by omega,E1M1AimResume.result s,run,?_,bounds.1,bounds.2,?_⟩
    · simp only [if_neg openWindow]
      exact ⟨True.intro,by simpa only [if_neg openWindow] using first.2.1⟩
    · intro a read mark cursor stack
      exact E1M1AimRecordFrame.resumed_frame s hits[j]! line front back ff fc bf bc a h read returnSafe mark

end Doom.Proofs.E1M1AimHistoryCycle
