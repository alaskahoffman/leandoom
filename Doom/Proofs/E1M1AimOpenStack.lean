import Doom.Proofs.E1M1AimStackShape
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1AimOpenStack
open Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1MinimumScan (address)
open E1M1SelectionHistory (History)
open E1M1HistoryDispatch (Selection)
open E1M1InterceptMark (consume)
open E1M1AimRepeatProgram (program ReadFrame)
attribute [local irreducible] load32 store32

open E1M1AimStackShape (Shape)
open E1M1AimHistoryCycle (Next carried Frame)
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
    (slotMark : Apart (s.regs 4+4) (s.regs 3))
    (callback : load32 s.memory (s.regs 4+4)=0x2b760) :
    ∃ n≤157+7*hits.size, ∃ out,
      Shape (s.regs 4+4) out ∧
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
    obtain ⟨k,hk,out,tail,frame,done,stack⟩ := E1M1AimLineScanStack.execution s f initial hits seen visits resolve target sp fraction j
      history selection line front back ff fc bf bc h bounded safe returnSafe go stable cursorSafe targetSafe cursorStore recordSafe
    have shape := E1M1AimStackShape.scan _ out (E1M1AimLineScanStack.position s hits[j]!
      line front back ff fc bf bc h returnSafe cursorSafe slotSafe slotMark callback out stack)
    have nextOut := carried s hits[j]! line front back ff fc bf bc h returnSafe cursorSafe
      slotSafe slotMark initial (consume hits j) (j::seen) resolve out done
    refine ⟨n+k,by omega,out,shape,E1M1PspriteStep.prefix_trans run tail,?_,?_,?_,?_⟩
    · simpa only [if_pos openWindow] using
        And.intro (History.push history fraction j selection.chosen selection.within) nextOut
    · exact (frame (0x2c1e4#32) (by unfold Apart; decide) (by
        rw [first.2.2.1]; simpa [BitVec.add_sub_cancel] using boundsSafe.1)).trans bounds.1
    · exact (frame (0x2c1e8#32) (by unfold Apart; decide) (by
        rw [first.2.2.1]; simpa [BitVec.add_sub_cancel] using boundsSafe.2)).trans bounds.2
    · intro a read mark cursor stack
      exact (frame a cursor (by rw [first.2.2.1]; simpa [BitVec.add_sub_cancel] using stack)).trans
        (E1M1AimRecordFrame.resumed_frame s hits[j]! line front back ff fc bf bc a h read returnSafe mark)
  · refine ⟨n,by omega,E1M1AimResume.result s,
      E1M1AimStackShape.stopped _ _ (by simpa only [if_neg openWindow] using first.2.1) first.2.2.1,run,?_,bounds.1,bounds.2,?_⟩
    · simp only [if_neg openWindow]
      exact ⟨True.intro,by simpa only [if_neg openWindow] using first.2.1⟩
    · intro a read mark cursor stack
      exact E1M1AimRecordFrame.resumed_frame s hits[j]! line front back ff fc bf bc a h read returnSafe mark

end Doom.Proofs.E1M1AimOpenStack
