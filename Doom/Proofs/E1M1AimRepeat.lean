import Doom.Proofs.E1M1AimRepeatProgram
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1AimRepeat
open Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1MinimumScan (address)
open E1M1AimRepeatProgram (program ReadFrame repeat_selection)
attribute [local irreducible] load32 store32

theorem next (s : X86Memory.State) (hit : Intercept) (line front back ff fc bf bc : Word)
    (h : E1M1AimMapped.Inputs s hit line front back ff fc bf bc)
    (hits : Array Intercept) (resolve : Intercept → Word) (j : Nat)
    (inside : j<hits.size) (bounded : hits.size≤128)
    (image : OriginalLineFinish.Encodes s.memory 0x2ba20 resolve hits)
    (safe : E1M1AimRecordFrame.RecordsSafe s hits) (returnSafe : E1M1AimReturnFrame.Safe s)
    (pointer : s.regs 3=address j) (go : (E1M1AimWindow.result s).core.regs 0≠0)
    (stable : resolve {hits[j]! with frac := ⟨2147483647⟩}=resolve hits[j]!)
    (cursorSafe : E1M1AimRecordFrame.ReadSafe s 0x2c028)
    (cursor : load32 s.memory 0x2c028=address hits.size) (maximum : s.regs 7=65536)
    (targetSafe : Apart (s.regs 4+4) 0x2c028)
    (recordSafe : ∀ i<hits.size, ∀ off∈[(0#32),4,8],
      Apart (OriginalLineCollection.slot 0x2ba20 i off) (s.regs 4)) :
    ∃ n≤13+7*hits.size, ∃ out,
      X86CodeMemory.Prefix FloorCaller.cm program [] n (E1M1AimResume.result s) out ∧
      E1M1AimNextSelection.Outcome (E1M1AimResume.result s).core (E1M1InterceptMark.consume hits j) resolve out ∧ ReadFrame (E1M1AimResume.result s).core out := by
  have r := E1M1AimRecordFrame.registers s hit line front back ff fc bf bc h returnSafe cursorSafe
  have image' := E1M1AimRecordFrame.resumed_records s hit line front back ff fc bf bc h hits resolve j inside bounded image safe returnSafe pointer go stable
  obtain ⟨n,hn,out,run,done,frame⟩ := repeat_selection (E1M1AimResume.result s).core (E1M1AimResume.result s).flags
    (E1M1InterceptMark.consume hits j) resolve
    (by simpa only [E1M1InterceptMark.size] using bounded)
    (by rw [E1M1InterceptMark.size]; omega)
    (by rw [E1M1InterceptMark.size]; exact r.1.trans cursor) image'
    (r.2.2.2.trans maximum) (by rw [r.2.1]; exact targetSafe)
    (by rw [r.2.1]; simpa [E1M1InterceptMark.size,BitVec.add_sub_cancel] using recordSafe)
  have pc : (E1M1AimResume.result s).pc=0x2c83a := by
    simp only [E1M1AimResume.result,OriginalInterceptGate.resumed,if_neg go]
  rw [OriginalPathXStep.at_pc _ _ pc] at run
  exact ⟨n,by simpa only [E1M1InterceptMark.size] using hn,out,run,done,frame⟩
/-- Continuous original execution from callback entry through its parent and
next selection. Continuation is derived from the clipped window; the next callback
retains those exact bounds and the initial indirect target. -/
theorem execution (s : X86Memory.State) (f : Option Flags) (hit : Intercept)
    (line front back ff fc bf bc : Word) (distance z lower upper floorSlope ceilingSlope : Fixed)
    (h : E1M1AimMapped.Inputs s hit line front back ff fc bf bc)
    (distanceReads : E1M1AimDistance.ReadSafe s) (floorReads : E1M1AimFloorEntry.ReadSafe s)
    (reads : E1M1AimCeilingEntry.ReadSafe s) (clip : E1M1AimCeilingEntry.ClipSafe s line front back)
    (range : load32 s.memory (0x2b9b8#32)=distance.raw.toBitVec)
    (eye : load32 s.memory (0x2b9a8#32)=z.raw.toBitVec)
    (bottom : load32 s.memory (0x2c1e4#32)=lower.raw.toBitVec)
    (top : load32 s.memory (0x2c1e8#32)=upper.raw.toBitVec)
    (pass : (if ff.toInt≤bf.toInt then bf else ff).toInt < (if bc.toInt≤fc.toInt then bc else fc).toInt)
    (floorOk : bf≠ff → checkedPathDiv (⟨Int32.ofBitVec (if ff.toInt≤bf.toInt then bf else ff)⟩-z)
      (distance*hit.frac)=.ok floorSlope)
    (ceilingOk : fc≠bc → checkedPathDiv (⟨Int32.ofBitVec (if bc.toInt≤fc.toInt then bc else fc)⟩-z)
      (distance*hit.frac)=.ok ceilingSlope)
    (returnSafe : E1M1AimReturnFrame.Safe s)
    (returnWord : load32 s.memory (s.regs 4)=0x2c86d)
    (markSafe : Apart (0x2c1e4#32) (s.regs 3) ∧ Apart (0x2c1e8#32) (s.regs 3))
    (hits : Array Intercept) (resolve : Intercept → Word) (j : Nat)
    (inside : j<hits.size) (bounded : hits.size≤128)
    (image : OriginalLineFinish.Encodes s.memory 0x2ba20 resolve hits)
    (safe : E1M1AimRecordFrame.RecordsSafe s hits)
    (pointer : s.regs 3=address j)
    (stable : resolve {hits[j]! with frac := ⟨2147483647⟩}=resolve hits[j]!)
    (cursorSafe : E1M1AimRecordFrame.ReadSafe s 0x2c028)
    (cursor : load32 s.memory 0x2c028=address hits.size) (maximum : s.regs 7=65536)
    (targetSafe : Apart (s.regs 4+4) 0x2c028)
    (recordSafe : ∀ i<hits.size, ∀ off∈[(0#32),4,8],
      Apart (OriginalLineCollection.slot 0x2ba20 i off) (s.regs 4))
    (boundsSafe : Apart (0x2c1e4#32) (s.regs 4) ∧ Apart (0x2c1e8#32) (s.regs 4))
    (slotSafe : E1M1AimRecordFrame.ReadSafe s (s.regs 4+4))
    (slotMark : Apart (s.regs 4+4) (s.regs 3)) :
    ∃ n≤157+7*hits.size, ∃ out,
      X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2b760⟩ out ∧
      (if (if bf=ff then lower.raw else max lower.raw floorSlope.raw).toInt <
          (if fc=bc then upper.raw else min upper.raw ceilingSlope.raw).toInt then
        (s.regs 6=0 ∧ out=E1M1AimNextSelection.head (E1M1AimResume.result s).core) ∨
        (s.regs 6≠0 ∧ E1M1CallbackEntry.Outcome (E1M1InterceptMark.consume hits j) resolve
          (load32 s.memory (s.regs 4+4)) (s.regs 4+4) out)
       else out=E1M1AimResume.result s ∧ out.pc=0x2c88c) ∧
      load32 out.core.memory (0x2c1e4#32)=(if bf=ff then lower.raw else max lower.raw floorSlope.raw).toBitVec ∧
      load32 out.core.memory (0x2c1e8#32)=(if fc=bc then upper.raw else min upper.raw ceilingSlope.raw).toBitVec := by
  have first := E1M1AimResume.execution s f hit line front back ff fc bf bc distance z lower upper floorSlope ceilingSlope
    h distanceReads floorReads reads clip range eye bottom top pass floorOk ceilingOk returnSafe returnWord markSafe
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
    obtain ⟨k,hk,out,tail,done,frame⟩ := next s hit line front back ff fc bf bc h hits resolve j inside bounded
      image safe returnSafe pointer go stable cursorSafe cursor maximum targetSafe recordSafe
    have carried := E1M1AimNextSelection.carried_outcome s hit line front back ff fc bf bc h returnSafe cursorSafe
      slotSafe slotMark (E1M1InterceptMark.consume hits j) resolve out done
    refine ⟨n+k,by omega,out,E1M1PspriteStep.prefix_trans run tail,by simpa only [if_pos openWindow] using carried,?_,?_⟩
    · exact (frame (0x2c1e4#32) (by unfold Apart; decide) (by
        rw [first.2.2.1]; simpa [BitVec.add_sub_cancel] using boundsSafe.1)).trans bounds.1
    · exact (frame (0x2c1e8#32) (by unfold Apart; decide) (by
        rw [first.2.2.1]; simpa [BitVec.add_sub_cancel] using boundsSafe.2)).trans bounds.2
  · refine ⟨n,by omega,E1M1AimResume.result s,run,?_,bounds⟩
    simp only [if_neg openWindow]
    exact ⟨True.intro,by simpa only [if_neg openWindow] using first.2.1⟩

end Doom.Proofs.E1M1AimRepeat
