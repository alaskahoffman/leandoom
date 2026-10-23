import Doom.Proofs.E1M1AimActorScanStack
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimLineScanStack
open Verification X86 X86Memory X86Control BlockSummary Collision E1M1SelectionHistory
open E1M1HistoryDispatch (Selection)
open E1M1MinimumScan (address)
open E1M1InterceptMark (consume)
open E1M1AimHistoryCycle (Frame)
attribute [local irreducible] load32 store32 SolidThing.shootHeight
open E1M1AimRepeatProgram (program ReadFrame)
theorem execution (s : X86Memory.State) (f : Option Flags)
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
      E1M1HistoryDispatch.Outcome (E1M1AimResume.result s).core initial (consume hits j) (j::seen) resolve out ∧
      E1M1AimScanStack.Position (load32 (E1M1AimResume.result s).core.memory ((E1M1AimResume.result s).core.regs 4))
        (s.regs 4+4) out := by
  have size := (E1M1SelectionHistory.image history).size
  have inside : j<hits.size := by have := selection.inside; omega
  have pointer : s.regs 3=address j := selection.ready.pointer.trans selection.argument
  have r := E1M1AimRecordFrame.registers s hits[j]! line front back ff fc bf bc h returnSafe cursorSafe
  have encoded := E1M1AimRecordFrame.resumed_records s hits[j]! line front back ff fc bf bc h
    hits resolve j inside (by omega) selection.ready.records safe returnSafe pointer go stable
  have advanced := History.push history fraction j selection.chosen selection.within
  obtain ⟨n,hn,out,run,frame,done,stack⟩ := E1M1AimScanStack.execution
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
  exact ⟨n,by simpa only [E1M1InterceptMark.size] using hn,out,run,frame,done,by simpa only [r.2.1,show (4 : Word)=(4#32) from rfl] using stack⟩


/-- The continuing line callback preserves the indirect destination used by the
following scan, including the selected-fraction mark. -/
theorem position (s : X86Memory.State) (hit : Intercept) (line front back ff fc bf bc : Word)
    (h : E1M1AimMapped.Inputs s hit line front back ff fc bf bc)
    (returnSafe : E1M1AimReturnFrame.Safe s) (cursorSafe : E1M1AimRecordFrame.ReadSafe s 0x2c028)
    (slotSafe : E1M1AimRecordFrame.ReadSafe s (s.regs 4+4))
    (slotMark : Apart (s.regs 4+4) (s.regs 3))
    (target : load32 s.memory (s.regs 4+4)=0x2b760)
    (out : X86Control.State)
    (stack : E1M1AimScanStack.Position
      (load32 (E1M1AimResume.result s).core.memory ((E1M1AimResume.result s).core.regs 4))
      (s.regs 4+4) out) :
    E1M1AimScanStack.Position 0x2b760 (s.regs 4+4) out := by
  have r := E1M1AimRecordFrame.registers s hit line front back ff fc bf bc h returnSafe cursorSafe
  have slot := E1M1AimRecordFrame.resumed_frame s hit line front back ff fc bf bc
    (s.regs 4+4) h slotSafe returnSafe slotMark
  have sp : (E1M1AimResume.result s).core.regs 4=s.regs 4+4 := r.2.1
  rw [sp,slot,target] at stack
  exact stack
end Doom.Proofs.E1M1AimLineScanStack
