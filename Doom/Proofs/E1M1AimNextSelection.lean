import Doom.Proofs.E1M1AimRecordFrame
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1AimNextSelection
open Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1MinimumScan (address)
open E1M1FirstIntercept (program)
attribute [local irreducible] load32 store32

/-- The loop tests the old counter, after decrementing its saved value. -/
def head (s : X86Memory.State) : X86Control.State :=
  ⟨put (put s 0 (s.regs 6)) 6 (s.regs 6-1),some (logical32 (s.regs 6)),
    if s.regs 6=0 then 0x2c887 else 0x2c841⟩

theorem contains_setup (pc : Nat) (h : OriginalInterceptSetup.program pc≠none) :
    program pc=OriginalInterceptSetup.program pc := by
  have eq := E1M1TraversalEntry.contains_setup pc h
  exact (E1M1FirstIntercept.contains_entry pc (by rw [eq]; exact h)).trans eq

/-- Four original instructions at the repeat edge; the zero case also performs
its historical wrapping decrement before leaving the loop. -/
theorem head_execution (s : X86Memory.State) (f : Option Flags) :
    X86CodeMemory.Prefix FloorCaller.cm program [] 4 ⟨s,f,0x2c83a⟩ (head s) := by
  have run : X86Routine.Prefix OriginalInterceptSetup.listed [] 4 ⟨s,f,0x2c83a⟩ (head s) := by
    apply X86Routine.Prefix.step (middle := ⟨put s 0 (s.regs 6),f,0x2c83c⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,put,write,blockPreservesFlags])
    apply X86Routine.Prefix.step (middle := ⟨(head s).core,none,0x2c83d⟩) (by simp) (by rfl) (by
      simp [head,X86Routine.execute,put,write,BitVec.sub_eq_add_neg])
    apply X86Routine.Prefix.step (middle := ⟨(head s).core,(head s).flags,0x2c83f⟩) (by simp) (by rfl) (by
      simp [head,X86Routine.execute,X86Control.execute,put,write])
    apply X86Routine.Prefix.step (middle := head s) (by simp) (by rfl) (by
      by_cases zero : s.regs 6=(0#32) <;>
        simp [head,X86Routine.execute,X86Control.execute,logical32,zero,put,write])
    exact .nil _
  have run := run.transfer OriginalInterceptSetup.program [] OriginalInterceptSetup.decoded (by simp)
  exact (X86CodeMemory.lift_success run FloorCaller.cm).transfer program [] contains_setup (by simp)

/-- Repeat may exhaust its counter even though the collection itself is nonempty. -/
def Outcome (s : X86Memory.State) (hits : Array Intercept) (resolve : Intercept → Word)
    (out : X86Control.State) : Prop :=
  (s.regs 6=0 ∧ out=head s) ∨
  (s.regs 6≠0 ∧ E1M1CallbackEntry.Outcome hits resolve
    (load32 s.memory (s.regs 4)) (s.regs 4) out)

/-- Re-enter the real loop head, scan the entire current buffer in original tie
order, and reach exhaustion, range rejection, or the next actual callback. -/
theorem dispatch (s : X86Memory.State) (f : Option Flags) (hits : Array Intercept)
    (resolve : Intercept → Word) (bounded : hits.size≤128) (nonempty : hits.size≠0)
    (limit : s.regs 1=address hits.size)
    (encoded : OriginalLineFinish.Encodes s.memory 0x2ba20 resolve hits)
    (maximum : s.regs 7=65536) (targetSafe : Apart (s.regs 4) 0x2c028)
    (recordSafe : ∀ i<hits.size, ∀ off∈[(0#32),4,8],
      Apart (OriginalLineCollection.slot 0x2ba20 i off) (s.regs 4-4)) :
    ∃ n≤13+7*hits.size, ∃ out,
      X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2c83a⟩ out ∧
      Outcome s hits resolve out := by
  have run := head_execution s f
  by_cases zero : s.regs 6=(0#32)
  · exact ⟨4,by omega,head s,run,Or.inl ⟨zero,rfl⟩⟩
  · obtain ⟨n,hn,out,tail,done⟩ := E1M1CallbackEntry.dispatch (head s) hits resolve bounded
      (by simpa [head,put,write] using limit) encoded
      (by simpa [head,put,write] using maximum)
      (by simp [head,zero,nonempty]) targetSafe recordSafe
    exact ⟨4+n,by omega,out,E1M1PspriteStep.prefix_trans run tail,Or.inr ⟨zero,done⟩⟩

/-- The next selection starts with the buffer derived from the initial callback
memory, including the consumed record, rather than an assumed post-call image.
The counter is carried unchanged through the callback; head_execution decrements it. -/
theorem after_callback (s : X86Memory.State) (hit : Intercept) (line front back ff fc bf bc : Word)
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
      Outcome (E1M1AimResume.result s).core (E1M1InterceptMark.consume hits j) resolve out := by
  have r := E1M1AimRecordFrame.registers s hit line front back ff fc bf bc h returnSafe cursorSafe
  have image' := E1M1AimRecordFrame.resumed_records s hit line front back ff fc bf bc h hits resolve j inside bounded image safe returnSafe pointer go stable
  obtain ⟨n,hn,out,run,done⟩ := dispatch (E1M1AimResume.result s).core (E1M1AimResume.result s).flags
    (E1M1InterceptMark.consume hits j) resolve
    (by simpa only [E1M1InterceptMark.size] using bounded)
    (by rw [E1M1InterceptMark.size]; omega)
    (by rw [E1M1InterceptMark.size]; exact r.1.trans cursor) image'
    (r.2.2.2.trans maximum) (by rw [r.2.1]; exact targetSafe)
    (by rw [r.2.1]; simpa [E1M1InterceptMark.size,BitVec.add_sub_cancel] using recordSafe)
  have pc : (E1M1AimResume.result s).pc=0x2c83a := by
    simp only [E1M1AimResume.result,OriginalInterceptGate.resumed,if_neg go]
  rw [OriginalPathXStep.at_pc _ _ pc] at run
  exact ⟨n,by simpa only [E1M1InterceptMark.size] using hn,out,run,done⟩
/-- Re-express the next outcome using the initial counter and callback slot.
All three values are carried through the real callback and parent mark. -/
theorem carried_outcome (s : X86Memory.State) (hit : Intercept) (line front back ff fc bf bc : Word)
    (h : E1M1AimMapped.Inputs s hit line front back ff fc bf bc)
    (returnSafe : E1M1AimReturnFrame.Safe s) (cursorSafe : E1M1AimRecordFrame.ReadSafe s 0x2c028)
    (slotSafe : E1M1AimRecordFrame.ReadSafe s (s.regs 4+4))
    (markSafe : Apart (s.regs 4+4) (s.regs 3))
    (hits : Array Intercept) (resolve : Intercept → Word) (out : X86Control.State)
    (done : Outcome (E1M1AimResume.result s).core hits resolve out) :
    (s.regs 6=0 ∧ out=head (E1M1AimResume.result s).core) ∨
    (s.regs 6≠0 ∧ E1M1CallbackEntry.Outcome hits resolve
      (load32 s.memory (s.regs 4+4)) (s.regs 4+4) out) := by
  have r := E1M1AimRecordFrame.registers s hit line front back ff fc bf bc h returnSafe cursorSafe
  have slot := E1M1AimRecordFrame.resumed_frame s hit line front back ff fc bf bc
    (s.regs 4+4) h slotSafe returnSafe markSafe
  unfold Outcome at done
  rw [r.2.2.1,r.2.1] at done
  change load32 (E1M1AimResume.result s).core.memory (s.regs 4+(4#32))=_ at slot
  rw [slot] at done
  exact done
end Doom.Proofs.E1M1AimNextSelection
