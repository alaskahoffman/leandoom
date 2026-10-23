import Doom.Proofs.E1M1TraversalBudget
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1SelectionRegisters
open Verification X86 X86Memory X86Control BlockSummary
open E1M1InterceptMinimum (Best update selectFrom minimum)
open E1M1MinimumScan (Represents Fractions address)
open OriginalInterceptMinimum (advanced result steps)
open OriginalInterceptGate (gate)
open E1M1InterceptGate (program contains_scan contains_gate gate_agrees)
attribute [local irreducible] load32 store32

/-- Carry the live traversal counter, maximum distance and stack through every scan iteration. -/
theorem scan (hits : Array Collision.Intercept) (fuel i : Nat) (best : Best)
    (s : X86Memory.State) (f : Option Flags) (bounded : hits.size≤128)
    (remaining : i+fuel=hits.size) (state : Represents s hits i best) :
    ∃ n≤7*fuel, ∃ out, X86Routine.Prefix program [] n
      ⟨s,f,if fuel=0 then 0x2c85e else 0x2c84f⟩ out ∧
      Represents out.core hits hits.size (selectFrom hits fuel i best) ∧
      out.pc=0x2c85e ∧ out.core.memory=s.memory ∧ out.core.regs 7=s.regs 7 ∧ out.core.regs 4=s.regs 4 ∧ out.core.regs 6=s.regs 6 := by
  induction fuel generalizing i best s f with
  | zero =>
    refine ⟨0,by omega,⟨s,f,0x2c85e⟩,.nil _,?_,rfl,rfl,rfl,rfl,rfl⟩
    simpa only [selectFrom,Nat.add_zero] using remaining ▸ state
  | succ fuel ih =>
    have inside : i<hits.size := by omega
    obtain ⟨n,hn,out,tailRun,outState,pc,memory,maximum,stack,counter⟩ :=
      ih (i+1) (update hits best i) (advanced s) (result s).flags (by omega)
        (E1M1MinimumScan.next s hits i best state inside)
    have seam : (⟨advanced s,(result s).flags,if fuel=0 then 0x2c85e else 0x2c84f⟩ : X86Control.State)=result s := by
      have pc := E1M1MinimumScan.next_pc s hits i best state inside bounded
      have cond : (i+1<hits.size) ↔ fuel≠0 := by omega
      have pc' : (result s).pc=(if fuel=0 then 0x2c85e else 0x2c84f) := by
        simpa only [cond,ite_not] using pc
      exact OriginalPathXStep.at_pc _ _ pc'
    rw [seam] at tailRun
    have bound : steps s≤7 := by unfold steps; split <;> omega
    have frame : (advanced s).regs 7=s.regs 7 := by
      unfold advanced OriginalInterceptMinimum.picked
      split <;> simp [put,write]
    have stackFrame : (advanced s).regs 4=s.regs 4 := by
      unfold advanced OriginalInterceptMinimum.picked
      split <;> simp [put,write]
    have counterFrame : (advanced s).regs 6=s.regs 6 := by
      unfold advanced OriginalInterceptMinimum.picked
      split <;> simp [put,write]
    exact ⟨steps s+n,by omega,out,
      OriginalGroupBounds.prefix_join ((OriginalInterceptMinimum.iteration s f).transfer program [] contains_scan (by simp)) tailRun,
      outState,pc,memory.trans (OriginalInterceptMinimum.fields s).1,maximum.trans frame,stack.trans stackFrame,counter.trans counterFrame⟩

/-- The full minimum scan now runs continuously into the original distance
branch. The result identifies the same source choice and exact cutoff exit. -/
theorem execution (s : X86Memory.State) (f : Option Flags) (hits : Array Collision.Intercept)
    (bounded : hits.size≤128) (limit : s.regs 1=address hits.size)
    (encoded : Fractions s.memory hits) (maximum : s.regs 7=65536) :
    ∃ n≤7+7*hits.size, ∃ (selected : X86Control.State), ∃ best,
      X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2c841⟩ (gate selected.core) ∧
      minimum hits=.ok best ∧ Represents selected.core hits hits.size best ∧
      (gate selected.core).pc=(if best.1>65536 then 0x2c887 else 0x2c868) ∧
      selected.core.memory=s.memory ∧ selected.core.regs 7=65536 ∧ selected.core.regs 4=s.regs 4 ∧ selected.core.regs 6=s.regs 6 := by
  let first := OriginalInterceptMinimum.entry s
  have state : Represents first.core hits 0 (2147483647,none) := by
    refine ⟨rfl,?_,rfl,?_,encoded⟩
    · simpa [first,OriginalInterceptMinimum.entry,OriginalInterceptMinimum.initialized,put,write] using limit
    · intro j h; cases h
  obtain ⟨n,hn,out,run,outState,pc,memory,maxFrame,stackFrame,counterFrame⟩ :=
    scan hits hits.size 0 (2147483647,none) first.core first.flags bounded (by omega) state
  have entryPc : first.pc=(if hits.size=0 then 0x2c85e else 0x2c84f) := by
    simp only [first,OriginalInterceptMinimum.entry,limit,E1M1MinimumScan.address_value _ bounded]
    simp only [show (178720+12*hits.size≤178720) ↔ hits.size=0 from by omega]
  rw [OriginalPathXStep.at_pc _ _ entryPc] at run
  have startRun := (OriginalInterceptMinimum.entry_execution s f).transfer program [] contains_scan (by simp)
  have gateRun := (OriginalInterceptGate.gate_execution out.core out.flags).transfer program [] contains_gate (by simp)
  rw [OriginalPathXStep.at_pc _ _ pc] at gateRun
  have maxOut : out.core.regs 7=65536 := maxFrame.trans (by
    simpa [first,OriginalInterceptMinimum.entry,OriginalInterceptMinimum.initialized,put,write] using maximum)
  exact ⟨4+n+3,by omega,out,selectFrom hits hits.size 0 (2147483647,none),
    X86CodeMemory.lift_success (OriginalGroupBounds.prefix_join (OriginalGroupBounds.prefix_join startRun run) gateRun) FloorCaller.cm,
    E1M1InterceptMinimum.minimum_replay hits,outState,gate_agrees _ _ _ outState maxOut,memory,maxOut,stackFrame.trans (by
      simp [first,OriginalInterceptMinimum.entry,OriginalInterceptMinimum.initialized,put,write]),counterFrame.trans (by
      simp [first,OriginalInterceptMinimum.entry,OriginalInterceptMinimum.initialized,put,write])⟩

end Doom.Proofs.E1M1SelectionRegisters
