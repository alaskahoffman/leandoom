import Doom.Proofs.OriginalInterceptGate
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1InterceptGate
open Verification X86 X86Memory X86Control BlockSummary
open E1M1InterceptMinimum (Best update selectFrom minimum)
open E1M1MinimumScan (Represents Fractions address)
open OriginalInterceptMinimum (advanced result steps)
open OriginalInterceptGate (gate saved beyond called)
attribute [local irreducible] load32 store32

/-- Use the original byte-backed scan and its adjacent gate in one program. -/
def program : X86Routine.Program := fun pc =>
  if pc<0x2c85e then OriginalInterceptMinimum.program pc else OriginalInterceptGate.program pc

theorem contains_scan (pc : Nat) (h : OriginalInterceptMinimum.program pc≠none) :
    program pc=OriginalInterceptMinimum.program pc := by
  have lt : pc<0x2c85e := by
    by_cases bad : pc<0x2c85e
    · exact bad
    · simp [OriginalInterceptMinimum.program,OriginalInterceptMinimum.bytesProgram,bad] at h
  simp [program,lt]

theorem contains_gate (pc : Nat) (h : OriginalInterceptGate.program pc≠none) :
    program pc=OriginalInterceptGate.program pc := by
  have ge : 0x2c85e≤pc := by
    by_cases bad : 0x2c85e≤pc
    · exact bad
    · simp [OriginalInterceptGate.program,OriginalInterceptGate.bytesProgram,bad] at h
  simp [program,show ¬pc<0x2c85e by omega]

/-- Carry the caller's maximum distance through every scan iteration. -/
theorem scan (hits : Array Collision.Intercept) (fuel i : Nat) (best : Best)
    (s : X86Memory.State) (f : Option Flags) (bounded : hits.size≤128)
    (remaining : i+fuel=hits.size) (state : Represents s hits i best) :
    ∃ n≤7*fuel, ∃ out, X86Routine.Prefix program [] n
      ⟨s,f,if fuel=0 then 0x2c85e else 0x2c84f⟩ out ∧
      Represents out.core hits hits.size (selectFrom hits fuel i best) ∧
      out.pc=0x2c85e ∧ out.core.memory=s.memory ∧ out.core.regs 7=s.regs 7 := by
  induction fuel generalizing i best s f with
  | zero =>
    refine ⟨0,by omega,⟨s,f,0x2c85e⟩,.nil _,?_,rfl,rfl,rfl⟩
    simpa only [selectFrom,Nat.add_zero] using remaining ▸ state
  | succ fuel ih =>
    have inside : i<hits.size := by omega
    obtain ⟨n,hn,out,tailRun,outState,pc,memory,maximum⟩ :=
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
    exact ⟨steps s+n,by omega,out,
      OriginalGroupBounds.prefix_join ((OriginalInterceptMinimum.iteration s f).transfer program [] contains_scan (by simp)) tailRun,
      outState,pc,memory.trans (OriginalInterceptMinimum.fields s).1,maximum.trans frame⟩

/-- Source and DOS use the same signed, inclusive 16.16 endpoint cutoff. -/
theorem gate_agrees (s : X86Memory.State) (hits : Array Collision.Intercept) (best : Best)
    (state : Represents s hits hits.size best) (maximum : s.regs 7=65536) :
    (gate s).pc=(if best.1>65536 then 0x2c887 else 0x2c868) := by
  have test : beyond s ↔ best.1>65536 := by
    simp [beyond,maximum,state.distance,Int32.lt_iff_toInt_lt]
  simp only [gate,test]

/-- With no finite selection, the actual DOS branch exits before the stale
best pointer can be passed to the callback. -/
theorem no_choice (s : X86Memory.State) (hits : Array Collision.Intercept) (distance : Int32)
    (selected : minimum hits=.ok (distance,none))
    (state : Represents s hits hits.size (distance,none)) (maximum : s.regs 7=65536) :
    (gate s).pc=0x2c887 := by
  rw [gate_agrees s hits (distance,none) state maximum]
  have sentinel := E1M1InterceptMinimum.minimum_none hits distance selected
  simp [sentinel]

/-- The full minimum scan now runs continuously into the original distance
branch. The result identifies the same source choice and exact cutoff exit. -/
theorem execution (s : X86Memory.State) (f : Option Flags) (hits : Array Collision.Intercept)
    (bounded : hits.size≤128) (limit : s.regs 1=address hits.size)
    (encoded : Fractions s.memory hits) (maximum : s.regs 7=65536) :
    ∃ n≤7+7*hits.size, ∃ (selected : X86Control.State), ∃ best,
      X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2c841⟩ (gate selected.core) ∧
      minimum hits=.ok best ∧ Represents selected.core hits hits.size best ∧
      (gate selected.core).pc=(if best.1>65536 then 0x2c887 else 0x2c868) ∧
      selected.core.memory=s.memory ∧ selected.core.regs 7=65536 := by
  let first := OriginalInterceptMinimum.entry s
  have state : Represents first.core hits 0 (2147483647,none) := by
    refine ⟨rfl,?_,rfl,?_,encoded⟩
    · simpa [first,OriginalInterceptMinimum.entry,OriginalInterceptMinimum.initialized,put,write] using limit
    · intro j h; cases h
  obtain ⟨n,hn,out,run,outState,pc,memory,maxFrame⟩ :=
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
    E1M1InterceptMinimum.minimum_replay hits,outState,gate_agrees _ _ _ outState maxOut,memory,maxOut⟩

private theorem choice_bound (hits : Array Collision.Intercept) (fuel i : Nat) (best : Best)
    (remaining : i+fuel≤hits.size) (initial : ∀ j, best.2=some j → j<hits.size) :
    ∀ j, (selectFrom hits fuel i best).2=some j → j<hits.size := by
  induction fuel generalizing i best with
  | zero => exact initial
  | succ fuel ih =>
    apply ih (i+1) (update hits best i) (by omega)
    intro j chosen
    by_cases better : hits[i]!.frac.raw<best.1
    · have same : i=j := by simpa [update,better] using chosen
      omega
    · exact initial j (by simpa [update,better] using chosen)

/-- An admitted source minimum always names a real array element. -/
theorem admitted (hits : Array Collision.Intercept) (best : Best)
    (selected : minimum hits=.ok best) (within : ¬best.1>65536) :
    ∃ j, best.2=some j ∧ j<hits.size := by
  have replay := E1M1InterceptMinimum.minimum_replay hits
  have eq : selectFrom hits hits.size 0 (2147483647,none)=best := by
    rw [selected] at replay
    exact (Except.ok.inj replay).symm
  have bounds := choice_bound hits hits.size 0 (2147483647,none) (by omega) (by intro j bad; cases bad)
  rw [eq] at bounds
  cases chosen : best.2 with
  | none =>
    have pair : best=(best.1,none) := Prod.ext rfl chosen
    have sentinel := E1M1InterceptMinimum.minimum_none hits best.1 (selected.trans (congrArg Except.ok pair))
    simp [sentinel] at within
  | some j => exact ⟨j,rfl,bounds j chosen⟩

/-- After a valid minimum, the distance branch and real CALL pass the exact
selected record address. The callback's own behavior is not assumed here. -/
theorem callback (s : X86Memory.State) (f : Option Flags) (hits : Array Collision.Intercept) (best : Best)
    (selected : minimum hits=.ok best) (within : ¬best.1>65536)
    (state : Represents s hits hits.size best) (maximum : s.regs 7=65536) :
    ∃ j, best.2=some j ∧ j<hits.size ∧
      X86CodeMemory.Prefix FloorCaller.cm program [] 5 ⟨s,f,0x2c85e⟩ (called (saved s) (gate s).flags) ∧
      (called (saved s) (gate s).flags).core.regs 0=address j ∧
      (called (saved s) (gate s).flags).pc=(load32 (saved s).memory (s.regs 4)).toNat := by
  obtain ⟨j,chosen,bound⟩ := admitted hits best selected within
  have pc : (gate s).pc=0x2c868 := by rw [gate_agrees s hits best state maximum,if_neg within]
  have gateRun := (OriginalInterceptGate.gate_execution s f).transfer program [] contains_gate (by simp)
  have callRun := (OriginalInterceptGate.call_execution (saved s) (gate s).flags).transfer program [] contains_gate (by simp)
  change X86Routine.Prefix program [] 2 ⟨(gate s).core,(gate s).flags,0x2c868⟩ _ at callRun
  rw [OriginalPathXStep.at_pc _ _ pc] at callRun
  refine ⟨j,chosen,bound,X86CodeMemory.lift_success (OriginalGroupBounds.prefix_join gateRun callRun) FloorCaller.cm,?_,rfl⟩
  simpa [called,X86Routine.pushWord,saved,put,write] using state.choice j chosen
end Doom.Proofs.E1M1InterceptGate
