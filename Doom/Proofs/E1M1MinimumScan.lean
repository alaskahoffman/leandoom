import Doom.Proofs.E1M1InterceptMinimum
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1MinimumScan
open Verification X86 X86Memory X86Control BlockSummary
open E1M1InterceptMinimum (Best update selectFrom minimum)
open OriginalInterceptMinimum (better fraction advanced result steps)
attribute [local irreducible] load32

def address (i : Nat) : Word := BitVec.ofNat 32 (178720+12*i)
def Fractions (m : Memory) (hits : Array Collision.Intercept) : Prop :=
  ∀ i<hits.size, load32 m (address i)=hits[i]!.frac.raw.toBitVec

/-- No constraint on EBX when the source has no choice: DOS retains stale EBX. -/
structure Represents (s : X86Memory.State) (hits : Array Collision.Intercept) (i : Nat) (best : Best) : Prop where
  pointer : s.regs 0=address i
  limit : s.regs 1=address hits.size
  distance : s.regs 2=best.1.toBitVec
  choice : ∀ j, best.2=some j → s.regs 3=address j
  fractions : Fractions s.memory hits

theorem address_next (i : Nat) : address i+12=address (i+1) := by
  simp [address,←BitVec.ofNat_add,Nat.mul_add,Nat.add_assoc]

theorem address_value (i : Nat) (bound : i≤128) : (address i).toNat=178720+12*i := by
  simp only [address,BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  omega

/-- Encoded records from collection provide exactly the fractions read here. -/
theorem fractions (m : Memory) (hits : Array Collision.Intercept) (resolve : Collision.Intercept → Word)
    (encoded : OriginalLineFinish.Encodes m 0x2ba20 resolve hits) : Fractions m hits := by
  intro i hi
  have h := (encoded i hi).1
  simpa [address,BitVec.ofNat_add,getElem!_pos hits i hi] using h

/-- The actual instruction iteration implements one source selection update. -/
theorem next (s : X86Memory.State) (hits : Array Collision.Intercept) (i : Nat) (best : Best)
    (state : Represents s hits i best) (inside : i<hits.size) :
    Represents (advanced s) hits (i+1) (update hits best i) := by
  have reads : fraction s=hits[i]!.frac.raw.toBitVec := by
    unfold fraction; rw [state.pointer]; exact state.fractions i inside
  have test : better s ↔ hits[i]!.frac.raw<best.1 := by
    unfold better; rw [reads,state.distance]
    simp [Int32.lt_iff_toInt_lt]
  have fields := OriginalInterceptMinimum.fields s
  refine ⟨fields.2.1.trans (by rw [state.pointer,address_next]),
    fields.2.2.1.trans state.limit,?_,?_,?_⟩
  · rw [fields.2.2.2.1]
    by_cases h : hits[i]!.frac.raw<best.1
    · rw [if_pos (test.mpr h),reads]; simp [update,h]
    · rw [if_neg (fun yes => h (test.mp yes)),state.distance]; simp [update,h]
  · intro j chosen
    rw [fields.2.2.2.2]
    by_cases h : hits[i]!.frac.raw<best.1
    · rw [if_pos (test.mpr h),state.pointer]
      have eq : i=j := by simpa [update,h] using chosen
      rw [eq]
    · rw [if_neg (fun yes => h (test.mp yes))]
      exact state.choice j (by simpa [update,h] using chosen)
  · rw [fields.1]; exact state.fractions

/-- The bound on the fixed DOS buffer rules out pointer wrap in the scan test. -/
theorem next_pc (s : X86Memory.State) (hits : Array Collision.Intercept) (i : Nat) (best : Best)
    (state : Represents s hits i best) (inside : i<hits.size) (bounded : hits.size≤128) :
    (result s).pc=(if i+1<hits.size then 0x2c84f else 0x2c85e) := by
  simp only [result,state.pointer,state.limit,address_next]
  rw [address_value _ (by omega),address_value _ bounded]
  simp only [show (178720+12*(i+1)<178720+12*hits.size) ↔ i+1<hits.size from by omega]

/-- Iterate the real backward branch over the entire remaining array. -/
theorem scan (hits : Array Collision.Intercept) (fuel i : Nat) (best : Best)
    (s : X86Memory.State) (f : Option Flags) (bounded : hits.size≤128)
    (remaining : i+fuel=hits.size) (state : Represents s hits i best) :
    ∃ n≤7*fuel, ∃ out, X86Routine.Prefix OriginalInterceptMinimum.program [] n
      ⟨s,f,if fuel=0 then 0x2c85e else 0x2c84f⟩ out ∧
      Represents out.core hits hits.size (selectFrom hits fuel i best) ∧ out.pc=0x2c85e ∧ out.core.memory=s.memory := by
  induction fuel generalizing i best s f with
  | zero =>
    refine ⟨0,by omega,⟨s,f,0x2c85e⟩,.nil _,?_,rfl,rfl⟩
    simpa only [selectFrom,Nat.add_zero] using remaining ▸ state
  | succ fuel ih =>
    have inside : i<hits.size := by omega
    have stepState := next s hits i best state inside
    obtain ⟨n,hn,out,tailRun,outState,pc,memory⟩ := ih (i+1) (update hits best i) (advanced s) (result s).flags
      (by omega) stepState
    have seam : (⟨advanced s,(result s).flags,if fuel=0 then 0x2c85e else 0x2c84f⟩ : X86Control.State)=result s := by
      have pc := next_pc s hits i best state inside bounded
      have cond : (i+1<hits.size) ↔ fuel≠0 := by omega
      have pc' : (result s).pc=(if fuel=0 then 0x2c85e else 0x2c84f) := by
        simpa only [cond,ite_not] using pc
      exact OriginalPathXStep.at_pc _ _ pc'
    rw [seam] at tailRun
    have bound : steps s≤7 := by unfold steps; split <;> omega
    exact ⟨steps s+n,by omega,out,OriginalGroupBounds.prefix_join (OriginalInterceptMinimum.iteration s f) tailRun,
      outState,pc,memory.trans (OriginalInterceptMinimum.fields s).1⟩

/-- Full original minimum scan equals the exact live selector. The old best
pointer may be arbitrary; it is constrained only if the source selects a hit. -/
theorem execution (s : X86Memory.State) (f : Option Flags) (hits : Array Collision.Intercept)
    (bounded : hits.size≤128) (limit : s.regs 1=address hits.size) (encoded : Fractions s.memory hits) :
    ∃ n≤4+7*hits.size, ∃ out best,
      X86CodeMemory.Prefix FloorCaller.cm OriginalInterceptMinimum.program [] n ⟨s,f,0x2c841⟩ out ∧
      minimum hits=.ok best ∧ Represents out.core hits hits.size best ∧ out.pc=0x2c85e ∧ out.core.memory=s.memory := by
  let first := OriginalInterceptMinimum.entry s
  have state : Represents first.core hits 0 (2147483647,none) := by
    refine ⟨rfl,?_,rfl,?_,encoded⟩
    · simpa [first,OriginalInterceptMinimum.entry,OriginalInterceptMinimum.initialized,put,write] using limit
    · intro j h; cases h
  obtain ⟨n,hn,out,run,outState,pc,memory⟩ := scan hits hits.size 0 (2147483647,none) first.core first.flags bounded (by omega) state
  have entryPc : first.pc=(if hits.size=0 then 0x2c85e else 0x2c84f) := by
    simp only [first,OriginalInterceptMinimum.entry,limit,address_value _ bounded]
    simp only [show (178720+12*hits.size≤178720) ↔ hits.size=0 from by omega]
  rw [OriginalPathXStep.at_pc _ _ entryPc] at run
  exact ⟨4+n,by omega,out,selectFrom hits hits.size 0 (2147483647,none),
    X86CodeMemory.lift_success (OriginalGroupBounds.prefix_join (OriginalInterceptMinimum.entry_execution s f) run) FloorCaller.cm,
    E1M1InterceptMinimum.minimum_replay hits,outState,pc,memory⟩
end Doom.Proofs.E1M1MinimumScan
