import Doom.Proofs.E1M1FiringGridState
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
namespace Doom.Proofs.E1M1AdvanceCollection
open Verification X86 X86Memory X86Control BlockSummary
open OriginalLineCollection (slot Tracks)
open E1M1PathAdvance (Cell observe step nextPc ended)
attribute [local irreducible] load32

/-- Endpoint exit performs no store; otherwise only the X branch writes the
Y-intercept local. This identifies the entire memory, not just selected reads. -/
theorem memory (s : X86Memory.State) :
    (OriginalPathAdvance.result s).core.memory=
      if OriginalPathAdvance.atEnd s then s.memory
      else if OriginalPathAdvance.takeX s then
        store32 s.memory (s.regs 4+44)
          (OriginalPathAdvance.localWord s 44+OriginalPathAdvance.localWord s 40)
      else s.memory := by
  unfold OriginalPathAdvance.result
  split
  · rfl
  · exact (E1M1PathAdvance.selected_observe s).2.2

/-- Any word disjoint from the one possible store survives every branch. -/
theorem frame (s : X86Memory.State) (a : Word) (safe : Apart a (s.regs 4+(44#32))) :
    load32 (OriginalPathAdvance.result s).core.memory a=load32 s.memory a := by
  rw [memory]
  split
  · rfl
  · split
    · exact load_store_apart _ _ _ _ safe
    · rfl

/-- Advancement preserves ordered records, their exact cursor, and the same
reserve. It does not consume an intercept slot or assume new collection room. -/
theorem collection (s : X86Memory.State) (base : Word) (resolve : Collision.Intercept → Word)
    (hits : Array Collision.Intercept) (reserve : Nat) (tracked : Tracks s base resolve hits reserve)
    (safe : OriginalLineMixedInvariant.ArraySafe base (s.regs 4+(44#32))) :
    Tracks (OriginalPathAdvance.result s).core base resolve hits reserve := by
  have keep (i : Nat) (hi : i<hits.size) (off : Word) (ho : off∈[(0#32),4,8]) :
      load32 (OriginalPathAdvance.result s).core.memory (slot base i off)=load32 s.memory (slot base i off) := by
    have bound := tracked.room
    exact frame s _ (FloorCaller.apart_symm (safe.1 i (by omega) off ho))
  refine ⟨?_,?_,tracked.room⟩
  · intro i hi
    simp only [slot] at keep
    have old := tracked.encoded i hi
    unfold OriginalLineFinish.RecordAt at old ⊢
    rw [show load32 (OriginalPathAdvance.result s).core.memory (base+BitVec.ofNat 32 (12*i))=
        load32 s.memory (base+BitVec.ofNat 32 (12*i)) by
          simpa only [slot,BitVec.add_zero] using keep i hi (0#32) (by simp),
      keep i hi (4#32) (by simp),keep i hi (8#32) (by simp)]
    exact old
  · exact (frame s _ (FloorCaller.apart_symm safe.2)).trans tracked.cursor

/-- A continuing step advances the natural iteration index exactly once;
endpoint exits do not increment it. The legal range excludes signed overflow. -/
theorem counter (g : Cell) (n : Nat) (bound : n<64) (count : g.count=BitVec.ofNat 32 n) :
    (step g).count=BitVec.ofNat 32 (if ended g then n else n+1) ∧
    nextPc g=(if ended g then 0x2cafd else if n+1<64 then 0x2ca7f else 0x2cafd) := by
  have add : BitVec.ofNat 32 n+1=BitVec.ofNat 32 (n+1) := by
    exact (BitVec.ofNat_add n 1).symm
  constructor
  · by_cases he : ended g=true
    · simpa only [step,if_pos he] using count
    · simp only [step,if_neg he]
      exact (congrArg (fun x : Word => x+1) count).trans add
  · unfold nextPc
    rw [count]
    have limit : (BitVec.ofNat 32 n+1).toInt<64 ↔ n+1<64 := E1M1PathAdvance.counter_limit n bound
    simp only [limit]

/-- The next-cell gate is reached exactly when neither endpoint nor budget
termination applies. A stalled cell follows the same budget rule. -/
theorem next_gate_iff (g : Cell) (n : Nat) (bound : n<64) (count : g.count=BitVec.ofNat 32 n) :
    nextPc g=0x2ca7f ↔ ended g=false ∧ n+1<64 := by
  rw [(counter g n bound count).2]
  cases ended g <;> by_cases hb : n+1<64 <;> simp [hb]

/-- Continuation supplies a legal index for the next iteration, rather than
assuming it at that boundary. It does not establish the next scan's capacity. -/
theorem continuing_index (g : Cell) (n : Nat) (bound : n<64) (count : g.count=BitVec.ofNat 32 n)
    (next : nextPc g=0x2ca7f) :
    (step g).count=BitVec.ofNat 32 (n+1) ∧ n+1<64 := by
  have condition := (next_gate_iff g n bound count).mp next
  exact ⟨by simpa only [condition.1,Bool.false_eq_true,↓reduceIte] using (counter g n bound count).1,condition.2⟩

/-- Reusable end-of-cell invariant: numeric state, ordered hits, stack and legal
iteration index travel together to the next gate or the post-loop boundary.
This does not execute the next cell's scans or allocate their reserve. -/
theorem iteration (s : X86Memory.State) (f : Option Flags) (g : Cell)
    (observed : observe s=g) (n : Nat) (bound : n<64) (count : g.count=BitVec.ofNat 32 n)
    (base : Word) (resolve : Collision.Intercept → Word) (hits : Array Collision.Intercept)
    (reserve : Nat) (tracked : Tracks s base resolve hits reserve)
    (safe : OriginalLineMixedInvariant.ArraySafe base (s.regs 4+(44#32))) :
    let out := OriginalPathAdvance.result s
    (∃ steps≤19, X86Routine.Prefix OriginalPathAdvance.program [] steps ⟨s,f,0x2cab5⟩ out) ∧
    observe out.core=step g ∧ out.core.regs 4=s.regs 4 ∧
    Tracks out.core base resolve hits reserve ∧
    out.core.regs 7=BitVec.ofNat 32 (if ended g then n else n+1) ∧
    out.pc=(if ended g then 0x2cafd else if n+1<64 then 0x2ca7f else 0x2cafd) := by
  obtain ⟨run,obs,pc,sp⟩ := E1M1PathAdvance.execution s f
  rw [observed] at obs pc
  have budget := counter g n bound count
  exact ⟨run,obs,sp,collection s base resolve hits reserve tracked safe,
    (congrArg Cell.count obs).trans budget.1,pc.trans budget.2⟩
end Doom.Proofs.E1M1AdvanceCollection
