import Doom.Proofs.E1M1ObjectBoundary
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1CellBoundaryAdvance
open Verification X86 X86Memory X86Control BlockSummary
open OriginalLineVisits (Represents stamp)
open E1M1PathAdvance (Cell observe step nextPc)
attribute [local irreducible] load32

/-- The numeric and mutable state needed after a successful cell return.
Map/node read contracts and capacity for the following scan are separate. -/
structure Returned (s : X86Control.State) (sp lines epoch : Word) (objects : Nat → Word)
    (g : Cell) (hits : Array Collision.Intercept) (seen : Array Bool) : Prop where
  pc : s.pc=0x2cab1
  success : s.core.regs 0=(1#32)
  stack : s.core.regs 4=sp-(112#32)
  observed : observe s.core=g
  tracked : OriginalLineCollection.Tracks s.core 0x2ba20 (E1M1ThingFinish.resolve lines objects) hits 0
  represented : Represents s.core.memory lines epoch seen

/-- The success test changes only control/flags; advancement starts from the
same core state. Its only possible store is the Y-intercept local. -/
def result (s : X86Control.State) := OriginalPathAdvance.result s.core

theorem frame (s : X86Control.State) (sp : Word) (stack : s.core.regs 4=sp-(112#32))
    (a : Word) (safe : Apart a (sp-(112#32)+(44#32))) :
    load32 (result s).core.memory a=load32 s.core.memory a :=
  E1M1AdvanceCollection.frame s.core a (by rw [stack]; exact safe)

/-- Reusable cell-return transition through the real success test and numeric
step, preserving ordered mixed records and visited history on all step branches.
The PC is the original endpoint/iteration-budget decision, including stalls. -/
theorem execution (s : X86Control.State) (sp lines epoch : Word) (objects : Nat → Word)
    (g : Cell) (hits : Array Collision.Intercept) (seen : Array Bool)
    (ready : Returned s sp lines epoch objects g hits seen)
    (locals : E1M1GridLocals.Safe sp lines)
    (epochSafe : Apart (0x13580#32) (sp-(112#32)+(44#32)))
    (stampSafe : ∀ j<seen.size, Apart (stamp lines j) (sp-(112#32)+(44#32))) :
    let out := result s
    (∃ n≤21, X86CodeMemory.Prefix FloorCaller.cm E1M1FiringAdvance.program [] n s out) ∧
    out.core.regs 4=sp-(112#32) ∧ observe out.core=step g ∧ out.pc=nextPc g ∧
    OriginalLineCollection.Tracks out.core 0x2ba20 (E1M1ThingFinish.resolve lines objects) hits 0 ∧
    Represents out.core.memory lines epoch seen := by
  have caller := E1M1FiringCellReturn.success_test s ready.pc ready.success
  obtain ⟨⟨n,hn,advance⟩,obs,pc,stack⟩ := E1M1PathAdvance.execution s.core (OriginalPathCell.resumed false s.core).flags
  change X86Routine.Prefix _ [] n ⟨(OriginalPathCell.resumed false s.core).core,
    (OriginalPathCell.resumed false s.core).flags,0x2cab5⟩ _ at advance
  rw [OriginalPathXStep.at_pc _ _ caller.2.1] at advance
  rw [ready.observed] at obs pc
  have collected := E1M1AdvanceCollection.collection s.core 0x2ba20
    (E1M1ThingFinish.resolve lines objects) hits 0 ready.tracked (by
      rw [ready.stack]; exact locals.array 44 (by simp [E1M1GridLocals.offsets]))
  refine ⟨⟨2+n,by omega,E1M1PspriteStep.prefix_trans
    (caller.1.transfer E1M1FiringAdvance.program [] E1M1FiringAdvance.contains_prior (by simp))
    (X86CodeMemory.lift_success (advance.transfer _ [] E1M1FiringAdvance.contains_advance (by simp)) FloorCaller.cm)⟩,
    stack.trans ready.stack,obs,pc,collected,⟨?_,?_⟩⟩
  · exact (frame s sp ready.stack _ epochSafe).trans ready.represented.1
  · intro j hj
    rw [frame s sp ready.stack _ (stampSafe j hj)]; exact ready.represented.2 j hj
end Doom.Proofs.E1M1CellBoundaryAdvance
