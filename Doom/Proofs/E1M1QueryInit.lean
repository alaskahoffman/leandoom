import Doom.Proofs.E1M1LiveWalk
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
namespace Doom.Proofs.E1M1QueryInit
open Verification X86 X86Memory X86Control BlockSummary
open E1M1PathMapSetup (grid StackSafe)

/-- The numeric collection-loop state is derived at query entry, not assumed at
an interior gate. The two successful divisions are production calculations. -/
theorem numeric (s : X86Memory.State) (ox oy sx sy ex ey : Fixed)
    (geometry : OriginalPathInit.Inputs s ox oy sx sy ex ey)
    (xout yout : Int32 × Fixed × Fixed)
    (okX : (Collision.pathStart ox oy sx sy ex ey).xStep=.ok xout)
    (okY : (Collision.pathStart ox oy sx sy ex ey).yStep=.ok yout) :
    E1M1PathAdvance.observe (grid s).core=
      E1M1FiringGridState.initial (Collision.pathStart ox oy sx sy ex ey) xout yout ∧
    (grid s).pc=0x2ca7f ∧ (grid s).core.regs 4=s.regs 4-60 := by
  have ready := (E1M1PathGridSetup.grid_observation_from_init s ox oy sx sy ex ey
    geometry xout yout okX okY).2
  have ends := E1M1GridLocals.endpoints s ox oy sx sy ex ey geometry
  exact ⟨E1M1FiringGridState.of_ready _ _ _ _ _ ready ends.1 ends.2,
    ready.pc,E1M1PathMapSetup.grid_stack s ox oy sx sy ex ey geometry⟩

/-- Initialization resets the cursor. Axis setup preserves it; there are no
preconditions on the old cursor or stale contents of the intercept buffer. -/
theorem empty_collection (s : X86Memory.State) (ox oy sx sy ex ey : Fixed)
    (geometry : OriginalPathInit.Inputs s ox oy sx sy ex ey)
    (safe : StackSafe (s.regs 4-60) 0x2c028)
    (resolve : Collision.Intercept → Word) :
    OriginalLineCollection.Tracks (grid s).core 0x2ba20 resolve #[] 0 := by
  have init := OriginalPathInit.ready s ox oy sx sy ex ey geometry
  have cursor := congrArg (fun v => v.1) init.globals
  have keep := E1M1PathMapSetup.after_frame (OriginalPathInit.result s).core 0x2c028
    (by rw [init.stack]; exact safe)
  constructor
  · intro i hi
    simp at hi
  · change load32 (grid s).core.memory 0x2c028=0x2ba20+BitVec.ofNat 32 (12*0)
    simpa [grid] using keep.trans cursor
  · decide

/-- The actual incremented DOS epoch represents the source's all-false array.
Freshness and separation are entry-memory contracts, including on counter wrap. -/
theorem initial_visits (s : X86Memory.State) (ox oy sx sy ex ey : Fixed)
    (geometry : OriginalPathInit.Inputs s ox oy sx sy ex ey)
    (lines : Word) (count : Nat)
    (epochSafe : StackSafe (s.regs 4-60) 0x13580)
    (stampSafe : ∀ j<count, E1M1PathMapSetup.Safe s (OriginalLineVisits.stamp lines j))
    (fresh : ∀ j<count, load32 s.memory (OriginalLineVisits.stamp lines j)≠load32 s.memory 0x13580+1) :
    OriginalLineVisits.Represents (grid s).core.memory lines (load32 s.memory 0x13580+1)
      (Array.replicate count false) := by
  have init := OriginalPathInit.ready s ox oy sx sy ex ey geometry
  have epoch := congrArg (fun v => v.2.2) init.globals
  have keep := E1M1PathMapSetup.after_frame (OriginalPathInit.result s).core 0x13580
    (by rw [init.stack]; exact epochSafe)
  apply OriginalLineVisits.fresh_represents
  · exact keep.trans epoch
  · intro j hj
    rw [E1M1PathMapSetup.grid_frame s ox oy sx sy ex ey geometry _ (stampSafe j hj)]
    exact fresh j hj
end Doom.Proofs.E1M1QueryInit
