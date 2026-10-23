import Doom.Proofs.E1M1AimTargetDecision
import Doom.Proofs.E1M1AimGeometry
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimSetupEntry
open Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1CellWalkInvariant (Context)
open E1M1PathMapQuery (traversal withStack)
attribute [local irreducible] load32 store32

/-- Query-entry values and address guards before ray construction. The layout
state changes only ESP; it assumes no executed memory image. -/
structure Inputs (q : Context) (s : X86Memory.State) (thing : SolidThing)
    (angle : Angle) (distance : Fixed) : Prop where
  geometry : E1M1AimGeometry.Inputs s thing angle distance
    (Fixed.ofInt q.world.grid.origin.x) (Fixed.ofInt q.world.grid.origin.y)
  stack : s.regs 4=q.sp-24
  epoch : q.epoch=load32 s.memory 0x13580+1
  trace : q.trace=(E1M1QueryCollection.path q thing.x thing.y
    (thing.attackEndpoint angle distance).1 (thing.attackEndpoint angle distance).2).trace
  lineCount : q.world.lines.size=475
  flagSafe : E1M1PathMapSetup.Safe (withStack s (s.regs 4-(28#32))) (E1M1ThingGate.flagWord q.sp)
  map : E1M1PathMapQuery.MapInputs s q.base q.lines q.words q.width q.height
  cursorSafe : E1M1PathMapSetup.StackSafe (s.regs 4-88) 0x2c028
  epochSafe : E1M1PathMapQuery.Safe s 0x13580
  stampSafe : ∀ j<q.world.lines.size, E1M1PathMapQuery.Safe s (OriginalLineVisits.stamp q.lines j)
  fresh : ∀ j<q.world.lines.size, load32 s.memory (OriginalLineVisits.stamp q.lines j)≠load32 s.memory 0x13580+1
  traceSafe : ∀ a∈E1M1ThingGeometry.traceReads, E1M1PathMapSetup.StackSafe (s.regs 4-88) a
  activeSafe : E1M1PathMapSetup.StackSafe (s.regs 4-88) 0x2c024

/-- Both callback and traversal flags are written by the real setup. -/
theorem call (s : X86Memory.State) (thing : SolidThing) (angle : Angle) (distance ox oy : Fixed)
    (geometry : E1M1AimGeometry.Inputs s thing angle distance ox oy) :
    (load32 (traversal s).core.memory ((traversal s).core.regs 4),
     load32 (traversal s).core.memory ((traversal s).core.regs 4+4),
     load32 (traversal s).core.memory ((traversal s).core.regs 4+8))=(0x2bbff,3,0x2b760) :=
  OriginalAimSetup.call_frame _ (E1M1AimGeometry.setup_inputs s thing angle distance ox oy geometry).separated

/-- Assemble every path-query entry field from pre-ray inputs. In particular,
fresh stamps are transported against the same preserved epoch word. -/
theorem entry (q : Context) (s : X86Memory.State) (thing : SolidThing)
    (angle : Angle) (distance : Fixed) (h : Inputs q s thing angle distance) :
    E1M1QueryCollection.Entry q (traversal s).core thing.x thing.y
      (thing.attackEndpoint angle distance).1 (thing.attackEndpoint angle distance).2 := by
  have sp := E1M1PathMapQuery.traversal_stack s
  have localSP : (traversal s).core.regs 4-60=s.regs 4-88 := by
    rw [sp]; simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  have epoch := E1M1PathMapQuery.traversal_frame s 0x13580 h.epochSafe
  refine ⟨E1M1AimGeometry.path_inputs s thing angle distance _ _ h.geometry,?_,?_,h.trace,h.lineCount,
    congrArg (fun t => t.2.1) (call s thing angle distance _ _ h.geometry),?_,
    E1M1PathMapQuery.map_at_traversal s _ _ _ _ _ h.map,?_,?_,?_,?_,?_,?_⟩
  · rw [sp,h.stack]; simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  · rw [epoch]; exact h.epoch
  · simpa only [E1M1PathMapSetup.Safe,OriginalPathInit.writes,sp,withStack,write,ite_true] using h.flagSafe
  · rw [localSP]; exact h.cursorSafe
  · exact (E1M1PathMapQuery.traversal_safe s _ h.epochSafe).2
  · intro j hj; exact E1M1PathMapQuery.traversal_safe s _ (h.stampSafe j hj)
  · intro j hj
    rw [E1M1PathMapQuery.traversal_frame s _ (h.stampSafe j hj),epoch]
    exact h.fresh j hj
  · rw [localSP]; exact h.traceSafe
  · rw [localSP]; exact h.activeSafe

/-- Setup creates the aiming window, null target, range and eye height; these
values do not need to be assumed at path-query entry. -/
theorem globals (s : X86Memory.State) (thing : SolidThing) (angle : Angle) (distance ox oy : Fixed)
    (geometry : E1M1AimGeometry.Inputs s thing angle distance ox oy) :
    load32 (traversal s).core.memory 0x2b9b8=distance.raw.toBitVec ∧
    load32 (traversal s).core.memory 0x2b9a8=thing.shootHeight.raw.toBitVec ∧
    load32 (traversal s).core.memory 0x2c1e4=aimBottomSlope.raw.toBitVec ∧
    load32 (traversal s).core.memory 0x2c1e8=aimTopSlope.raw.toBitVec ∧
    load32 (traversal s).core.memory 0x2b9f8=0 := by
  have input := E1M1AimGeometry.setup_inputs s thing angle distance ox oy geometry
  have values := OriginalAimSetup.live_globals _ thing angle distance input
  exact ⟨congrArg (fun t => t.2.1) values,OriginalAimSetup.live_height _ thing angle distance input,
    congrArg (fun t => t.2.2.2.1) values,congrArg (fun t => t.2.2.2.2) values,
    congrArg (fun t => t.2.2.1) values⟩
end Doom.Proofs.E1M1AimSetupEntry
