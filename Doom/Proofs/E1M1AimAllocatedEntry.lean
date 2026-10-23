import Doom.Proofs.E1M1AimStaticRegions
set_option backward.isDefEq.respectTransparency false
namespace Doom.Proofs.E1M1AimAllocatedEntry
open Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1NoiseAllocation (Region)
open E1M1CellWalkInvariant (Context)
open E1M1AimRegions (StackReserve Covered safe_reads)
open E1M1AimStaticRegions (Layout)
open E1M1AimControllerInputs (layout)

/-- The complete setup read guard follows from fixed map sizes and scalar
region placement, for every 32-bit angle and every memory contents. -/
theorem setup_safe (q : Context) (stack : Region) (s : X86Memory.State) (angle : Angle)
    (reserve : StackReserve stack s) (placement : Layout stack q.base q.lines (s.regs 0))
    (words : q.words.size=3461) (lines : q.world.lines.size=475) :
    E1M1AimControllerInputs.SafeReads s (E1M1AimControllerSetup.reads q s angle) := by
  apply safe_reads stack s _ reserve
  intro a member
  simp only [E1M1AimControllerSetup.reads,List.mem_append] at member
  rcases member with (geometry|map)|stamp
  · exact E1M1AimStaticRegions.geometry_covered stack q.base q.lines s angle placement a geometry
  · exact E1M1AimStaticRegions.map_covered stack q.base q.lines (s.regs 0) q.words placement words a map
  · exact E1M1AimStaticRegions.stamps_covered stack q.base q.lines (s.regs 0) _ placement lines a stamp

/-- The angle used to establish the actual entry registers also lies in the
shooter prefix, so it needs no separate pairwise non-aliasing premise. -/
theorem angle_safe (stack : Region) (s : X86Memory.State) (base lines : Word)
    (reserve : StackReserve stack s) (placement : Layout stack base lines (s.regs 0)) :
    ∀ b∈OriginalBulletSlope.saveWrites s, Apart (s.regs 0+32) b := by
  intro b member
  have inside := E1M1AimRegions.field (s.regs 0) 72 32 placement.shooterBound (by decide)
  apply Region.apart inside (E1M1AimRegions.writes_contained stack s reserve b ?_) placement.shooterStack
  simp only [OriginalBulletSlope.saveWrites,List.mem_cons,List.not_mem_nil,or_false] at member
  simp only [E1M1AimControllerEntry.writes,List.mem_cons,List.not_mem_nil,or_false]
  rcases member with h|h|h|h <;> simp [h]

/-- Connect the range facts to the existing real-prologue input transport.
Map/object encodings, inner-query guards and freshness remain in `before`;
no initial-state or reachability claim is hidden in the layout certificate. -/
theorem inputs (q : Context) (stack : Region) (s : X86Memory.State) (f : Option Flags)
    (thing : SolidThing) (angle : Angle)
    (reserve : StackReserve stack s) (placement : Layout stack q.base q.lines (s.regs 0))
    (words : q.words.size=3461)
    (before : E1M1AimSetupEntry.Inputs q (layout s angle) thing angle (Fixed.ofInt 1024))
    (tables : ThrustTables s.memory) (value : load32 s.memory (s.regs 0+32)=angle.raw.toBitVec) :
    E1M1AimSetupEntry.Inputs q (E1M1AimControllerEntry.entry s f).core thing angle (Fixed.ofInt 1024) ∧
    ThrustTables (E1M1AimControllerEntry.entry s f).core.memory ∧
    (E1M1AimControllerEntry.entry s f).core.regs=(layout s angle).regs := by
  have regs := E1M1AimControllerInputs.registers s f angle value (angle_safe stack s _ _ reserve placement)
  exact ⟨E1M1AimControllerSetup.setup q s f thing angle regs before tables
      (setup_safe q stack s angle reserve placement words before.lineCount),
    E1M1AimControllerData.tables s f tables
      (E1M1AimStaticRegions.tables_safe stack s reserve placement.globalsStack),regs⟩

/-- Protect all linedef stamps for any epoch, including either retry epoch.
This preserves an existing freshness fact; it does not manufacture freshness. -/
theorem fresh (stack : Region) (s : X86Memory.State) (f : Option Flags)
    (base lines epoch : Word) (reserve : StackReserve stack s)
    (placement : Layout stack base lines (s.regs 0))
    (before : E1M1AimStampImage.Fresh s.memory lines epoch 475) :
    E1M1AimStampImage.Fresh (E1M1AimControllerEntry.entry s f).core.memory lines epoch 475 := by
  apply E1M1AimControllerData.fresh s f lines epoch 475 before
  intro j hj b hb
  exact Region.apart (E1M1AimStaticRegions.line_stamp lines placement.linesBound j hj)
    (E1M1AimRegions.writes_contained stack s reserve b hb) placement.linesStack
end Doom.Proofs.E1M1AimAllocatedEntry
