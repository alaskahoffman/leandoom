import Doom.Proofs.E1M1AimCatalogRegions
set_option backward.isDefEq.respectTransparency false
namespace Doom.Proofs.E1M1AimCatalogEntry
open Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1NoiseAllocation (Region)
open E1M1CellWalkInvariant (Context)
open E1M1AimCatalog (Portal)
open E1M1AimQueryCatalog (view)
open E1M1AimPreRayMemory (Later)
open E1M1ThingFinish (resolve)
open E1M1AimQueryCaller (callerSlots)

/-- The unchanged contents and non-read guards of the pre-ray catalog. The
three actor/wall/portal read-guard fields are constructed from region placement
below. Callback, saved-word and collection conditions are not silently removed. -/
structure OtherInputs (q : Context) (s : X86Memory.State) (scene : Scene) (shooter : Nat)
    (hits : Array Intercept) (portals : Nat → Option Portal) (walls : Nat → Prop) (who : Word) : Prop where
  layout : E1M1AimCycleInvariant.Layout (view q s) hits
  query : ∀ a∈[(0x2b9b8#32),0x2b9a8], E1M1AimMapFrame.StableWord (view q s) a
  clip : E1M1AimNextLine.ClipGlobalsSafe (view q s)
  portals : E1M1AimCatalog.Catalog (view q s) hits (resolve q.lines q.objects) portals
  valueReads : ∀ a∈[(0x2b9b8#32),0x2b9a8], Later q s a
  shooterReg : s.regs 0=who
  shooterSafe : E1M1AimMapFrame.StableWord (view q s) 0x2b9ac
  shooterLater : Later q s 0x2b9ac
  saveSafe : E1M1AimActorReturn.Safe (view q s)
  actors : ∀ i<hits.size, hits[i]!.isLine=false →
    hits[i]!.id<scene.things.size ∧ (resolve q.lines q.objects hits[i]! = who ↔ hits[i]!.id=shooter) ∧
    E1M1AimActorCatalog.Entry (view q s) (resolve q.lines q.objects hits[i]!) scene.things[hits[i]!.id]!
  walls : E1M1AimWallCatalog.Catalog (view q s) hits (resolve q.lines q.objects) walls
  targetSafe : E1M1AimMapFrame.StableWord (view q s) 0x2b9f8
  savedSafe : ∀ a∈E1M1AimSavedCaller.words (q.sp-136), E1M1AimSavedWords.Protect (view q s) a
  globalReads : ∀ a∈[(0x2c1e4#32),0x2c1e8,0x2b9f8], Later q s a
  callerReads : ∀ off∈callerSlots, Later q s ((q.sp-136)+off)


/-- Build the existing complete pre-ray catalog, deriving all three families of
setup read guards and retaining the explicit later collection/selection frames. -/
theorem initial (q : Context) (stack : Region) (s : X86Memory.State) (scene : Scene)
    (shooter : Nat) (hits : Array Intercept) (portals : Nat → Option Portal)
    (walls : Nat → Prop) (who : Word)
    (reserve : E1M1AimSetupFootprint.Reserve stack s)
    (placement : E1M1AimCatalogRegions.Layout stack hits (resolve q.lines q.objects) portals)
    (later : ∀ a∈E1M1AimRetryCatalog.reads hits (resolve q.lines q.objects) portals,
      E1M1FiringMapState.Safe q.sp q.lines a ∧ E1M1AimEntryFrame.SafeWord (q.sp-112) a)
    (other : OtherInputs q s scene shooter hits portals walls who) :
    E1M1AimPreRayCatalog.Initial q s scene shooter hits portals walls who := by
  have read := E1M1AimCatalogRegions.read q stack s hits portals reserve placement later
  refine ⟨other.layout,other.query,other.clip,?_,other.portals,other.valueReads,?_,
    other.shooterReg,other.shooterSafe,other.shooterLater,other.saveSafe,other.actors,?_,
    other.walls,other.targetSafe,other.savedSafe,other.globalReads,other.callerReads⟩
  · intro i hi p hp a ha
    exact read a (E1M1AimRetryCatalog.portal_reads hits _ portals i hi p hp a ha)
  · intro i hi kind a ha
    exact read a (E1M1AimRetryCatalog.actor_reads hits _ portals i hi kind a ha)
  · intro i hi wall
    exact read _ (E1M1AimRetryCatalog.wall_reads hits _ portals i hi (other.walls i hi wall).1)

/-- Feed the reconstructed catalog to the existing real setup-to-traversal
transport, including the shooter global written by setup. -/
theorem remaining (q : Context) (stack : Region) (s : X86Memory.State) (scene : Scene)
    (shooter : Nat) (thing : SolidThing) (angle : Angle) (distance : Fixed)
    (hits : Array Intercept) (portals : Nat → Option Portal) (walls : Nat → Prop) (who : Word)
    (geometry : E1M1AimGeometry.Inputs s thing angle distance
      (Fixed.ofInt q.world.grid.origin.x) (Fixed.ofInt q.world.grid.origin.y))
    (reserve : E1M1AimSetupFootprint.Reserve stack s)
    (placement : E1M1AimCatalogRegions.Layout stack hits (resolve q.lines q.objects) portals)
    (later : ∀ a∈E1M1AimRetryCatalog.reads hits (resolve q.lines q.objects) portals,
      E1M1FiringMapState.Safe q.sp q.lines a ∧ E1M1AimEntryFrame.SafeWord (q.sp-112) a)
    (other : OtherInputs q s scene shooter hits portals walls who) :
    E1M1AimSetupCatalog.Remaining q (E1M1PathMapQuery.traversal s).core scene shooter hits portals walls who :=
  E1M1AimPreRayCatalog.remaining q s scene shooter thing angle distance hits portals walls who geometry
    (initial q stack s scene shooter hits portals walls who reserve placement later other)

/-- Carry the constructed catalog through the actual outer prologue as well.
The shooter angle retains its separate guard because the shooter need not occur
in the hit catalog. No reached register or memory image is supplied. -/
theorem controller (q : Context) (stack : Region) (s : X86Memory.State) (f : Option Flags)
    (angle : Angle) (scene : Scene) (shooter : Nat) (hits : Array Intercept)
    (portals : Nat → Option Portal) (walls : Nat → Prop) (who : Word)
    (room : stack.lo+124 ≤ (s.regs 4).toNat)
    (top : (s.regs 4).toNat ≤ stack.hi) (bound : stack.hi ≤ 2^32)
    (placement : E1M1AimCatalogRegions.Layout stack hits (resolve q.lines q.objects) portals)
    (later : ∀ a∈E1M1AimRetryCatalog.reads hits (resolve q.lines q.objects) portals,
      E1M1FiringMapState.Safe q.sp q.lines a ∧ E1M1AimEntryFrame.SafeWord (q.sp-112) a)
    (other : OtherInputs q (E1M1AimControllerInputs.layout s angle) scene shooter hits portals walls who)
    (value : load32 s.memory (s.regs 0+32)=angle.raw.toBitVec)
    (angleSafe : ∀ b∈OriginalBulletSlope.saveWrites s, Apart (s.regs 0+32) b) :
    E1M1AimPreRayCatalog.Initial q (E1M1AimControllerEntry.entry s f).core scene shooter hits portals walls who := by
  have small : E1M1AimRegions.StackReserve stack s := ⟨by omega,top,bound⟩
  exact E1M1AimControllerInputs.catalog q s f angle scene shooter hits portals walls who
    (E1M1AimControllerInputs.registers s f angle value angleSafe)
    (initial q stack (E1M1AimControllerInputs.layout s angle) scene shooter hits portals walls who
      (E1M1AimSetupFootprint.controller_reserve stack s angle room top bound) placement later other)
    (E1M1AimCatalogRegions.prologue_safe stack s hits _ portals small placement)

/-- The original opening helper computes the same signed floor/ceiling extrema
using region-derived protection, including its own sixteen-byte stack saves. -/
theorem opening_heights (stack : Region) (s : X86Memory.State) (front back ff fc bf bc : Word)
    (reserve : E1M1AimObjectRegions.OpeningReserve stack s)
    (lineStorage : E1M1AimObjectRegions.Storage stack (s.regs 0) 62)
    (frontStorage : E1M1AimObjectRegions.Storage stack front 8)
    (backStorage : E1M1AimObjectRegions.Storage stack back 8)
    (side : load16 s.memory (s.regs 0+24) ≠ 0xffff)
    (frontPtr : load32 s.memory (s.regs 0+46)=front)
    (backPtr : load32 s.memory (s.regs 0+50)=back)
    (frontFloor : load32 s.memory front=ff) (frontCeiling : load32 s.memory (front+4)=fc)
    (backFloor : load32 s.memory back=bf) (backCeiling : load32 s.memory (back+4)=bc) :
    load32 (E1M1NoiseOpening.result s).core.memory 0x2c034=(if bc.toInt≤fc.toInt then bc else fc) ∧
    load32 (E1M1NoiseOpening.result s).core.memory 0x2c030=(if ff.toInt≤bf.toInt then bf else ff) :=
  E1M1OpeningHeights.heights s front back ff fc bf bc
    (E1M1AimObjectRegions.opening_safe stack s front back reserve lineStorage frontStorage backStorage)
    side frontPtr backPtr frontFloor frontCeiling backFloor backCeiling
end Doom.Proofs.E1M1AimCatalogEntry
