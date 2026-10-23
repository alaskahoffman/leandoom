import Doom.Proofs.E1M1AimObjectCatalog
set_option backward.isDefEq.respectTransparency false
namespace Doom.Proofs.E1M1AimObjectEntry
open Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1NoiseAllocation (Region)
open E1M1CellWalkInvariant (Context)
open E1M1AimCatalog (Portal)
open E1M1AimQueryCatalog (view)
open E1M1AimPreRayMemory (Later)
open E1M1ThingFinish (resolve)
open E1M1AimQueryCaller (callerSlots)

/-- Contents, classification and identity only: all catalog address guards are
constructed from the separately supplied object placement. -/
structure OtherInputs (q : Context) (s : X86Memory.State) (scene : Scene) (shooter : Nat)
    (hits : Array Intercept) (portals : Nat → Option Portal) (walls : Nat → Prop) (who : Word) : Prop where
  portals : ∀ i<hits.size, ∀ p, portals i=some p →
    E1M1AimObjectCatalog.PortalValues s.memory hits[i]! (resolve q.lines q.objects hits[i]!) p
  shooterReg : s.regs 0=who
  actors : ∀ i<hits.size, hits[i]!.isLine=false →
    hits[i]!.id<scene.things.size ∧ (resolve q.lines q.objects hits[i]! = who ↔ hits[i]!.id=shooter) ∧
    E1M1AimObjectCatalog.ActorValues s.memory (resolve q.lines q.objects hits[i]!) scene.things[hits[i]!.id]!
  walls : ∀ i<hits.size, walls i →
    E1M1AimObjectCatalog.WallValues s.memory hits[i]! (resolve q.lines q.objects hits[i]!)

/-- The query view changes only the specification stack address; these contents
remain in the actual input memory, not an assumed future machine state. -/
theorem other (q : Context) (stack : Region) (s : X86Memory.State) (scene : Scene)
    (shooter : Nat) (hits : Array Intercept) (portals : Nat → Option Portal)
    (walls : Nat → Prop) (who : Word)
    (placement : E1M1AimCatalogRegions.Layout stack hits (resolve q.lines q.objects) portals)
    (reserve : E1M1AimWalkRegions.Reserve stack q.sp)
    (input : OtherInputs q s scene shooter hits portals walls who) :
    E1M1AimHelperEntry.OtherInputs q s scene shooter hits portals walls who := by
  exact {
    portals := E1M1AimObjectCatalog.portals stack q.sp (view q s) hits _ portals placement reserve rfl input.portals
    shooterReg := input.shooterReg
    actors := E1M1AimObjectCatalog.actors stack q.sp (view q s) scene shooter hits _ portals who placement reserve rfl input.actors
    walls := E1M1AimObjectCatalog.walls stack q.sp (view q s) hits _ portals walls placement reserve rfl input.walls
  }

/-- Catalog join with all three object-catalog guards derived from storage. -/
theorem initial (q : Context) (stack : Region) (s : X86Memory.State) (scene : Scene)
    (shooter : Nat) (hits : Array Intercept) (portals : Nat → Option Portal)
    (walls : Nat → Prop) (who : Word)
    (reserve : E1M1AimSetupFootprint.Reserve stack s)
    (placement : E1M1AimStampRegions.Layout stack q.lines hits (resolve q.lines q.objects) portals)
    (walkReserve : E1M1AimWalkRegions.Reserve stack q.sp)
    (globalPlacement : E1M1AimGlobalRegions.Layout stack q.lines) (capacity : hits.size≤128)
    (position : s.regs 4=q.sp-24)
    (other : OtherInputs q s scene shooter hits portals walls who) :
    E1M1AimPreRayCatalog.Initial q s scene shooter hits portals walls who := by
  exact E1M1AimHelperEntry.initial q stack s scene shooter hits portals walls who reserve placement walkReserve globalPlacement capacity position
    (E1M1AimObjectEntry.other q stack s scene shooter hits portals walls who placement.objects walkReserve other)

/-- Catalog join with all three object-catalog guards derived from storage. -/
theorem remaining (q : Context) (stack : Region) (s : X86Memory.State) (scene : Scene)
    (shooter : Nat) (thing : SolidThing) (angle : Angle) (distance : Fixed)
    (hits : Array Intercept) (portals : Nat → Option Portal) (walls : Nat → Prop) (who : Word)
    (geometry : E1M1AimGeometry.Inputs s thing angle distance
      (Fixed.ofInt q.world.grid.origin.x) (Fixed.ofInt q.world.grid.origin.y))
    (reserve : E1M1AimSetupFootprint.Reserve stack s)
    (placement : E1M1AimStampRegions.Layout stack q.lines hits (resolve q.lines q.objects) portals)
    (walkReserve : E1M1AimWalkRegions.Reserve stack q.sp)
    (globalPlacement : E1M1AimGlobalRegions.Layout stack q.lines) (capacity : hits.size≤128)
    (position : s.regs 4=q.sp-24)
    (other : OtherInputs q s scene shooter hits portals walls who) :
    E1M1AimSetupCatalog.Remaining q (E1M1PathMapQuery.traversal s).core scene shooter hits portals walls who := by
  exact E1M1AimHelperEntry.remaining q stack s scene shooter thing angle distance hits portals walls who geometry reserve placement walkReserve globalPlacement capacity position
    (E1M1AimObjectEntry.other q stack s scene shooter hits portals walls who placement.objects walkReserve other)

/-- Catalog join with all three object-catalog guards derived from storage. -/
theorem controller (q : Context) (stack : Region) (s : X86Memory.State) (f : Option Flags)
    (angle : Angle) (scene : Scene) (shooter : Nat) (hits : Array Intercept)
    (portals : Nat → Option Portal) (walls : Nat → Prop) (who : Word)
    (room : stack.lo+124 ≤ (s.regs 4).toNat)
    (top : (s.regs 4).toNat ≤ stack.hi) (bound : stack.hi ≤ 2^32)
    (placement : E1M1AimStampRegions.Layout stack q.lines hits (resolve q.lines q.objects) portals)
    (walkReserve : E1M1AimWalkRegions.Reserve stack q.sp)
    (globalPlacement : E1M1AimGlobalRegions.Layout stack q.lines) (capacity : hits.size≤128)
    (position : s.regs 4=q.sp-4)
    (other : OtherInputs q (E1M1AimControllerInputs.layout s angle) scene shooter hits portals walls who)
    (value : load32 s.memory (s.regs 0+32)=angle.raw.toBitVec)
    (angleSafe : ∀ b∈OriginalBulletSlope.saveWrites s, Apart (s.regs 0+32) b) :
    E1M1AimPreRayCatalog.Initial q (E1M1AimControllerEntry.entry s f).core scene shooter hits portals walls who := by
  exact E1M1AimHelperEntry.controller q stack s f angle scene shooter hits portals walls who room top bound placement walkReserve globalPlacement capacity position
    (E1M1AimObjectEntry.other q stack (E1M1AimControllerInputs.layout s angle) scene shooter hits portals walls who placement.objects walkReserve other) value angleSafe

end Doom.Proofs.E1M1AimObjectEntry
