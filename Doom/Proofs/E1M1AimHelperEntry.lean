import Doom.Proofs.E1M1AimHelperRegions
set_option backward.isDefEq.respectTransparency false
namespace Doom.Proofs.E1M1AimHelperEntry
open Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1NoiseAllocation (Region)
open E1M1CellWalkInvariant (Context)
open E1M1AimCatalog (Portal)
open E1M1AimQueryCatalog (view)
open E1M1AimPreRayMemory (Later)
open E1M1ThingFinish (resolve)
open E1M1AimQueryCaller (callerSlots)

/-- Remaining catalog obligations: portal/wall and actor memory contents,
shooter register, and pointer/identity correspondence. Fixed layout is derived. -/
structure OtherInputs (q : Context) (s : X86Memory.State) (scene : Scene) (shooter : Nat)
    (hits : Array Intercept) (portals : Nat → Option Portal) (walls : Nat → Prop) (who : Word) : Prop where
  portals : E1M1AimCatalog.Catalog (view q s) hits (resolve q.lines q.objects) portals
  shooterReg : s.regs 0=who
  actors : ∀ i<hits.size, hits[i]!.isLine=false →
    hits[i]!.id<scene.things.size ∧ (resolve q.lines q.objects hits[i]! = who ↔ hits[i]!.id=shooter) ∧
    E1M1AimActorCatalog.Entry (view q s) (resolve q.lines q.objects hits[i]!) scene.things[hits[i]!.id]!
  walls : E1M1AimWallCatalog.Catalog (view q s) hits (resolve q.lines q.objects) walls

/-- Derive the complete eleven-field callback layout. Capacity and placement
remain explicit, while catalog contents and identity are retained unchanged. -/
theorem other (q : Context) (stack : Region) (s : X86Memory.State) (scene : Scene)
    (shooter : Nat) (hits : Array Intercept) (portals : Nat → Option Portal)
    (walls : Nat → Prop) (who : Word)
    (placement : E1M1AimGlobalRegions.Layout stack q.lines)
    (reserve : E1M1AimWalkRegions.Reserve stack q.sp) (capacity : hits.size≤128)
    (input : OtherInputs q s scene shooter hits portals walls who) :
    E1M1AimGlobalEntry.OtherInputs q s scene shooter hits portals walls who := by
  exact {
    layout := E1M1AimHelperRegions.layout stack q (view q s) hits placement reserve rfl capacity
    portals := input.portals
    shooterReg := input.shooterReg
    actors := input.actors
    walls := input.walls
  }

/-- Catalog join with the complete fixed callback layout derived. -/
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
  exact E1M1AimGlobalEntry.initial q stack s scene shooter hits portals walls who reserve placement walkReserve globalPlacement position
    (E1M1AimHelperEntry.other q stack s scene shooter hits portals walls who globalPlacement walkReserve capacity other)

/-- Catalog join with the complete fixed callback layout derived. -/
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
  exact E1M1AimGlobalEntry.remaining q stack s scene shooter thing angle distance hits portals walls who geometry reserve placement walkReserve globalPlacement position
    (E1M1AimHelperEntry.other q stack s scene shooter hits portals walls who globalPlacement walkReserve capacity other)

/-- Catalog join with the complete fixed callback layout derived. -/
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
  exact E1M1AimGlobalEntry.controller q stack s f angle scene shooter hits portals walls who room top bound placement walkReserve globalPlacement position
    (E1M1AimHelperEntry.other q stack (E1M1AimControllerInputs.layout s angle) scene shooter hits portals walls who globalPlacement walkReserve capacity other) value angleSafe

end Doom.Proofs.E1M1AimHelperEntry
