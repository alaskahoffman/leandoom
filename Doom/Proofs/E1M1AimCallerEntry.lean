import Doom.Proofs.E1M1AimCallerRegions
set_option backward.isDefEq.respectTransparency false
namespace Doom.Proofs.E1M1AimCallerEntry
open Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1NoiseAllocation (Region)
open E1M1CellWalkInvariant (Context)
open E1M1AimCatalog (Portal)
open E1M1AimQueryCatalog (view)
open E1M1AimPreRayMemory (Later)
open E1M1ThingFinish (resolve)
open E1M1AimQueryCaller (callerSlots)

/-- All predecessor catalog fields except callerReads. The stack-position
relation needed to derive it is explicit in the constructors below. -/
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
  actors : ∀ i<hits.size, hits[i]!.isLine=false →
    hits[i]!.id<scene.things.size ∧ (resolve q.lines q.objects hits[i]! = who ↔ hits[i]!.id=shooter) ∧
    E1M1AimActorCatalog.Entry (view q s) (resolve q.lines q.objects hits[i]!) scene.things[hits[i]!.id]!
  walls : E1M1AimWallCatalog.Catalog (view q s) hits (resolve q.lines q.objects) walls
  targetSafe : E1M1AimMapFrame.StableWord (view q s) 0x2b9f8
  globalReads : ∀ a∈[(0x2c1e4#32),0x2c1e8,0x2b9f8], Later q s a

/-- Reconstruct caller-read guards from the actual aim-entry stack relation. -/
theorem other (q : Context) (stack : Region) (s : X86Memory.State) (scene : Scene)
    (shooter : Nat) (hits : Array Intercept) (portals : Nat → Option Portal)
    (walls : Nat → Prop) (who : Word)
    (placement : E1M1AimCallbackRegions.Layout stack q.lines)
    (reserve : E1M1AimWalkRegions.Reserve stack q.sp) (position : s.regs 4=q.sp-24)
    (input : OtherInputs q s scene shooter hits portals walls who) :
    E1M1AimSavedEntry.OtherInputs q s scene shooter hits portals walls who := by
  exact {
    layout := input.layout
    query := input.query
    clip := input.clip
    portals := input.portals
    valueReads := input.valueReads
    shooterReg := input.shooterReg
    shooterSafe := input.shooterSafe
    shooterLater := input.shooterLater
    actors := input.actors
    walls := input.walls
    targetSafe := input.targetSafe
    globalReads := input.globalReads
    callerReads := E1M1AimCallerRegions.callers stack q s placement reserve position
  }

/-- Catalog join with original caller-read protection derived. -/
theorem initial (q : Context) (stack : Region) (s : X86Memory.State) (scene : Scene)
    (shooter : Nat) (hits : Array Intercept) (portals : Nat → Option Portal)
    (walls : Nat → Prop) (who : Word)
    (reserve : E1M1AimSetupFootprint.Reserve stack s)
    (placement : E1M1AimStampRegions.Layout stack q.lines hits (resolve q.lines q.objects) portals)
    (walkReserve : E1M1AimWalkRegions.Reserve stack q.sp)
    (callerPlacement : E1M1AimCallbackRegions.Layout stack q.lines)
    (position : s.regs 4=q.sp-24)
    (other : OtherInputs q s scene shooter hits portals walls who) :
    E1M1AimPreRayCatalog.Initial q s scene shooter hits portals walls who := by
  exact E1M1AimSavedEntry.initial q stack s scene shooter hits portals walls who reserve placement walkReserve callerPlacement
    (E1M1AimCallerEntry.other q stack s scene shooter hits portals walls who callerPlacement walkReserve position other)

/-- Catalog join with original caller-read protection derived. -/
theorem remaining (q : Context) (stack : Region) (s : X86Memory.State) (scene : Scene)
    (shooter : Nat) (thing : SolidThing) (angle : Angle) (distance : Fixed)
    (hits : Array Intercept) (portals : Nat → Option Portal) (walls : Nat → Prop) (who : Word)
    (geometry : E1M1AimGeometry.Inputs s thing angle distance
      (Fixed.ofInt q.world.grid.origin.x) (Fixed.ofInt q.world.grid.origin.y))
    (reserve : E1M1AimSetupFootprint.Reserve stack s)
    (placement : E1M1AimStampRegions.Layout stack q.lines hits (resolve q.lines q.objects) portals)
    (walkReserve : E1M1AimWalkRegions.Reserve stack q.sp)
    (callerPlacement : E1M1AimCallbackRegions.Layout stack q.lines)
    (position : s.regs 4=q.sp-24)
    (other : OtherInputs q s scene shooter hits portals walls who) :
    E1M1AimSetupCatalog.Remaining q (E1M1PathMapQuery.traversal s).core scene shooter hits portals walls who := by
  exact E1M1AimSavedEntry.remaining q stack s scene shooter thing angle distance hits portals walls who geometry reserve placement walkReserve callerPlacement
    (E1M1AimCallerEntry.other q stack s scene shooter hits portals walls who callerPlacement walkReserve position other)

/-- Catalog join with original caller-read protection derived. -/
theorem controller (q : Context) (stack : Region) (s : X86Memory.State) (f : Option Flags)
    (angle : Angle) (scene : Scene) (shooter : Nat) (hits : Array Intercept)
    (portals : Nat → Option Portal) (walls : Nat → Prop) (who : Word)
    (room : stack.lo+124 ≤ (s.regs 4).toNat)
    (top : (s.regs 4).toNat ≤ stack.hi) (bound : stack.hi ≤ 2^32)
    (placement : E1M1AimStampRegions.Layout stack q.lines hits (resolve q.lines q.objects) portals)
    (walkReserve : E1M1AimWalkRegions.Reserve stack q.sp)
    (callerPlacement : E1M1AimCallbackRegions.Layout stack q.lines)
    (position : s.regs 4=q.sp-4)
    (other : OtherInputs q (E1M1AimControllerInputs.layout s angle) scene shooter hits portals walls who)
    (value : load32 s.memory (s.regs 0+32)=angle.raw.toBitVec)
    (angleSafe : ∀ b∈OriginalBulletSlope.saveWrites s, Apart (s.regs 0+32) b) :
    E1M1AimPreRayCatalog.Initial q (E1M1AimControllerEntry.entry s f).core scene shooter hits portals walls who := by
  have queryPosition : (E1M1AimControllerInputs.layout s angle).regs 4=q.sp-24 := by
    simp [E1M1AimControllerInputs.layout,put,write,position,BitVec.sub_sub]
  exact E1M1AimSavedEntry.controller q stack s f angle scene shooter hits portals walls who room top bound placement walkReserve callerPlacement
    (E1M1AimCallerEntry.other q stack (E1M1AimControllerInputs.layout s angle) scene shooter hits portals walls who callerPlacement walkReserve queryPosition other) value angleSafe

end Doom.Proofs.E1M1AimCallerEntry
