import Doom.Proofs.E1M1AimStampRegions
set_option backward.isDefEq.respectTransparency false
namespace Doom.Proofs.E1M1AimCollectionEntry
open Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1NoiseAllocation (Region)
open E1M1CellWalkInvariant (Context)
open E1M1AimCatalog (Portal)
open E1M1ThingFinish (resolve)
open E1M1AimCatalogEntry (OtherInputs)

/-- Supply the formerly explicit collection/first-selection guards from region
placement, line-record identity and one scalar context stack reserve. -/
theorem later (q : Context) (stack : Region) (hits : Array Intercept) (portals : Nat → Option Portal)
    (walkReserve : E1M1AimWalkRegions.Reserve stack q.sp)
    (placement : E1M1AimStampRegions.Layout stack q.lines hits (resolve q.lines q.objects) portals) :
    ∀ a∈E1M1AimRetryCatalog.reads hits (resolve q.lines q.objects) portals,
      E1M1FiringMapState.Safe q.sp q.lines a ∧ E1M1AimEntryFrame.SafeWord (q.sp-112) a := by
  intro a member
  have located := E1M1AimCatalogRegions.located stack hits _ portals placement.objects a member
  exact ⟨E1M1AimWalkRegions.collection stack q.sp q.lines a walkReserve located
      (E1M1AimStampRegions.stamps stack q.lines hits _ portals placement a member),
    E1M1AimWalkRegions.selection stack q.sp a walkReserve located⟩

/-- Persistent ordered-hit read protection for every actor/wall/portal word. -/
theorem stable (q : Context) (stack : Region) (s : X86Memory.State)
    (hits : Array Intercept) (portals : Nat → Option Portal)
    (walkReserve : E1M1AimWalkRegions.Reserve stack q.sp)
    (placement : E1M1AimCatalogRegions.Layout stack hits (resolve q.lines q.objects) portals) :
    ∀ a∈E1M1AimRetryCatalog.reads hits (resolve q.lines q.objects) portals,
      E1M1AimMapFrame.StableWord (E1M1AimQueryCatalog.view q s) a := by
  intro a member
  exact E1M1AimWalkRegions.ordered stack q.sp a _ walkReserve
    (E1M1AimCatalogRegions.located stack hits _ portals placement a member) rfl

/-- Feed the derived persistent guard into the existing complete callback,
sentinel-mark and minimum-scan frame. Execution/frame premises are unchanged. -/
theorem word (q : Context) (stack : Region) (s : X86Memory.State) (out : X86Control.State)
    (hits : Array Intercept) (portals : Nat → Option Portal) (marked : Nat) (a : Word)
    (walkReserve : E1M1AimWalkRegions.Reserve stack q.sp)
    (placement : E1M1AimCatalogRegions.Layout stack hits (resolve q.lines q.objects) portals)
    (member : a∈E1M1AimRetryCatalog.reads hits (resolve q.lines q.objects) portals)
    (frame : E1M1AimHistoryCycle.Frame (E1M1AimQueryCatalog.view q s) out)
    (pointer : (E1M1AimQueryCatalog.view q s).regs 3=E1M1MinimumScan.address marked)
    (bounded : marked<128) : load32 out.core.memory a=load32 s.memory a := by
  exact E1M1AimMapFrame.word (E1M1AimQueryCatalog.view q s) out marked a frame pointer bounded
    (stable q stack s hits portals walkReserve placement a member)

/-- Reuse the existing catalog join with derived later read guards. -/
theorem initial (q : Context) (stack : Region) (s : X86Memory.State) (scene : Scene)
    (shooter : Nat) (hits : Array Intercept) (portals : Nat → Option Portal)
    (walls : Nat → Prop) (who : Word)
    (reserve : E1M1AimSetupFootprint.Reserve stack s)
    (placement : E1M1AimStampRegions.Layout stack q.lines hits (resolve q.lines q.objects) portals)
    (walkReserve : E1M1AimWalkRegions.Reserve stack q.sp)
    (other : OtherInputs q s scene shooter hits portals walls who) :
    E1M1AimPreRayCatalog.Initial q s scene shooter hits portals walls who := by
  exact E1M1AimCatalogEntry.initial q stack s scene shooter hits portals walls who reserve placement.objects (later q stack hits portals walkReserve placement) other

/-- Reuse the existing catalog join with derived later read guards. -/
theorem remaining (q : Context) (stack : Region) (s : X86Memory.State) (scene : Scene)
    (shooter : Nat) (thing : SolidThing) (angle : Angle) (distance : Fixed)
    (hits : Array Intercept) (portals : Nat → Option Portal) (walls : Nat → Prop) (who : Word)
    (geometry : E1M1AimGeometry.Inputs s thing angle distance
      (Fixed.ofInt q.world.grid.origin.x) (Fixed.ofInt q.world.grid.origin.y))
    (reserve : E1M1AimSetupFootprint.Reserve stack s)
    (placement : E1M1AimStampRegions.Layout stack q.lines hits (resolve q.lines q.objects) portals)
    (walkReserve : E1M1AimWalkRegions.Reserve stack q.sp)
    (other : OtherInputs q s scene shooter hits portals walls who) :
    E1M1AimSetupCatalog.Remaining q (E1M1PathMapQuery.traversal s).core scene shooter hits portals walls who := by
  exact E1M1AimCatalogEntry.remaining q stack s scene shooter thing angle distance hits portals walls who geometry reserve placement.objects (later q stack hits portals walkReserve placement) other

/-- Reuse the existing catalog join with derived later read guards. -/
theorem controller (q : Context) (stack : Region) (s : X86Memory.State) (f : Option Flags)
    (angle : Angle) (scene : Scene) (shooter : Nat) (hits : Array Intercept)
    (portals : Nat → Option Portal) (walls : Nat → Prop) (who : Word)
    (room : stack.lo+124 ≤ (s.regs 4).toNat)
    (top : (s.regs 4).toNat ≤ stack.hi) (bound : stack.hi ≤ 2^32)
    (placement : E1M1AimStampRegions.Layout stack q.lines hits (resolve q.lines q.objects) portals)
    (walkReserve : E1M1AimWalkRegions.Reserve stack q.sp)
    (other : OtherInputs q (E1M1AimControllerInputs.layout s angle) scene shooter hits portals walls who)
    (value : load32 s.memory (s.regs 0+32)=angle.raw.toBitVec)
    (angleSafe : ∀ b∈OriginalBulletSlope.saveWrites s, Apart (s.regs 0+32) b) :
    E1M1AimPreRayCatalog.Initial q (E1M1AimControllerEntry.entry s f).core scene shooter hits portals walls who := by
  exact E1M1AimCatalogEntry.controller q stack s f angle scene shooter hits portals walls who room top bound placement.objects (later q stack hits portals walkReserve placement) other value angleSafe

end Doom.Proofs.E1M1AimCollectionEntry
