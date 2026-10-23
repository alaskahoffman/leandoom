import Doom.Proofs.E1M1AimObjectRegions
set_option backward.isDefEq.respectTransparency false
namespace Doom.Proofs.E1M1AimCatalogRegions
open Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1NoiseAllocation (Region)
open E1M1AimObjectRegions (Storage Located)
open E1M1AimCatalog (Portal)
open E1M1CellWalkInvariant (Context)

/-- Per-object region placement for exactly the represented hits/openings.
No global separation between two read-only objects is required. -/
structure Layout (stack : Region) (hits : Array Intercept) (lookup : Intercept → Word)
    (portals : Nat → Option Portal) : Prop where
  hit : ∀ i<hits.size, if hits[i]!.isLine then Storage stack (lookup hits[i]!) 62
    else Storage stack (lookup hits[i]!) 108
  portal : ∀ i<hits.size, ∀ p, portals i=some p →
    Storage stack (lookup hits[i]!) 62 ∧ Storage stack p.front 8 ∧ Storage stack p.back 8

theorem located (stack : Region) (hits : Array Intercept) (lookup : Intercept → Word)
    (portals : Nat → Option Portal) (placement : Layout stack hits lookup portals) :
    ∀ a∈E1M1AimRetryCatalog.reads hits lookup portals, Located stack a := by
  intro a member
  obtain ⟨i,hi,member⟩ := List.mem_flatMap.mp member
  have index := List.mem_range.mp hi
  simp only [List.mem_append] at member
  rcases member with hit|portal
  · have storage := placement.hit i index
    cases kind : hits[i]!.isLine
    · simp only [kind,Bool.false_eq_true,if_false] at hit storage
      exact E1M1AimObjectRegions.actor stack _ storage a hit
    · simp only [kind,if_true,List.mem_singleton] at hit storage
      subst a
      exact E1M1AimObjectRegions.wall stack _ storage
  · cases listed : portals i with
    | none => simp only [listed,List.not_mem_nil] at portal
    | some p =>
      have storage := placement.portal i index p listed
      exact E1M1AimObjectRegions.opening stack _ _ _ storage.1 storage.2.1 storage.2.2 a
        (by simpa only [listed] using portal)

/-- All read addresses survive the controller prologue without a separate
pairwise SafeReads premise. -/
theorem prologue_safe (stack : Region) (s : X86Memory.State)
    (hits : Array Intercept) (lookup : Intercept → Word) (portals : Nat → Option Portal)
    (reserve : E1M1AimRegions.StackReserve stack s) (placement : Layout stack hits lookup portals) :
    E1M1AimControllerInputs.SafeReads s (E1M1AimRetryCatalog.reads hits lookup portals) := by
  apply E1M1AimRegions.safe_reads stack s _ reserve
  intro a member
  obtain ⟨r,inside,apartStack,_⟩ := located stack hits lookup portals placement a member
  exact ⟨r,inside,apartStack⟩

/-- The later collection and first-selection frames remain explicit. The
query-setup part, including path initialization, is derived from region bounds. -/
theorem read (q : Context) (stack : Region) (s : X86Memory.State)
    (hits : Array Intercept) (portals : Nat → Option Portal)
    (reserve : E1M1AimSetupFootprint.Reserve stack s)
    (placement : Layout stack hits (E1M1ThingFinish.resolve q.lines q.objects) portals)
    (later : ∀ a∈E1M1AimRetryCatalog.reads hits (E1M1ThingFinish.resolve q.lines q.objects) portals,
      E1M1FiringMapState.Safe q.sp q.lines a ∧ E1M1AimEntryFrame.SafeWord (q.sp-112) a) :
    ∀ a∈E1M1AimRetryCatalog.reads hits (E1M1ThingFinish.resolve q.lines q.objects) portals,
      E1M1AimPreRayMemory.Read q s a := by
  intro a member
  have safe := E1M1AimObjectRegions.setup_safe stack s a reserve
    (located stack hits _ portals placement a member)
  exact ⟨safe,safe.later,later a member⟩
end Doom.Proofs.E1M1AimCatalogRegions
