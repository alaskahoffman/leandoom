import Doom.Proofs.E1M1AimWalkRegions
set_option backward.isDefEq.respectTransparency false
namespace Doom.Proofs.E1M1AimStampRegions
open Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1NoiseAllocation (Region)
open E1M1AimCatalog (Portal)

/-- Every four-byte read ending before offset 54 is disjoint from every visit
stamp in the 475-line array, even if the array's base wraps. -/
theorem line_field (lines : Word) (i j off : Nat) (hi : i<475) (hj : j<475)
    (fits : off+4 ≤ 54) :
    Apart (E1M1ScanGeometry.linePointer lines i+BitVec.ofNat 32 off)
      (OriginalLineVisits.stamp lines j) := by
  intro x y equal
  have left : E1M1ScanGeometry.linePointer lines i+BitVec.ofNat 32 off+BitVec.ofNat 32 x.val=
      lines+BitVec.ofNat 32 (62*i+off+x.val) := by
    simp only [E1M1ScanGeometry.linePointer,BitVec.ofNat_add,BitVec.ofNat_mul]
    rw [BitVec.mul_comm (BitVec.ofNat 32 i)]
    ac_rfl
  have right : OriginalLineVisits.stamp lines j+BitVec.ofNat 32 y.val=
      lines+BitVec.ofNat 32 (62*j+54+y.val) := by
    simp only [OriginalLineVisits.stamp,BitVec.ofNat_add,BitVec.ofNat_mul]
    rw [BitVec.mul_comm (BitVec.ofNat 32 j)]
    ac_rfl
  rw [left,right] at equal
  have cancelled := congrArg (fun v : Word => v-lines) equal
  simp only [BitVec.add_comm lines,BitVec.add_sub_cancel] at cancelled
  have same := congrArg BitVec.toNat cancelled
  have xx := x.isLt; have yy := y.isLt
  simp only [BitVec.toNat_ofNat] at same
  rw [Nat.mod_eq_of_lt (show 62*i+off+x.val<2^32 by omega),
    Nat.mod_eq_of_lt (show 62*j+54+y.val<2^32 by omega)] at same
  omega

/-- An external object/sector prefix avoids every stamp by separation from the
linedef array. Line fields themselves use line_field instead. -/
theorem external_field (lines base : Word) (bytes off j : Nat)
    (lineBound : lines.toNat+475*62 ≤ 2^32) (bound : base.toNat+bytes ≤ 2^32)
    (separate : (E1M1AimObjectRegions.region base bytes).Disjoint (E1M1AimStaticRegions.linedefs lines))
    (fits : off+4 ≤ bytes) (hj : j<475) :
    Apart (base+BitVec.ofNat 32 off) (OriginalLineVisits.stamp lines j) := by
  exact Region.apart (E1M1AimRegions.field base bytes off bound fits)
    (E1M1AimStaticRegions.line_stamp lines lineBound j hj) separate

/-- Dynamic actors and sector prefixes are outside the line array; line hits
resolve to actual bounded line records. These are representation obligations. -/
structure Layout (stack : Region) (lines : Word) (hits : Array Intercept)
    (lookup : Intercept → Word) (portals : Nat → Option Portal) : Prop where
  objects : E1M1AimCatalogRegions.Layout stack hits lookup portals
  lineBound : lines.toNat+475*62 ≤ 2^32
  lineHit : ∀ i<hits.size, hits[i]!.isLine=true →
    ∃ id<475, lookup hits[i]! = E1M1ScanGeometry.linePointer lines id
  actorApart : ∀ i<hits.size, hits[i]!.isLine=false →
    (E1M1AimObjectRegions.region (lookup hits[i]!) 108).Disjoint (E1M1AimStaticRegions.linedefs lines)
  portalLine : ∀ i<hits.size, ∀ p, portals i=some p →
    ∃ id<475, lookup hits[i]! = E1M1ScanGeometry.linePointer lines id
  sectorsApart : ∀ i<hits.size, ∀ p, portals i=some p →
    (E1M1AimObjectRegions.region p.front 8).Disjoint (E1M1AimStaticRegions.linedefs lines) ∧
    (E1M1AimObjectRegions.region p.back 8).Disjoint (E1M1AimStaticRegions.linedefs lines)

theorem stamps (stack : Region) (lines : Word) (hits : Array Intercept)
    (lookup : Intercept → Word) (portals : Nat → Option Portal)
    (placement : Layout stack lines hits lookup portals) :
    ∀ a∈E1M1AimRetryCatalog.reads hits lookup portals, ∀ j<475,
      Apart a (OriginalLineVisits.stamp lines j) := by
  intro a member j hj
  obtain ⟨i,hi,member⟩ := List.mem_flatMap.mp member
  have index := List.mem_range.mp hi
  simp only [List.mem_append] at member
  rcases member with hit|portal
  · cases kind : hits[i]!.isLine
    · have storage := placement.objects.hit i index
      simp only [kind,Bool.false_eq_true,if_false] at hit storage
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hit
      rcases hit with rfl|rfl|rfl <;>
        exact external_field lines _ 108 _ j placement.lineBound storage.bound
          (placement.actorApart i index kind) (by decide) hj
    · simp only [kind,if_true,List.mem_singleton] at hit
      subst a
      obtain ⟨id,bounded,address⟩ := placement.lineHit i index kind
      rw [address]
      exact line_field lines id j 16 bounded hj (by decide)
  · cases listed : portals i with
    | none => simp only [listed,List.not_mem_nil] at portal
    | some p =>
      have storage := placement.objects.portal i index p listed
      have sectors := placement.sectorsApart i index p listed
      obtain ⟨id,bounded,address⟩ := placement.portalLine i index p listed
      simp only [listed,E1M1OpeningHeights.reads,List.mem_cons,List.not_mem_nil,or_false] at portal
      rcases portal with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      · rw [address]; exact line_field lines id j 16 bounded hj (by decide)
      · rw [address]; exact line_field lines id j 24 bounded hj (by decide)
      · rw [address]; exact line_field lines id j 46 bounded hj (by decide)
      · rw [address]; exact line_field lines id j 50 bounded hj (by decide)
      · simpa using external_field lines _ 8 0 j placement.lineBound storage.2.1.bound sectors.1 (by decide) hj
      · exact external_field lines _ 8 4 j placement.lineBound storage.2.1.bound sectors.1 (by decide) hj
      · simpa using external_field lines _ 8 0 j placement.lineBound storage.2.2.bound sectors.2 (by decide) hj
      · exact external_field lines _ 8 4 j placement.lineBound storage.2.2.bound sectors.2 (by decide) hj
end Doom.Proofs.E1M1AimStampRegions
