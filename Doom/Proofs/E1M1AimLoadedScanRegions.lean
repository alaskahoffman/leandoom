import Doom.Proofs.E1M1AimLoadedPortal
import Doom.Proofs.E1M1LineOutput
set_option backward.isDefEq.respectTransparency false
namespace Doom.Proofs.E1M1AimLoadedScanRegions
open Verification X86 X86Memory X86Control BlockSummary
open E1M1NoiseAllocation (Region)
open E1M1AimObjectRegions (region)
open E1M1LineScan (cursor)

/-- Sufficient nonwrapping storage bounds for this loader's sixteen stack bytes. -/
def Reserve (stack : Region) (sp : Word) : Prop :=
  stack.lo+16≤sp.toNat ∧ sp.toNat≤stack.hi ∧ stack.hi≤2^32

/-- A whole line array, separated from loader stack writes. Allocation itself
is still a premise; no particular actual DOS heap placement is asserted. -/
structure Layout (total : Nat) (base : Word) (stack : Region) : Prop where
  bound : base.toNat+62*total≤2^32
  stackApart : (region base (62*total)).Disjoint stack

/-- A read-only sector prefix can alias another sector, but not line writes. -/
structure Sector (total : Nat) (base address : Word) (stack : Region) : Prop where
  bound : address.toNat+8≤2^32
  linesApart : (region address 8).Disjoint (region base (62*total))
  stackApart : (region address 8).Disjoint stack

theorem cursor_nat (base : Word) (n : Nat) (bound : base.toNat+62*n<2^32) :
    (cursor base 62 n).toNat=base.toNat+62*n := by
  induction n with
  | zero => simp [cursor]
  | succ n ih =>
    have prev := ih (by omega)
    simp only [cursor,BitVec.toNat_add,prev]
    change (base.toNat+62*n+62)%4294967296=base.toNat+62*(n+1)
    omega

theorem record_field (total : Nat) (base : Word) (i off : Nat)
    (bound : base.toNat+62*total≤2^32) (inside : i<total) (fits : off+4≤62) :
    (region base (62*total)).Contains (cursor base 62 i+BitVec.ofNat 32 off) := by
  have pos := cursor_nat base i (by omega)
  have inRecord := E1M1AimRegions.field (cursor base 62 i) 62 off (by omega) fits
  simp only [region,Region.Contains,pos] at inRecord ⊢
  omega

theorem records_apart (total : Nat) (base : Word) (i j : Nat)
    (bound : base.toNat+62*total≤2^32) (order : i<j) (inside : j<total) :
    (region (cursor base 62 i) 62).Disjoint (region (cursor base 62 j) 62) := by
  have left := cursor_nat base i (by omega)
  have right := cursor_nat base j (by omega)
  exact Or.inl (by simp only [region,left,right]; omega)

/-- Convert a disjoint read region into all actual body write guards,
including unaligned halfword stores and the diagonal FixedDiv call's stack. -/
theorem protected_read (r stack : Region) (a output sp : Word)
    (read : r.Contains a) (bound : output.toNat+62≤2^32)
    (lineApart : r.Disjoint (region output 62)) (stackApart : r.Disjoint stack)
    (reserve : Reserve stack sp) : E1M1LineFrame.Protected a output sp := by
  have word (off : Nat) (fits : off+4≤62) : Apart a (output+BitVec.ofNat 32 off) :=
    Region.apart read (E1M1AimRegions.field output 62 off bound fits) lineApart
  refine ⟨?_,?_,?_⟩
  · intro off member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      exact word _ (by decide)
  · intro off member
    have whole : Apart a (output+off) := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl|rfl|rfl|rfl <;> exact word _ (by decide)
    intro i j eq
    exact whole i ⟨j.val,by omega⟩ eq
  · have saved (n : Nat) (low : 4≤n) (high : n≤16) : stack.Contains (sp-BitVec.ofNat 32 n) := by
      have size := sp.isLt
      simp only [Reserve] at reserve
      simp only [Region.Contains,BitVec.toNat_sub,BitVec.toNat_ofNat]
      omega
    intro off member
    apply Region.apart read ?_ stackApart
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl <;> exact saved _ (by decide) (by decide)

theorem earlier_field (total : Nat) (base sp : Word) (stack : Region) (i j off : Nat)
    (layout : Layout total base stack) (reserve : Reserve stack sp)
    (order : i<j) (inside : j<total) (fits : off+4≤62) :
    E1M1LineFrame.Protected (cursor base 62 i+BitVec.ofNat 32 off) (cursor base 62 j) sp := by
  have left := cursor_nat base i (by have := layout.bound; omega)
  have right := cursor_nat base j (by have := layout.bound; omega)
  have all := layout.bound
  apply protected_read (region (cursor base 62 i) 62) stack _ _ sp
    (E1M1AimRegions.field _ 62 off (by omega) fits) (by omega)
    (records_apart total base i j all order inside) ?_ reserve
  rcases layout.stackApart with before|after
  · exact Or.inl (by simp only [region,left]; simp only [region] at before; omega)
  · exact Or.inr (by simp only [region,left]; simp only [region] at after; omega)

theorem sector_field (total : Nat) (base address sp : Word) (stack : Region) (j off : Nat)
    (layout : Layout total base stack) (sector : Sector total base address stack)
    (reserve : Reserve stack sp) (inside : j<total) (fits : off+4≤8) :
    E1M1LineFrame.Protected (address+BitVec.ofNat 32 off) (cursor base 62 j) sp := by
  have pos := cursor_nat base j (by have := layout.bound; omega)
  have all := layout.bound
  apply protected_read (region address 8) stack _ _ sp
    (E1M1AimRegions.field address 8 off sector.bound fits) (by omega) ?_ sector.stackApart reserve
  rcases sector.linesApart with before|after
  · exact Or.inl (by simp only [region,pos]; simp only [region] at before; omega)
  · exact Or.inr (by simp only [region,pos]; simp only [region] at after; omega)

/-- All eight portal reads survive any later line iteration. No pairwise
nonaliasing assumption between front and back sectors is needed. -/
theorem portal_reads (total : Nat) (base sp : Word) (stack : Region) (i j : Nat)
    (p : E1M1AimCatalog.Portal) (layout : Layout total base stack)
    (front : Sector total base p.front stack) (back : Sector total base p.back stack)
    (reserve : Reserve stack sp) (order : i<j) (inside : j<total) :
    ∀ a∈E1M1AimLoadedPortal.reads (cursor base 62 i) p,
      E1M1LineFrame.Protected a (cursor base 62 j) sp := by
  intro a member
  simp only [E1M1AimLoadedPortal.reads,E1M1OpeningHeights.reads,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact earlier_field total base sp stack i j 16 layout reserve order inside (by decide)
  · exact earlier_field total base sp stack i j 24 layout reserve order inside (by decide)
  · exact earlier_field total base sp stack i j 46 layout reserve order inside (by decide)
  · exact earlier_field total base sp stack i j 50 layout reserve order inside (by decide)
  · simpa using sector_field total base p.front sp stack j 0 layout front reserve inside (by decide)
  · exact sector_field total base p.front sp stack j 4 layout front reserve inside (by decide)
  · simpa using sector_field total base p.back sp stack j 0 layout back reserve inside (by decide)
  · exact sector_field total base p.back sp stack j 4 layout back reserve inside (by decide)
/-- The same allocation bounds discharge the current suffix's sector guards. -/
theorem sector_safe (total : Nat) (base sp : Word) (stack : Region) (i : Nat)
    (p : E1M1AimCatalog.Portal) (layout : Layout total base stack)
    (front : Sector total base p.front stack) (back : Sector total base p.back stack)
    (reserve : Reserve stack sp) (inside : i<total) :
    E1M1AimLoadedPortal.SectorSafe (cursor base 62 i) p := by
  intro a member
  have protect : E1M1LineFrame.Protected a (cursor base 62 i) sp := by
    simp only [E1M1AimLoadedPortal.sectorReads,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl
    · simpa using sector_field total base p.front sp stack i 0 layout front reserve inside (by decide)
    · exact sector_field total base p.front sp stack i 4 layout front reserve inside (by decide)
    · simpa using sector_field total base p.back sp stack i 0 layout back reserve inside (by decide)
    · exact sector_field total base p.back sp stack i 4 layout back reserve inside (by decide)
  exact ⟨⟨protect.halves 22 (by simp),protect.halves 24 (by simp)⟩,
    protect.words 46 (by simp),protect.words 50 (by simp)⟩
end Doom.Proofs.E1M1AimLoadedScanRegions
