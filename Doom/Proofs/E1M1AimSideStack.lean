import Doom.Proofs.E1M1AimPinnedSides
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1AimSideStack
open Verification X86 X86Memory X86Control BlockSummary
open E1M1AimTextureCatalog E1M1AimPinnedCatalog E1M1AimSideLoop
open E1M1NoiseAllocation (Region)

/-- Opt-in read-only region; unlike Persistent it may contain heap metadata or
saved caller words. Disjointness is from every output and actual stack writes. -/
structure Protected (l : LayoutData) (layout : Layout l) (r : Region) : Prop where
  output : r.Disjoint (region l.output (18*648))
  stack : r.Disjoint layout.stack

theorem protection_safe (l : LayoutData) (layout : Layout l) (r : Region)
    (safe : Protected l layout r) (i : Nat) (s : X86Memory.State)
    (regs : Registers l i s) (inside : i<648) (p : Word) (read : r.Contains p) :
    BodySafe s p := by
  have pos := at_nat l.output 18 i (by have := layout.outputBound; omega)
  apply region_safe l layout i s regs inside p r read _ safe.stack
  rcases safe.output with left|right
  · exact Or.inl (by simp only [region,pos]; simp only [region] at left; omega)
  · exact Or.inr (by simp only [region,pos]; simp only [region] at right; omega)

/-- No per-body frame hypothesis: each body guard follows from static placement. -/
theorem region_preserved (l : LayoutData) (layout : Layout l) (s : X86Memory.State)
    (f : Option Flags) (initial : Incoming l s) (r : Region) (safe : Protected l layout r)
    (p : Word) (read : r.Contains p) (n : Nat) (bound : n≤648) :
    load32 (states s f n).core.memory p=load32 s.memory p := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have inv := (states_invariant l layout s f initial n (by omega)).1
    let row : Fin 648 := ⟨n,by omega⟩
    have ready := body_ready l layout row _ inv.registers inv.image
    have frame := body_frame _ _ _ _ _ _ _ (pinned_body_catalog _ l.table l.pointer row ready) p
      (protection_safe l layout r safe n _ inv.registers (by omega) p read)
    exact frame.trans (ih (by omega))

/-- ESP+4 is the saved W_CacheLumpNum pointer; ESP+8..28 are six saved
registers and ESP+32 the caller return word. The scratch at ESP is not saved.
This region is deliberately distinct from the lower call/push reserve. -/
def upperRegion (l : LayoutData) : Region := ⟨l.sp.toNat+4,l.sp.toNat+36⟩
structure UpperStack (l : LayoutData) (layout : Layout l) : Prop where
  bound : l.sp.toNat+36≤2^32
  protection : Protected l layout (upperRegion l)

theorem upper_contains (l : LayoutData) (layout : Layout l) (upper : UpperStack l layout)
    (off : Nat) (low : 4≤off) (high : off+4≤36) :
    (upperRegion l).Contains (l.sp+BitVec.ofNat 32 off) := by
  have bound := upper.bound
  simp only [upperRegion,Region.Contains,BitVec.toNat_add,BitVec.toNat_ofNat]
  omega

theorem upper_preserved (l : LayoutData) (layout : Layout l) (s : X86Memory.State)
    (f : Option Flags) (initial : Incoming l s) (upper : UpperStack l layout)
    (off : Nat) (low : 4≤off) (high : off+4≤36) :
    load32 (states s f 648).core.memory (l.sp+BitVec.ofNat 32 off)=
      load32 s.memory (l.sp+BitVec.ofNat 32 off) :=
  region_preserved l layout s f initial (upperRegion l) upper.protection _
    (upper_contains l layout upper off low high) 648 (by decide)

theorem saved_raw_pointer (l : LayoutData) (layout : Layout l) (s : X86Memory.State)
    (f : Option Flags) (initial : Incoming l s) (upper : UpperStack l layout)
    (saved : load32 s.memory (l.sp+4)=l.raw) :
    load32 (states s f 648).core.memory ((states s f 648).core.regs 4+4)=l.raw := by
  rw [(states_invariant l layout s f initial 648 (by decide)).1.registers.stack]
  exact (upper_preserved l layout s f initial upper 4 (by decide) (by decide)).trans saved

end Doom.Proofs.E1M1AimSideStack
