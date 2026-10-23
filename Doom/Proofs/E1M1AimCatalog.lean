import Doom.Proofs.E1M1AimNextLine
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1AimCatalog
open Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1MinimumScan (address)
open E1M1SelectionHistory (History)
open E1M1HistoryDispatch (Selection)
open E1M1AimHistoryCycle (Frame)
open E1M1AimCycleInvariant (Layout QuerySafe)
open E1M1AimMapFrame (Region)
open E1M1AimNextLine (ClipGlobalsSafe)
attribute [local irreducible] load32 store32

/-- Immutable descriptor for a represented two-sided line. A catalog may leave
other hits unclassified; this does not assume every hit is a line or is open. -/
structure Portal where
  front : Word
  back : Word
  ff : Word
  fc : Word
  bf : Word
  bc : Word

def Entry (s : X86Memory.State) (hit : Intercept) (line : Word) (p : Portal) : Prop :=
  hit.isLine=true ∧ Region s line p.front p.back ∧
  E1M1AimOpeningFrame.Image s.memory line p.front p.back p.ff p.fc p.bf p.bc ∧
  s.memory (line+(16#32)) &&& (4#8)≠0

def Catalog (s : X86Memory.State) (initial : Array Intercept)
    (resolve : Intercept → Word) (portals : Nat → Option Portal) : Prop :=
  ∀ i<initial.size, ∀ p, portals i=some p → Entry s initial[i]! (resolve initial[i]!) p

/-- Preserve each represented line, independently of which one was processed. -/
theorem entry_frame (s : X86Memory.State) (out : X86Control.State) (marked : Nat)
    (hit : Intercept) (line : Word) (p : Portal)
    (frame : Frame s out) (stack : out.core.regs 4=s.regs 4)
    (pointer : s.regs 3=address marked) (bounded : marked<128)
    (entry : Entry s hit line p) : Entry out.core hit line p := by
  obtain ⟨kind,region,image,two⟩ := entry
  have kept := E1M1AimMapFrame.image s out marked line p.front p.back p.ff p.fc p.bf p.bc
    frame pointer bounded region image
  exact ⟨kind,E1M1AimMapFrame.region s out.core line p.front p.back stack region,kept.1,
    by rw [kept.2]; exact two⟩

/-- One execution frame preserves the entire catalog, not just its next entry. -/
theorem preserved (s : X86Memory.State) (out : X86Control.State) (marked : Nat)
    (initial : Array Intercept) (resolve : Intercept → Word) (portals : Nat → Option Portal)
    (frame : Frame s out) (stack : out.core.regs 4=s.regs 4)
    (pointer : s.regs 3=address marked) (bounded : marked<128)
    (catalog : Catalog s initial resolve portals) : Catalog out.core initial resolve portals := by
  intro i inside p listed
  exact entry_frame s out marked initial[i]! (resolve initial[i]!) p frame stack pointer bounded
    (catalog i inside p listed)

/-- A catalog entry at the actual selected index supplies all mapped-line and
arithmetic-read conditions; no post-selection memory image is supplied. -/
theorem inputs (s : X86Control.State) (initial work : Array Intercept) (seen : List Nat)
    (visits : Array Intercept) (resolve : Intercept → Word) (portals : Nat → Option Portal)
    (target sp : Word) (fraction : Int32) (j : Nat) (p : Portal)
    (history : History initial work seen visits)
    (selection : Selection initial work seen resolve target sp s fraction j)
    (catalog : Catalog s.core initial resolve portals) (listed : portals j=some p)
    (layout : Layout s.core work) (query : QuerySafe s.core) (globals : ClipGlobalsSafe s.core) :
    E1M1AimMapped.Inputs s.core work[j]! (resolve initial[j]!) p.front p.back p.ff p.fc p.bf p.bc ∧
    E1M1AimDistance.ReadSafe s.core ∧
    E1M1AimCeilingEntry.ClipSafe s.core (resolve initial[j]!) p.front p.back := by
  obtain ⟨kind,region,image,two⟩ := catalog j selection.inside p listed
  have record := E1M1AimCycleInvariant.record initial work seen visits resolve target sp s fraction j history selection
  have size := (E1M1SelectionHistory.image history).size
  have inside : j<work.size := by have := selection.inside; omega
  refine ⟨?_,E1M1AimNextLine.distance_reads s initial work seen visits resolve target sp fraction j
    history selection layout.recordsSafe query,E1M1AimNextLine.clip_safe s.core _ _ _ region globals⟩
  rw [selection.original]
  refine ⟨record,kind,?_,?_,(region _ (by simp)).1.1,?_,layout.helperSafe,
    E1M1AimMapFrame.map_safe s.core _ _ _ region,image⟩
  · rw [selection.argument]; exact (layout.recordsSafe j inside 4 (by simp)).1
  · rw [selection.argument]; exact (layout.recordsSafe j inside 8 (by simp)).1
  · exact two
end Doom.Proofs.E1M1AimCatalog
