import Doom.Proofs.E1M1AimBlockingCycle
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
namespace Doom.Proofs.E1M1AimWallCatalog
open Verification X86 X86Memory X86Control BlockSummary Collision E1M1SelectionHistory
open E1M1MinimumScan (address)
open E1M1HistoryDispatch (Selection)
open E1M1AimHistoryCycle (Frame)
open E1M1AimMapFrame (StableWord)
attribute [local irreducible] load32 store32

/-- A partial wall catalog needs only the flags byte, not a fictitious back sector. -/
def Catalog (s : X86Memory.State) (initial : Array Intercept)
    (resolve : Intercept → Word) (walls : Nat → Prop) : Prop :=
  ∀ i<initial.size, walls i → initial[i]!.isLine=true ∧
    StableWord s (resolve initial[i]!+16) ∧ s.memory (resolve initial[i]!+16) &&& (4#8)=0

def Represents (scene : Scene) (initial : Array Intercept) (walls : Nat → Prop) : Prop :=
  ∀ i<initial.size, walls i → scene.lines[initial[i]!.id]!.twoSided=false

/-- Every listed wall's flag survives a continuing callback, the sentinel mark,
minimum scan and next CALL. Only the original catalog is supplied. -/
theorem preserved (s : X86Memory.State) (out : X86Control.State) (marked : Nat)
    (initial : Array Intercept) (resolve : Intercept → Word) (walls : Nat → Prop)
    (frame : Frame s out) (stack : out.core.regs 4=s.regs 4)
    (pointer : s.regs 3=address marked) (bounded : marked<128)
    (catalog : Catalog s initial resolve walls) : Catalog out.core initial resolve walls := by
  intro i inside listed
  obtain ⟨kind,safe,flags⟩ := catalog i inside listed
  exact ⟨kind,E1M1AimMapFrame.stable_word s out.core _ stack safe,
    by rw [E1M1AimMapFrame.byte s out marked _ frame pointer bounded safe]; exact flags⟩

/-- Discharge the wall branch's map and flag premises at the actual selected hit. -/
theorem inputs (scene : Scene) (initial work : Array Intercept) (seen : List Nat)
    (resolve : Intercept → Word) (walls : Nat → Prop) (target sp : Word)
    (s : X86Control.State) (fraction : Int32) (j : Nat)
    (selection : Selection initial work seen resolve target sp s fraction j)
    (catalog : Catalog s.core initial resolve walls) (represented : Represents scene initial walls)
    (listed : walls j) :
    (work[j]!).isLine=true ∧ E1M1AimWall.Safe (s.core.regs 4) (resolve initial[j]!+16) ∧
    (s.core.memory (resolve initial[j]!+16) &&& (4#8) != 0)=scene.lines[work[j]!.id]!.twoSided ∧
    scene.lines[work[j]!.id]!.twoSided=false := by
  obtain ⟨kind,safe,flags⟩ := catalog j selection.inside listed
  have solid := represented j selection.inside listed
  rw [selection.original]
  exact ⟨kind,safe.1.1,by simpa [solid] using flags,solid⟩

end Doom.Proofs.E1M1AimWallCatalog
