import Doom.Proofs.E1M1AimLineDispatch
set_option backward.isDefEq.respectTransparency false
namespace Doom.Proofs.E1M1AimLineCoverage
open Verification X86 X86Memory Collision
open E1M1AimCatalog (Portal)
open E1M1HistoryDispatch (Selection)

/-- Every original line intercept is represented by a wall or a two-sided entry.
Actors are deliberately outside this coverage obligation. -/
def Coverage (initial : Array Intercept) (walls : Nat → Prop) (portals : Nat → Option Portal) : Prop :=
  ∀ i<initial.size, initial[i]!.isLine=true → walls i ∨ ∃ p, portals i=some p

/-- A reached selected line inherits coverage from its original buffer entry. -/
theorem selected (initial work : Array Intercept) (seen : List Nat) (resolve : Intercept → Word)
    (walls : Nat → Prop) (portals : Nat → Option Portal) (target sp : Word)
    (s : X86Control.State) (fraction : Int32) (j : Nat)
    (selection : Selection initial work seen resolve target sp s fraction j)
    (covered : Coverage initial walls portals) (isLine : (work[j]!).isLine=true) :
    walls j ∨ ∃ p, portals j=some p := by
  apply covered j selection.inside
  simpa only [selection.original] using isLine

/-- Shared source representation rules out contradictory wall/portal labels. -/
theorem exclusive (scene : Scene) (initial : Array Intercept) (walls : Nat → Prop)
    (portals : Nat → Option Portal) (j : Nat) (p : Portal) (inside : j<initial.size)
    (wallMap : E1M1AimWallCatalog.Represents scene initial walls)
    (portalMap : E1M1AimSourceCatalog.Represents scene initial portals)
    (wall : walls j) (listed : portals j=some p) : False := by
  have no := wallMap j inside wall
  have yes := (portalMap j inside p listed).2.2
  rw [no] at yes
  contradiction

end Doom.Proofs.E1M1AimLineCoverage
