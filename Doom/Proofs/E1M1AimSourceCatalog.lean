import Doom.Proofs.E1M1AimPathBridge
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1AimSourceCatalog
open Verification X86 X86Memory Collision E1M1SelectionHistory
open E1M1HistoryDispatch (Selection)
open E1M1AimCatalog (Portal)
open E1M1AimIteration
open E1M1AimLineJoin (bits_eq floor_word ceiling_word bottom_word top_word)

def front (p : Portal) : Heights := ⟨⟨Int32.ofBitVec p.ff⟩,⟨Int32.ofBitVec p.fc⟩⟩
def back (p : Portal) : Heights := ⟨⟨Int32.ofBitVec p.bf⟩,⟨Int32.ofBitVec p.bc⟩⟩

/-- The immutable source scene and the machine catalog describe the same
represented lines. Unlisted intercepts remain unclassified. -/
def Represents (scene : Scene) (initial : Array Intercept) (portals : Nat → Option Portal) : Prop :=
  ∀ i<initial.size, ∀ p, portals i=some p →
    scene.lines[initial[i]!.id]!.front=front p ∧
    scene.lines[initial[i]!.id]!.back=some (back p) ∧
    scene.lines[initial[i]!.id]!.twoSided=true

/-- The source map facts follow for the reached, unmarked selected record. -/
theorem entry (scene : Scene) (initial work : Array Intercept) (seen : List Nat)
    (resolve : Intercept → Word) (portals : Nat → Option Portal)
    (target sp : Word) (s : X86Control.State) (fraction : Int32) (j : Nat) (p : Portal)
    (selection : Selection initial work seen resolve target sp s fraction j)
    (represented : Represents scene initial portals) (listed : portals j=some p) :
    scene.lines[work[j]!.id]!.front=front p ∧
    scene.lines[work[j]!.id]!.back=some (back p) ∧
    scene.lines[work[j]!.id]!.twoSided=true := by
  rw [selection.original]
  exact represented j selection.inside p listed

/-- Translate the source branch and divisions to the existing binary callback
contract, preserving signed max/min and height-dependent division guards. -/
theorem arithmetic (p : Portal) (distance z : Fixed) (hit : Intercept)
    (lower upper floorSlope ceilingSlope : Fixed)
    (pass : max (front p).floor.raw (back p).floor.raw <
      min (front p).ceiling.raw (back p).ceiling.raw)
    (floorOk : (front p).floor≠(back p).floor →
      checkedPathDiv (⟨max (front p).floor.raw (back p).floor.raw⟩-z)
        (distance*hit.frac)=.ok floorSlope)
    (ceilingOk : (front p).ceiling≠(back p).ceiling →
      checkedPathDiv (⟨min (front p).ceiling.raw (back p).ceiling.raw⟩-z)
        (distance*hit.frac)=.ok ceilingSlope) :
    (if p.ff.toInt≤p.bf.toInt then p.bf else p.ff).toInt <
      (if p.bc.toInt≤p.fc.toInt then p.bc else p.fc).toInt ∧
    (p.bf≠p.ff → checkedPathDiv (⟨Int32.ofBitVec (if p.ff.toInt≤p.bf.toInt then p.bf else p.ff)⟩-z)
      (distance*hit.frac)=.ok floorSlope) ∧
    (p.fc≠p.bc → checkedPathDiv (⟨Int32.ofBitVec (if p.bc.toInt≤p.fc.toInt then p.bc else p.fc)⟩-z)
      (distance*hit.frac)=.ok ceilingSlope) ∧
    (if p.bf=p.ff then lower.raw else max lower.raw floorSlope.raw)=
      (bottomAfter (front p) (back p) lower floorSlope).raw ∧
    (if p.fc=p.bc then upper.raw else min upper.raw ceilingSlope.raw)=
      (topAfter (front p) (back p) upper ceilingSlope).raw := by
  have floorBits := floor_word (front p).floor (back p).floor
  have ceilingBits := ceiling_word (front p).ceiling (back p).ceiling
  have bottomBits := bottom_word (front p) (back p) lower floorSlope
  have topBits := top_word (front p) (back p) upper ceilingSlope
  simp only [front,back,Int32.toBitVec_ofBitVec] at floorBits ceilingBits bottomBits topBits
  refine ⟨?_,?_,?_,bottomBits,topBits⟩
  · have bounds := E1M1AimPortalSource.signed_bounds (front p).floor (front p).ceiling
      (back p).floor (back p).ceiling
    simp only [Int32.lt_iff_toInt_lt,Int32.le_iff_toInt_le] at pass bounds
    simp only [front,back,Int32.toBitVec_ofBitVec] at bounds pass
    omega
  · rw [floorBits]
    intro different
    apply floorOk
    intro equal
    have eq := congrArg (fun a : Fixed => a.raw.toBitVec) equal
    simp only [front,back,Int32.toBitVec_ofBitVec] at eq
    exact different eq.symm
  · rw [ceilingBits]
    intro different
    apply ceilingOk
    intro equal
    have eq := congrArg (fun a : Fixed => a.raw.toBitVec) equal
    simp only [front,back,Int32.toBitVec_ofBitVec] at eq
    exact different eq

end Doom.Proofs.E1M1AimSourceCatalog
