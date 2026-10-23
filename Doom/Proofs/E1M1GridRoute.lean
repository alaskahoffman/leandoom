import Doom.Proofs.E1M1LoggedWalk
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1GridRoute
open Verification X86
open E1M1CellWalkInvariant (Cell)
open E1M1PathAdvance (step nextPc ended)
open E1M1CellWalk (Follows stopPc)

/-- Metadata supplies memory contracts, never the coordinates of the walk. -/
def selected (pick : Int32 → Int32 → Cell) (g : E1M1PathAdvance.Cell) : Cell :=
  { pick (Int32.ofBitVec g.mapX) (Int32.ofBitVec g.mapY) with
    x := Int32.ofBitVec g.mapX, y := Int32.ofBitVec g.mapY }

/-- Generate the numeric route using the original controller's continuation PC. -/
def route (pick : Int32 → Int32 → Cell) : Nat → E1M1PathAdvance.Cell → List Cell
  | 0,_ => []
  | fuel+1,g => selected pick g ::
      if nextPc g=0x2ca7f then route pick fuel (step g) else []

/-- The source controller checks the endpoint after collecting a cell and otherwise
uses its remaining iteration budget. No machine PC appears in this definition. -/
def sourceRoute (pick : Int32 → Int32 → Cell) : Nat → E1M1PathAdvance.Cell → List Cell
  | 0,_ => []
  | fuel+1,g => selected pick g ::
      if ended g then [] else sourceRoute pick fuel (step g)

/-- Every generated coordinate and continuation is justified by the numeric state. -/
theorem follows (pick : Int32 → Int32 → Cell) (fuel : Nat) (g : E1M1PathAdvance.Cell) :
    Follows g (route pick fuel g) := by
  induction fuel generalizing g with
  | zero => trivial
  | succ fuel ih =>
    simp only [route,Follows,selected,Int32.toBitVec_ofBitVec]
    split <;> simp_all [Follows]

/-- A legal remaining budget always includes its current cell. -/
theorem nonempty (pick : Int32 → Int32 → Cell) (fuel : Nat) (g : E1M1PathAdvance.Cell) :
    route pick (fuel+1) g≠[] := by simp [route]

/-- The route cannot exceed its supplied budget, including numerical stalls. -/
theorem length_bound (pick : Int32 → Int32 → Cell) (fuel : Nat) (g : E1M1PathAdvance.Cell) :
    (route pick fuel g).length≤fuel := by
  induction fuel generalizing g with
  | zero => simp [route]
  | succ fuel ih =>
    simp only [route,List.length_cons]
    split <;> simp_all

/-- Legal machine counters give exactly the source endpoint/budget itinerary. -/
theorem source_eq (pick : Int32 → Int32 → Cell) (fuel n : Nat)
    (g : E1M1PathAdvance.Cell) (legal : n<64) (remaining : fuel=64-n)
    (counter : g.count=BitVec.ofNat 32 n) :
    route pick fuel g=sourceRoute pick fuel g := by
  induction fuel generalizing g n with
  | zero => omega
  | succ fuel ih =>
    simp only [route,sourceRoute]
    by_cases go : nextPc g=0x2ca7f
    · have cont := E1M1CellWalkLimit.continuation g n legal counter go
      rw [if_pos go,cont.1]
      simp only [Bool.false_eq_true,ite_false]
      rw [ih (n+1) (step g) cont.2.1 (by omega) cont.2.2]
    · rw [if_neg go]
      cases endpoint : ended g with
      | true => simp
      | false =>
        have last : n+1≥64 := by
          have no : ¬(g.count+(1#32)).toInt<64 := by
            simpa [nextPc,endpoint] using go
          rw [counter,E1M1PathAdvance.counter_limit n legal] at no
          omega
        have zero : fuel=0 := by omega
        simp [zero,sourceRoute]

/-- Generating all remaining iterations exits the DOS loop, even when the endpoint
is reached early. This is not merely a prefix with a chosen stopping point. -/
theorem exits (pick : Int32 → Int32 → Cell) (fuel n pc : Nat)
    (g : E1M1PathAdvance.Cell) (legal : n<64) (remaining : fuel=64-n)
    (counter : g.count=BitVec.ofNat 32 n) :
    stopPc pc g (route pick fuel g)=0x2cafd := by
  induction fuel generalizing g n pc with
  | zero => omega
  | succ fuel ih =>
    simp only [route,stopPc]
    by_cases go : nextPc g=0x2ca7f
    · rw [if_pos go]
      have cont := E1M1CellWalkLimit.continuation g n legal counter go
      exact ih (n+1) (nextPc g) (step g) cont.2.1 (by omega) cont.2.2
    · rw [if_neg go]
      change nextPc g=0x2cafd
      unfold nextPc at go ⊢
      split <;> simp_all
end Doom.Proofs.E1M1GridRoute
