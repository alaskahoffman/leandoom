import Doom.Proofs.E1M1AimRetryInputs
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimStampImage
open Verification X86 X86Memory X86Control BlockSummary
open OriginalLineVisits (stamp Represents)
attribute [local irreducible] load32 store32

/-- Keep the original values of unvisited stamps, not merely their inequality
with the current epoch. The Boolean history records all actual visits. -/
structure Image (origin current : Memory) (lines epoch : Word) (seen : Array Bool) : Prop where
  counter : load32 current 0x13580=epoch
  stamps : ∀ j<seen.size, load32 current (stamp lines j)=
    if seen[j]! then epoch else load32 origin (stamp lines j)

def Fresh (m : Memory) (lines epoch : Word) (count : Nat) : Prop :=
  ∀ j<count, load32 m (stamp lines j)≠epoch

/-- An arbitrary represented starting history supplies its own original image. -/
theorem start (m : Memory) (lines epoch : Word) (seen : Array Bool)
    (represented : Represents m lines epoch seen) : Image m m lines epoch seen := by
  refine ⟨represented.1,?_⟩
  intro j hj
  by_cases yes : seen[j]! = true
  · rw [if_pos yes]; exact (represented.2 j hj).mpr yes
  · rw [if_neg yes]

/-- Pure preservation around a scan transports its strengthened image. -/
theorem transport (origin m n : Memory) (lines epoch : Word) (seen : Array Bool)
    (image : Image origin m lines epoch seen)
    (counter : load32 n 0x13580=load32 m 0x13580)
    (stamps : ∀ j<seen.size, load32 n (stamp lines j)=load32 m (stamp lines j)) :
    Image origin n lines epoch seen :=
  ⟨counter.trans image.counter,fun j hj => (stamps j hj).trans (image.stamps j hj)⟩

/-- Marked words use the current epoch; untouched words use their original
value. These are the two distinct obligations for freshness at a later epoch. -/
theorem fresh (origin current : Memory) (lines epoch future : Word) (seen : Array Bool)
    (image : Image origin current lines epoch seen) (different : epoch≠future)
    (before : Fresh origin lines future seen.size) : Fresh current lines future seen.size := by
  intro j hj
  rw [image.stamps j hj]
  split
  · exact different
  · exact before j hj

/-- Adjacent epochs differ even at unsigned wraparound. This alone says
nothing about whether an old, unvisited stamp equals the new epoch. -/
theorem successor_ne (epoch : Word) : epoch≠epoch+1 := by
  intro same
  have number := congrArg BitVec.toNat same
  simp only [BitVec.toNat_add] at number
  change epoch.toNat=(epoch.toNat+1)%2^32 at number
  have bound := BitVec.isLt epoch
  omega

theorem next_fresh (origin current : Memory) (lines epoch : Word) (seen : Array Bool)
    (image : Image origin current lines epoch seen)
    (before : Fresh origin lines (epoch+1) seen.size) :
    Fresh current lines (load32 current 0x13580+1) seen.size := by
  rw [image.counter]
  exact fresh origin current lines epoch (epoch+1) seen image (successor_ne epoch) before

/-- One sufficient entry condition is that every old stamp is at most the
current epoch, and the next increment does not wrap. Reachability of these
bounds is separate; we do not silently impose a non-wrapping machine model. -/
theorem bounded_fresh (m : Memory) (lines epoch : Word) (count : Nat)
    (bounded : ∀ j<count, (load32 m (stamp lines j)).toNat≤epoch.toNat)
    (noWrap : epoch.toNat<2^32-1) : Fresh m lines (epoch+1) count := by
  intro j hj same
  have old := bounded j hj
  have number := congrArg BitVec.toNat same
  simp only [BitVec.toNat_add] at number
  change (load32 m (stamp lines j)).toNat=(epoch.toNat+1)%2^32 at number
  omega

/-- After actual path initialization increments the epoch, the strengthened
image supplies the fresh all-false history required by the source traversal. -/
theorem restart (origin : Memory) (s : X86Memory.State) (lines epoch : Word) (seen : Array Bool)
    (ox oy sx sy ex ey : Fixed) (geometry : OriginalPathInit.Inputs s ox oy sx sy ex ey)
    (image : Image origin s.memory lines epoch seen)
    (before : Fresh origin lines (epoch+1) seen.size)
    (epochSafe : E1M1PathMapSetup.StackSafe (s.regs 4-60) 0x13580)
    (stampSafe : ∀ j<seen.size, E1M1PathMapSetup.Safe s (stamp lines j)) :
    Represents (E1M1PathMapSetup.grid s).core.memory lines (epoch+1)
      (Array.replicate seen.size false) := by
  have initialized := E1M1QueryInit.initial_visits s ox oy sx sy ex ey geometry lines seen.size
    epochSafe stampSafe (next_fresh origin s.memory lines epoch seen image before)
  simpa only [image.counter] using initialized
end Doom.Proofs.E1M1AimStampImage
