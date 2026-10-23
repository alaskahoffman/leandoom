import Doom.Proofs.E1M1AimControllerExit
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimThirdRequest
open Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1AimStampImage (Image Fresh)
open E1M1AimStampQuery (stampWords)
attribute [local irreducible] load32 store32

/-- Two increments cannot reproduce a 32-bit epoch, including across wrap. -/
theorem two_ahead_ne (epoch : Word) : epoch≠(epoch+1)+1 := by
  intro same
  have number := congrArg BitVec.toNat same
  rw [BitVec.add_assoc] at number
  change epoch.toNat=(epoch.toNat+2)%2^32 at number
  have bound := BitVec.isLt epoch
  omega

/-- Retain old values through two actual marking histories. Freshness for the
third epoch comes from original words, not an assumption at the second return. -/
theorem consecutive_fresh (origin middle current : Memory) (lines epoch : Word)
    (first second : Array Bool) (count : Nat) (firstSize : first.size=count) (secondSize : second.size=count)
    (firstImage : Image origin middle lines epoch first)
    (secondImage : Image middle current lines (epoch+1) second)
    (before : Fresh origin lines ((epoch+1)+1) count) :
    Fresh current lines ((epoch+1)+1) count := by
  have middleFresh := E1M1AimStampImage.fresh origin middle lines epoch ((epoch+1)+1) first
    firstImage (two_ahead_ne epoch) (by simpa only [firstSize] using before)
  have currentFresh := E1M1AimStampImage.fresh middle current lines (epoch+1) ((epoch+1)+1) second
    secondImage (E1M1AimStampImage.successor_ne (epoch+1))
    (by simpa only [firstSize,secondSize] using middleFresh)
  simpa only [secondSize] using currentFresh

/-- Caller slope/return stores preserve the exact query image under the explicit
word-separation guards. The old memory used for unvisited stamps is unchanged. -/
theorem retry_image (second : Bool) (origin : Memory) (out : X86Control.State)
    (lines epoch : Word) (seen : Array Bool) (count : Nat) (size : seen.size=count)
    (image : Image origin out.core.memory lines epoch seen)
    (safe : ∀ a∈stampWords lines count, Apart a 0x2c0c0 ∧ Apart a (out.core.regs 4-4)) :
    Image origin (E1M1BulletAim.nextQuery second out.core).core.memory lines epoch seen :=
  E1M1AimStampQuery.transport origin out.core.memory _ lines epoch seen count size image
    (fun a ha => E1M1AimRetryRequest.frame second out.core a (safe a ha).1 (safe a ha).2)

/-- The same two caller stores preserve freshness already obtained from exact
histories. There is no assumption that unvisited stamps were reset to zero. -/
theorem retry_fresh (second : Bool) (out : X86Control.State) (lines future : Word) (count : Nat)
    (fresh : Fresh out.core.memory lines future count)
    (safe : ∀ a∈stampWords lines count, Apart a 0x2c0c0 ∧ Apart a (out.core.regs 4-4)) :
    Fresh (E1M1BulletAim.nextQuery second out.core).core.memory lines future count := by
  intro j hj
  have member : OriginalLineVisits.stamp lines j∈stampWords lines count := by
    simp only [stampWords,List.mem_cons,List.mem_map,List.mem_range]
    exact Or.inr ⟨j,hj,rfl⟩
  rw [E1M1AimRetryRequest.frame second out.core _ (safe _ member).1 (safe _ member).2]
  exact fresh j hj

/-- Compose the two real requests. The third ray is left of the ORIGINAL angle,
not left of an already-updated angle by another 1/64 turn. All arithmetic wraps. -/
theorem arguments (s : X86Memory.State) (right third : X86Control.State) (angle : Angle)
    (first : E1M1AimRetryRequest.Request false s right)
    (second : E1M1AimRetryRequest.Request true right.core third)
    (controller : s.regs 6=s.regs 0 ∧ s.regs 1=angle.raw.toBitVec) :
    third.pc=0x2bb80 ∧ third.core.regs 4=s.regs 4 ∧ third.core.regs 0=s.regs 0 ∧
    third.core.regs 2=(angle.raw+0xfc000000).toBitVec ∧ third.core.regs 3=0x04000000 ∧
    load32 third.core.memory (third.core.regs 4)=0x2d819 := by
  refine ⟨second.pc,second.stack.trans first.stack,
    second.actor.trans (first.savedActor.trans controller.1),?_,second.range,second.returnWord⟩
  rw [second.angle,first.savedAngle,controller.2]
  exact E1M1BulletAim.retry_angles angle.raw
end Doom.Proofs.E1M1AimThirdRequest
