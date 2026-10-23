import Doom.Proofs.E1M1AimRetryData
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimRetryGeometry
open Verification X86 X86Memory X86Control BlockSummary
open E1M1PathMapQuery (withStack)
attribute [local irreducible] load32 store32

/-- The second retry starts with the already-rightward angle in ECX. -/
def nextAngle (second : Bool) (angle : Angle) : Angle :=
  ⟨angle.raw+(if second then 0xf8000000 else 0x04000000)⟩

theorem angle_bits (second : Bool) (angle : Angle) :
    (nextAngle second angle).raw.toBitVec=
      angle.raw.toBitVec+(if second then 0xf8000000 else 0x04000000) := by
  cases second <;> rfl

def sampleReads (angle : Angle) : List Word :=
  [(0x13584#32),(angle.raw.toBitVec >>> 19 <<< 2)+0x7a84,(angle.raw.toBitVec >>> 19 <<< 2)+0x5a84]
def reads (s : X86Memory.State) (angle : Angle) : List Word :=
  OriginalAimSetup.actorReads s ++ [0x2c104,0x2c108] ++ sampleReads angle

/-- Only the samples used by the new angle must survive; their values follow
from the original full-table image, not an assumed reached ray result. -/
theorem samples (s t : X86Memory.State) (angle : Angle) (distance : Fixed)
    (tables : ThrustTables s.memory)
    (angleReg : t.regs 2=angle.raw.toBitVec) (rangeReg : t.regs 3=distance.raw.toBitVec)
    (stack : t.regs 4=s.regs 4)
    (kept : ∀ a∈sampleReads angle, load32 t.memory a=load32 s.memory a)
    (safe : ∀ a∈sampleReads angle, ∀ b∈OriginalAimQuery.saveWrites s, Apart a b) :
    E1M1AimGeometry.RaySamples t angle distance := by
  have values := thrust_selected_tables s.memory angle tables
  rw [tables.cosinePointer] at values
  refine ⟨angleReg,rangeReg,(kept _ (by simp [sampleReads])).trans tables.cosinePointer,
    (kept _ (by simp [sampleReads])).trans values.1,
    (kept _ (by simp [sampleReads])).trans values.2,?_⟩
  simpa only [OriginalAimQuery.saveWrites,stack,sampleReads] using safe

/-- Reconstruct all geometric inputs at another call with the same shooter and
stack, but a new angle/range. Static layout and actor guards are reused. -/
theorem geometry (s t : X86Memory.State) (thing : Collision.SolidThing)
    (oldAngle angle : Angle) (oldDistance distance ox oy : Fixed)
    (before : E1M1AimGeometry.Inputs s thing oldAngle oldDistance ox oy)
    (tables : ThrustTables s.memory)
    (actor : t.regs 0=s.regs 0) (stack : t.regs 4=s.regs 4)
    (angleReg : t.regs 2=angle.raw.toBitVec) (rangeReg : t.regs 3=distance.raw.toBitVec)
    (kept : ∀ a∈reads s angle, load32 t.memory a=load32 s.memory a)
    (sampleSafe : ∀ a∈sampleReads angle, ∀ b∈OriginalAimQuery.saveWrites s, Apart a b) :
    E1M1AimGeometry.Inputs t thing angle distance ox oy := by
  have actors (a : Word) (ha : a∈OriginalAimSetup.actorReads s) :=
    kept a (List.mem_append_left _ (List.mem_append_left _ ha))
  have origins (a : Word) (ha : a∈[(0x2c104#32),0x2c108]) :=
    kept a (List.mem_append_left _ (List.mem_append_right _ ha))
  refine ⟨samples s t angle distance tables angleReg rangeReg stack
    (fun a ha => kept a (List.mem_append_right _ ha)) sampleSafe,?_,?_,?_,?_,?_,
    (origins _ (by simp)).trans before.originX,(origins _ (by simp)).trans before.originY,
    E1M1AimRetryData.safe s t _ stack before.safeX,E1M1AimRetryData.safe s t _ stack before.safeY,?_,?_,?_⟩
  · rw [actor,actors _ (by simp [OriginalAimSetup.actorReads])]; exact before.x
  · rw [actor,actors _ (by simp [OriginalAimSetup.actorReads])]; exact before.y
  · rw [actor,actors _ (by simp [OriginalAimSetup.actorReads])]; exact before.z
  · rw [actor,actors _ (by simp [OriginalAimSetup.actorReads])]; exact before.height
  · intro a ha
    exact E1M1AimRetryData.safe s t a stack (before.actorSafe a (by
      simpa only [OriginalAimSetup.actorReads,actor] using ha))
  · simpa only [OriginalAimSetup.Separated,OriginalAimSetup.writes,withStack,write,ite_true,stack]
      using before.aimLayout
  · simpa only [OriginalPathInit.writes,withStack,write,ite_true,stack] using before.flagSafe
  · simpa only [OriginalPathInit.Separated,OriginalPathInit.writes,withStack,write,ite_true,stack]
      using before.pathLayout
end Doom.Proofs.E1M1AimRetryGeometry
