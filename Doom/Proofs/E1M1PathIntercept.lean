import Doom.Proofs.E1M1PathXStep
import Doom.Proofs.PathXStepFrame
import Doom.Proofs.OriginalPathIntercept
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1PathIntercept
open Verification X86 X86Memory X86Control BlockSummary

def program (pc : Nat) : Option (X86Routine.Op × Nat) :=
  match E1M1PathXStep.program pc with
  | some op => some op
  | none => OriginalPathIntercept.program pc

theorem contains_prior (pc : Nat) (h : E1M1PathXStep.program pc≠none) :
    program pc=E1M1PathXStep.program pc := by
  unfold program
  cases hp : E1M1PathXStep.program pc <;> simp_all

theorem contains_intercept (pc : Nat) (h : OriginalPathIntercept.program pc≠none) :
    program pc=OriginalPathIntercept.program pc := by
  have range : 0x2c9d3≤pc ∧ pc<0x2ca10 := by
    by_cases r : 0x2c9d3≤pc ∧ pc<0x2ca10
    · exact r
    · simp [OriginalPathIntercept.program,OriginalPathIntercept.bytesProgram,r] at h
  have all : ∀ i : Fin 61, E1M1PathXStep.program (0x2c9d3+i.val)=none := by decide
  have eq : 0x2c9d3+(pc-0x2c9d3)=pc := by omega
  have absent : E1M1PathXStep.program pc=none := by
    simpa only [eq] using all ⟨pc-0x2c9d3,by omega⟩
  simp [program,absent]

def firstIntercept (gun : Fire.Gun) (s : X86Memory.State) :=
  OriginalPathIntercept.result (E1M1PathXStep.firstXStep gun s).core

theorem first_intercept_execution (gun : Fire.Gun) (s : X86Memory.State) (f : Option Flags)
    (c : Weapon.Context) (h : E1M1DischargeSetters.Inputs gun s c)
    (safe : OriginalPathXStep.Safe (E1M1PathInit.firstPath gun s).core) :
    ∃ n, n≤287 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n
      ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ (firstIntercept gun s) := by
  obtain ⟨n,hn,a⟩ := E1M1PathXStep.first_xstep_execution gun s f c h safe
  have a := a.transfer program [] contains_prior (by simp)
  have b := OriginalPathIntercept.execution (E1M1PathXStep.firstXStep gun s).core
    (E1M1PathXStep.firstXStep gun s).flags
  have b := (X86CodeMemory.lift_success b FloorCaller.cm).transfer program [] contains_intercept (by simp)
  have pc : (E1M1PathXStep.firstXStep gun s).pc=0x2c9d3 := OriginalPathXStep.result_pc _
  rw [OriginalPathXStep.at_pc _ _ pc] at b
  exact ⟨n+19,by omega,E1M1PspriteStep.prefix_trans a b⟩

/-- The previous initialization and X-step proof supply every input. No fresh
coordinate or stack assumption is inserted between the executable blocks. -/
theorem inputs_from_xstep (s : X86Memory.State) (ox oy sx sy ex ey : Fixed)
    (h : OriginalPathInit.Inputs s ox oy sx sy ex ey)
    (out : Int32 × Fixed × Fixed) (ok : (Collision.pathStart ox oy sx sy ex ey).xStep=.ok out) :
    OriginalPathIntercept.Inputs (OriginalPathXStep.result (OriginalPathInit.result s).core).core
      (Collision.pathStart ox oy sx sy ex ey) out.2.1 out.2.2 := by
  have ready := OriginalPathInit.ready s ox oy sx sy ex ey h
  have matched := (OriginalPathXStep.live _ _ out (E1M1PathXStep.inputs_from_init _ _ _ _ _ _ _ h) ok).2
  have values : (OriginalPathXStep.result (OriginalPathInit.result s).core).core.regs 3=out.2.1.raw.toBitVec ∧
      (OriginalPathXStep.result (OriginalPathInit.result s).core).core.regs 0=out.2.2.raw.toBitVec := by
    exact ⟨congrArg (fun v => v.2.1) matched,congrArg (fun v => v.2.2) matched⟩
  constructor
  · rw [PathXStepFrame.registers _ 6 (by simp)]
    exact congrArg (fun v => v.1) ready.relative
  · rw [PathXStepFrame.registers _ 7 (by simp)]
    exact congrArg (fun v => v.2.1) ready.relative
  · rw [PathXStepFrame.registers _ 5 (by simp)]
    exact congrArg (fun v => v.2.2.1) ready.relative
  · rw [PathXStepFrame.registers _ 1 (by simp)]
    exact congrArg (fun v => v.2.2.2) ready.relative
  · exact values.1
  · exact values.2
  · rw [PathXStepFrame.stack,PathXStepFrame.local_preserved _ _ (by simp),ready.stack]
    have addr : s.regs 4-60+(16#32)=s.regs 4-44 := by simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rw [addr]
    exact congrArg (fun v => v.2.1) ready.blocks
  · rw [PathXStepFrame.stack,PathXStepFrame.local_preserved _ _ (by simp),ready.stack]
    have addr : s.regs 4-60+(24#32)=s.regs 4-36 := by simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rw [addr]
    exact congrArg (fun v => v.2.2.2) ready.blocks

/-- Continuous firing execution through the first crossing, together with the
live fixed-point result and all operands for the following Y-axis comparison. -/
theorem first_intercept_correspondence (gun : Fire.Gun) (s : X86Memory.State) (f : Option Flags)
    (c : Weapon.Context) (h : E1M1DischargeSetters.Inputs gun s c)
    (ox oy sx sy ex ey : Fixed)
    (geometry : OriginalPathInit.Inputs (E1M1AimSetup.firstTraversal gun s).core ox oy sx sy ex ey)
    (out : Int32 × Fixed × Fixed) (ok : (Collision.pathStart ox oy sx sy ex ey).xStep=.ok out) :
    ∃ n, n≤287 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n
      ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ (firstIntercept gun s) ∧
    OriginalPathIntercept.Ready (E1M1PathXStep.firstXStep gun s).core (firstIntercept gun s)
      (Collision.pathStart ox oy sx sy ex ey) out.2.1 out.2.2 := by
  have inputs := inputs_from_xstep _ ox oy sx sy ex ey geometry out ok
  have safe := (OriginalPathXStep.live (E1M1PathInit.firstPath gun s).core _ out
    (E1M1PathXStep.inputs_from_init _ _ _ _ _ _ _ geometry) ok).1
  obtain ⟨n,hn,path⟩ := first_intercept_execution gun s f c h safe
  exact ⟨n,hn,path,OriginalPathIntercept.live _ _ _ _ inputs⟩
end Doom.Proofs.E1M1PathIntercept
