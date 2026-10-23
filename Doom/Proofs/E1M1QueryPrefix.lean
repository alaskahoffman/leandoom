import Doom.Proofs.E1M1QueryImages
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1QueryPrefix
open Verification X86 X86Memory X86Control BlockSummary

private theorem extend {a b c : X86Routine.Program}
    (ab : ∀ pc, a pc≠none → b pc=a pc) (bc : ∀ pc, b pc≠none → c pc=b pc) :
    ∀ pc, a pc≠none → c pc=a pc := by
  intro pc h
  have eq := ab pc h
  exact (bc pc (by rw [eq]; exact h)).trans eq

/-- The setup uses the same authenticated program as the complete cell loop. -/
theorem contains_grid : ∀ pc, E1M1PathGridSetup.program pc≠none →
    E1M1FiringAdvance.program pc=E1M1PathGridSetup.program pc :=
  extend E1M1PathMapCaller.contains_grid
    (extend E1M1FiringScan.contains_firing
      (extend E1M1ThingEntry.contains_prior
        (extend E1M1FiringThings.contains_entry E1M1FiringAdvance.contains_prior)))

private theorem contains_init : ∀ pc, OriginalPathInit.program pc≠none →
    E1M1PathGridSetup.program pc=OriginalPathInit.program pc :=
  extend E1M1PathInit.contains_init (extend E1M1PathXStep.contains_prior
    (extend E1M1PathIntercept.contains_prior E1M1PathGridSetup.contains_prior))
private theorem contains_x : ∀ pc, OriginalPathXStep.program pc≠none →
    E1M1PathGridSetup.program pc=OriginalPathXStep.program pc :=
  extend E1M1PathXStep.contains_step
    (extend E1M1PathIntercept.contains_prior E1M1PathGridSetup.contains_prior)
private theorem contains_intercept : ∀ pc, OriginalPathIntercept.program pc≠none →
    E1M1PathGridSetup.program pc=OriginalPathIntercept.program pc :=
  extend E1M1PathIntercept.contains_intercept E1M1PathGridSetup.contains_prior

/-- Continuous original P_PathTraverse initialization, with helper safety
obtained from the successful production axis calculations. -/
theorem execution (s : X86Memory.State) (f : Option Flags) (ox oy sx sy ex ey : Fixed)
    (geometry : OriginalPathInit.Inputs s ox oy sx sy ex ey)
    (xout yout : Int32 × Fixed × Fixed)
    (okX : (Collision.pathStart ox oy sx sy ex ey).xStep=.ok xout)
    (okY : (Collision.pathStart ox oy sx sy ex ey).yStep=.ok yout) :
    ∃ n≤175, X86CodeMemory.Prefix FloorCaller.cm E1M1FiringAdvance.program [] n
      ⟨s,f,0x2c8a0⟩ (E1M1PathMapSetup.grid s) := by
  let i := OriginalPathInit.result s
  let x := OriginalPathXStep.result i.core
  let t := OriginalPathIntercept.result x.core
  have safeX := (OriginalPathXStep.live i.core _ xout
    (E1M1PathXStep.inputs_from_init s ox oy sx sy ex ey geometry) okX).1
  have safeY := (E1M1PathGridSetup.grid_observation_from_init s ox oy sx sy ex ey geometry xout yout okX okY).1
  obtain ⟨a,ha,init⟩ := OriginalPathInit.execution s f
  have init := init.transfer E1M1PathGridSetup.program [] contains_init (by simp)
  obtain ⟨b,hb,xrun⟩ := OriginalPathXStep.execution i.core i.flags safeX
  have xrun := xrun.transfer E1M1PathGridSetup.program [] contains_x (by simp)
  have irun := (OriginalPathIntercept.execution x.core x.flags).transfer
    E1M1PathGridSetup.program [] contains_intercept (by simp)
  rw [OriginalPathXStep.at_pc _ _ (OriginalPathXStep.result_pc i.core)] at irun
  obtain ⟨c,hc,yrun⟩ := E1M1PathGridSetup.after_execution t.core safeY
  have seam : (⟨t.core,OriginalPathYStep.comparison t.core,0x2ca10⟩ : X86Control.State)=t := rfl
  rw [seam] at yrun
  have run := OriginalGroupBounds.prefix_join
    (OriginalGroupBounds.prefix_join (OriginalGroupBounds.prefix_join init xrun) irun) yrun
  exact ⟨a+b+19+c,by omega,
    (X86CodeMemory.lift_success run FloorCaller.cm).transfer _ [] contains_grid (by simp)⟩
end Doom.Proofs.E1M1QueryPrefix
