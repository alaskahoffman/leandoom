import Doom.Proofs.OriginalLineCrossing
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1LineCrossing
open Verification X86 X86Memory X86Control BlockSummary
abbrev boundary := E1M1LineCell.firstCell
abbrev program := OriginalLineCrossing.program

theorem contains_cell (pc : Nat) (h : E1M1LineCell.program pc≠none) :
    program pc=E1M1LineCell.program pc := by
  have e0 := E1M1LineInterceptEntry.contains_prior pc h
  have h0 : E1M1LineInterceptEntry.program pc≠none := by rw [e0]; exact h
  have e1 := E1M1LineSide.contains_prior pc h0
  have h1 : E1M1LineSide.program pc≠none := by rw [e1]; exact h0
  have e2 := E1M1DivlineSide.contains_prior pc h1
  have h2 : E1M1DivlineSide.program pc≠none := by rw [e2]; exact h1
  have e3 := E1M1LineSecondPoint.contains_prior pc h2
  have h3 : E1M1LineSecondPoint.program pc≠none := by rw [e3]; exact h2
  exact ((((OriginalLineCrossing.contains_tests pc h3).trans e3).trans e2).trans e1).trans e0

theorem callback_execution (gun : Fire.Gun) (s : X86Memory.State) (f : Option Flags)
    (c : Weapon.Context) (h : E1M1DischargeSetters.Inputs gun s c)
    (ox oy sx sy ex ey : Fixed)
    (geometry : OriginalPathInit.Inputs (E1M1AimSetup.firstTraversal gun s).core ox oy sx sy ex ey)
    (layout : OriginalAimSetup.Separated (E1M1AimQuery.firstRay gun s).core)
    (xout yout : Int32 × Fixed × Fixed)
    (okX : (Collision.pathStart ox oy sx sy ex ey).xStep=.ok xout)
    (okY : (Collision.pathStart ox oy sx sy ex ey).yStep=.ok yout)
    (entry : (boundary gun s).pc=0x2c5f0)
    (trace : Collision.Divline) (line : Collision.Line) (p v w : Word)
    (inputs : OriginalLineCrossing.Inputs (boundary gun s).core trace line p v w)
    (frac : Fixed) (flags : Nat)
    (data : OriginalLineCrossing.TailData (boundary gun s).core trace line frac flags p v) :
    ∃ steps≤649, X86CodeMemory.Prefix FloorCaller.cm program [] steps
      ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ (OriginalLineCrossing.result (boundary gun s).core) := by
  obtain ⟨n,hn,a⟩ := E1M1LineCell.first_cell_execution gun s f c h
    ox oy sx sy ex ey geometry layout xout yout okX okY
  have a := a.transfer program [] contains_cell (by simp)
  obtain ⟨m,hm,b⟩ := OriginalLineCrossing.execution (boundary gun s).core trace line p v w inputs frac flags data (boundary gun s).flags
  rw [OriginalPathXStep.at_pc _ _ entry] at b
  exact ⟨n+m,by omega,E1M1PspriteStep.prefix_trans a (X86CodeMemory.lift_success b FloorCaller.cm)⟩

end Doom.Proofs.E1M1LineCrossing
