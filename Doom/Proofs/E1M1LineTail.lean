import Doom.Proofs.OriginalLineTail
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1LineTail
open Verification X86 X86Memory X86Control BlockSummary
abbrev boundary := E1M1LineSecondPoint.lineTest
abbrev program := OriginalLineTail.program

theorem contains_prior (pc : Nat) (h : E1M1LineSecondPoint.program pc≠none) :
    program pc=E1M1LineSecondPoint.program pc := by
  have a := E1M1LineFraction.contains_prior pc h
  have b : E1M1LineFraction.program pc≠none := by rw [a]; exact h
  exact (E1M1LineFinish.contains_prior pc b).trans a

theorem crossing_list_return_execution (gun : Fire.Gun) (s : X86Memory.State) (f : Option Flags)
    (c : Weapon.Context) (h : E1M1DischargeSetters.Inputs gun s c)
    (ox oy sx sy ex ey : Fixed)
    (geometry : OriginalPathInit.Inputs (E1M1AimSetup.firstTraversal gun s).core ox oy sx sy ex ey)
    (layout : OriginalAimSetup.Separated (E1M1AimQuery.firstRay gun s).core)
    (xout yout : Int32 × Fixed × Fixed)
    (okX : (Collision.pathStart ox oy sx sy ex ey).xStep=.ok xout)
    (okY : (Collision.pathStart ox oy sx sy ex ey).yStep=.ok yout)
    (atCrossing : (boundary gun s).pc=0x2c691)
    (trace : Collision.Divline) (line : Collision.Line) (frac : Fixed) (flags : Nat) (p v list : Word)
    (inputs : OriginalLineTail.Inputs (boundary gun s).core trace line frac flags p v)
    (tailLayout : OriginalLineTail.Layout (boundary gun s).core)
    (ret : load32 (boundary gun s).core.memory ((boundary gun s).core.regs 4+(36#32))=(0x2c578#32))
    (saved : load32 (boundary gun s).core.memory ((boundary gun s).core.regs 4+(24#32))=list)
    (savedSafe : OriginalLineTail.Protected (boundary gun s).core ((boundary gun s).core.regs 4+(24#32)))
    (keepGoing : frac.raw<0 ∨ (flags &&& 4 != 0 && frac.raw<65536 && line.back.isNone)=false)
    (count : Nat)
    (window : ∀ i<count, OriginalLineResume.SeenAt (boundary gun s).core.memory (list+BitVec.ofNat 32 (2*(i+1))))
    (windowSafe : ∀ i<count, ∀ a∈OriginalLineTail.seenReads (boundary gun s).core.memory
      (list+BitVec.ofNat 32 (2*(i+1))), OriginalLineTail.Protected (boundary gun s).core a)
    (last : load16 (boundary gun s).core.memory (list+BitVec.ofNat 32 (2*(count+1)))=(0xffff#16))
    (lastSafe : OriginalLineTail.Protected (boundary gun s).core (list+BitVec.ofNat 32 (2*(count+1)))) :
    ∃ steps≤656+10*count, X86CodeMemory.Prefix FloorCaller.cm program [] steps
      ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩
      (OriginalLineBounds.returned (OriginalLineCell.header
        (OriginalLineResume.skipMany count (OriginalLineTail.result (boundary gun s).core)).core).core) := by
  obtain ⟨n,hn,head⟩ := E1M1LineSecondPoint.line_test_execution gun s f c h
    ox oy sx sy ex ey geometry layout xout yout okX okY
  have head := head.transfer program [] contains_prior (by simp)
  obtain ⟨m,hm,tail⟩ := OriginalLineTail.through_sentinel (boundary gun s).core (boundary gun s).flags
    trace line frac flags p v list inputs tailLayout ret saved savedSafe keepGoing count window windowSafe last lastSafe
  rw [OriginalPathXStep.at_pc _ _ atCrossing] at tail
  exact ⟨n+m,by omega,E1M1PspriteStep.prefix_trans head (X86CodeMemory.lift_success tail FloorCaller.cm)⟩

end Doom.Proofs.E1M1LineTail
