import Doom.Proofs.E1M1LineFinish
import Doom.Proofs.OriginalLineResume
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1LineResume
open Verification X86 X86Memory X86Control BlockSummary
abbrev program := E1M1LineFinish.program

theorem contains_resume (pc : Nat) (h : OriginalLineResume.program pc≠none) :
    program pc=OriginalLineResume.program pc := by
  by_cases inside : 0x2c520≤pc ∧ pc<0x2c591
  · have all : ∀ i : Fin 113, program (0x2c520+i.val)=OriginalLineResume.program (0x2c520+i.val) := by decide
    have eq : 0x2c520+(pc-0x2c520)=pc := by omega
    simpa only [eq] using all ⟨pc-0x2c520,by omega⟩
  have a : ¬(0x2c541≤pc ∧ pc<0x2c587) := by omega
  have b : ¬(0x2c520≤pc ∧ pc<0x2c541) := by omega
  have c : ¬(0x2c587≤pc ∧ pc<0x2c591) := by omega
  simp [OriginalLineResume.program,OriginalLineCell.program,OriginalLineCell.bytesProgram,
    OriginalLineBounds.program,OriginalLineBounds.bytesProgram,a,b,c] at h

def continueIterator (s : X86Control.State) : X86Control.State :=
  if s.pc=0x2c578 then OriginalLineResume.result s.core
  else if s.pc=0x2c587 then OriginalLineBounds.returned s.core else s

theorem continue_execution (s : X86Control.State) :
    ∃ n≤5, X86Routine.Prefix program [] n s (continueIterator s) := by
  by_cases atReturn : s.pc=0x2c578
  · obtain ⟨n,hn,hp⟩ := OriginalLineResume.execution s.core s.flags
    rw [OriginalPathXStep.at_pc _ _ atReturn] at hp
    exact ⟨n,hn,by simpa only [continueIterator,if_pos atReturn] using hp.transfer program [] contains_resume (by simp)⟩
  · by_cases atEnd : s.pc=0x2c587
    · have hp := (OriginalLineBounds.return_execution s.core s.flags).transfer OriginalLineResume.program [] OriginalLineResume.contains_bounds (by simp)
      rw [OriginalPathXStep.at_pc _ _ atEnd] at hp
      exact ⟨4,by omega,by simpa only [continueIterator,if_neg atReturn,if_pos atEnd] using hp.transfer program [] contains_resume (by simp)⟩
    · exact ⟨0,by omega,by simpa only [continueIterator,if_neg atReturn,if_neg atEnd] using X86Routine.Prefix.nil (program:=program) (exits:=[]) s⟩

def resumed (gun : Fire.Gun) (s : X86Memory.State) := continueIterator (E1M1LineFinish.finish gun s)

theorem line_resume_execution (gun : Fire.Gun) (s : X86Memory.State) (f : Option Flags)
    (c : Weapon.Context) (h : E1M1DischargeSetters.Inputs gun s c)
    (ox oy sx sy ex ey : Fixed)
    (geometry : OriginalPathInit.Inputs (E1M1AimSetup.firstTraversal gun s).core ox oy sx sy ex ey)
    (layout : OriginalAimSetup.Separated (E1M1AimQuery.firstRay gun s).core)
    (xout yout : Int32 × Fixed × Fixed)
    (okX : (Collision.pathStart ox oy sx sy ex ey).xStep=.ok xout)
    (okY : (Collision.pathStart ox oy sx sy ex ey).yStep=.ok yout)
    (safe : E1M1LineFraction.Ready (E1M1LineSecondPoint.lineTest gun s)) :
    ∃ n≤649, X86CodeMemory.Prefix FloorCaller.cm program [] n
      ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ (resumed gun s) := by
  obtain ⟨n,hn,a⟩ := E1M1LineFinish.line_finish_execution gun s f c h
    ox oy sx sy ex ey geometry layout xout yout okX okY safe
  obtain ⟨m,hm,b⟩ := continue_execution (E1M1LineFinish.finish gun s)
  exact ⟨n+m,by omega,E1M1PspriteStep.prefix_trans a (X86CodeMemory.lift_success b FloorCaller.cm)⟩

/-- Any finite run of duplicate skips composes into the same firing program. -/
theorem duplicate_run (n : Nat) (s : X86Control.State) (atHeader : s.pc=0x2c57f)
    (seen : OriginalLineResume.Duplicates n s) :
    ∃ steps≤10*n, X86Routine.Prefix program [] steps s (OriginalLineResume.skipMany n s) := by
  obtain ⟨m,hm,hp⟩ := OriginalLineResume.skip_execution n s atHeader seen
  exact ⟨m,hm,hp.transfer program [] contains_resume (by simp)⟩
theorem line_list_return_execution (gun : Fire.Gun) (s : X86Memory.State) (f : Option Flags)
    (c : Weapon.Context) (h : E1M1DischargeSetters.Inputs gun s c)
    (ox oy sx sy ex ey : Fixed)
    (geometry : OriginalPathInit.Inputs (E1M1AimSetup.firstTraversal gun s).core ox oy sx sy ex ey)
    (layout : OriginalAimSetup.Separated (E1M1AimQuery.firstRay gun s).core)
    (xout yout : Int32 × Fixed × Fixed)
    (okX : (Collision.pathStart ox oy sx sy ex ey).xStep=.ok xout)
    (okY : (Collision.pathStart ox oy sx sy ex ey).yStep=.ok yout)
    (safe : E1M1LineFraction.Ready (E1M1LineSecondPoint.lineTest gun s))
    (count : Nat) (atHeader : (resumed gun s).pc=0x2c57f)
    (window : ∀ i<count, OriginalLineResume.SeenAt (resumed gun s).core.memory
      ((resumed gun s).core.regs 2+BitVec.ofNat 32 (2*i)))
    (last : load16 (resumed gun s).core.memory
      ((resumed gun s).core.regs 2+BitVec.ofNat 32 (2*count))=(0xffff#16)) :
    ∃ steps≤656+10*count, X86CodeMemory.Prefix FloorCaller.cm program [] steps
      ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩
      (OriginalLineBounds.returned (OriginalLineCell.header (OriginalLineResume.skipMany count (resumed gun s)).core).core) := by
  obtain ⟨n,hn,head⟩ := line_resume_execution gun s f c h
    ox oy sx sy ex ey geometry layout xout yout okX okY safe
  obtain ⟨m,hm,tail⟩ := OriginalLineResume.through_sentinel count (resumed gun s) atHeader window last
  have tail := tail.transfer program [] contains_resume (by simp)
  exact ⟨n+m,by omega,E1M1PspriteStep.prefix_trans head (X86CodeMemory.lift_success tail FloorCaller.cm)⟩

end Doom.Proofs.E1M1LineResume
