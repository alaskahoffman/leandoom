import Doom.Proofs.E1M1LineFraction
import Doom.Proofs.OriginalLineFinish
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1LineFinish
open Verification X86 X86Memory X86Control BlockSummary

def program (pc : Nat) : Option (X86Routine.Op × Nat) :=
  match E1M1LineFraction.program pc with
  | some op => some op
  | none => OriginalLineFinish.program pc

theorem contains_prior (pc : Nat) (h : E1M1LineFraction.program pc≠none) :
    program pc=E1M1LineFraction.program pc := by
  unfold program
  cases hp : E1M1LineFraction.program pc <;> simp_all

theorem contains_finish (pc : Nat) (h : OriginalLineFinish.program pc≠none) :
    program pc=OriginalLineFinish.program pc := by
  by_cases inside : 0x2c6bb≤pc ∧ pc<0x2c71a
  · have all : ∀ i : Fin 95, program (0x2c6bb+i.val)=OriginalLineFinish.program (0x2c6bb+i.val) := by decide
    have eq : 0x2c6bb+(pc-0x2c6bb)=pc := by omega
    simpa only [eq] using all ⟨pc-0x2c6bb,by omega⟩
  simp [OriginalLineFinish.program,OriginalLineFinish.bytesProgram,inside] at h

def continueFinish (s : X86Control.State) : X86Control.State :=
  if s.pc=0x2c6bb then OriginalLineFinish.result s.core else s

theorem continue_execution (s : X86Control.State) :
    ∃ n≤23, X86Routine.Prefix program [] n s (continueFinish s) := by
  by_cases atCall : s.pc=0x2c6bb
  · obtain ⟨n,hn,hp⟩ := OriginalLineFinish.execution s.core s.flags
    rw [OriginalPathXStep.at_pc _ _ atCall] at hp
    exact ⟨n,hn,by simpa only [continueFinish,if_pos atCall] using hp.transfer program [] contains_finish (by simp)⟩
  · exact ⟨0,by omega,by simpa only [continueFinish,if_neg atCall] using X86Routine.Prefix.nil (program:=program) (exits:=[]) s⟩

def finish (gun : Fire.Gun) (s : X86Memory.State) := continueFinish (E1M1LineFraction.fraction gun s)

theorem line_finish_execution (gun : Fire.Gun) (s : X86Memory.State) (f : Option Flags)
    (c : Weapon.Context) (h : E1M1DischargeSetters.Inputs gun s c)
    (ox oy sx sy ex ey : Fixed)
    (geometry : OriginalPathInit.Inputs (E1M1AimSetup.firstTraversal gun s).core ox oy sx sy ex ey)
    (layout : OriginalAimSetup.Separated (E1M1AimQuery.firstRay gun s).core)
    (xout yout : Int32 × Fixed × Fixed)
    (okX : (Collision.pathStart ox oy sx sy ex ey).xStep=.ok xout)
    (okY : (Collision.pathStart ox oy sx sy ex ey).yStep=.ok yout)
    (safe : E1M1LineFraction.Ready (E1M1LineSecondPoint.lineTest gun s)) :
    ∃ n≤644, X86CodeMemory.Prefix FloorCaller.cm program [] n
      ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ (finish gun s) := by
  obtain ⟨n,hn,a⟩ := E1M1LineFraction.line_fraction_execution gun s f c h
    ox oy sx sy ex ey geometry layout xout yout okX okY safe
  have a := a.transfer program [] contains_prior (by simp)
  obtain ⟨m,hm,b⟩ := continue_execution (E1M1LineFraction.fraction gun s)
  exact ⟨n+m,by omega,E1M1PspriteStep.prefix_trans a (X86CodeMemory.lift_success b FloorCaller.cm)⟩

/-- The arithmetic result supplies the fraction and restored line pointer.
The global/backsector facts remain explicit facts at this boundary. -/
theorem fraction_inputs (s : X86Memory.State) (trace : Collision.Divline)
    (line : Collision.Line) (frac : Fixed) (flags : Nat) (p v : Word)
    (h : OriginalLineFraction.Inputs s trace line p v)
    (computed : Collision.interceptVector trace ⟨line.x,line.y,line.dx,line.dy⟩=.ok frac)
    (active : load32 (OriginalLineFraction.result s).core.memory (0x2c024#32)≠(0#32) ↔ flags &&& 4≠0)
    (back : load32 (OriginalLineFraction.result s).core.memory (p+(50#32))=(0#32) ↔ line.back.isNone=true) :
    OriginalLineFinish.Inputs (OriginalLineFraction.result s).core frac line flags p := by
  have value := OriginalLineFraction.live s trace line (OriginalLineFraction.encoded s trace line p v h)
    (by rw [computed]; rfl)
  simp only [computed,Except.toOption,Option.map,Option.some.injEq] at value
  exact ⟨value.symm, (OriginalLineFraction.returned s).2.2.trans h.pointer,active,back⟩

end Doom.Proofs.E1M1LineFinish
