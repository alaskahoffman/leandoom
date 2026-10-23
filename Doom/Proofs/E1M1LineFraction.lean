import Doom.Proofs.E1M1LineSecondPoint
import Doom.Proofs.OriginalLineFraction
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1LineFraction
open Verification X86 X86Memory X86Control BlockSummary

def program (pc : Nat) : Option (X86Routine.Op × Nat) :=
  match E1M1LineSecondPoint.program pc with
  | some op => some op
  | none => OriginalLineFraction.program pc

theorem contains_prior (pc : Nat) (h : E1M1LineSecondPoint.program pc≠none) :
    program pc=E1M1LineSecondPoint.program pc := by
  unfold program
  cases hp : E1M1LineSecondPoint.program pc <;> simp_all

theorem contains_fraction (pc : Nat) (h : OriginalLineFraction.program pc≠none) :
    program pc=OriginalLineFraction.program pc := by
  by_cases r2c691 : 0x2c691≤pc ∧ pc<0x2c6bb
  · have all : ∀ i : Fin 42, program (0x2c691+i.val)=OriginalLineFraction.program (0x2c691+i.val) := by decide
    have eq : 0x2c691+(pc-0x2c691)=pc := by omega
    simpa only [eq] using all ⟨pc-0x2c691,by omega⟩
  by_cases r2c2d0 : 0x2c2d0≤pc ∧ pc<0x2c334
  · have all : ∀ i : Fin 100, program (0x2c2d0+i.val)=OriginalLineFraction.program (0x2c2d0+i.val) := by decide
    have eq : 0x2c2d0+(pc-0x2c2d0)=pc := by omega
    simpa only [eq] using all ⟨pc-0x2c2d0,by omega⟩
  by_cases r1d180 : 0x1d180≤pc ∧ pc<0x1d1c1
  · have all : ∀ i : Fin 65, program (0x1d180+i.val)=OriginalLineFraction.program (0x1d180+i.val) := by decide
    have eq : 0x1d180+(pc-0x1d180)=pc := by omega
    simpa only [eq] using all ⟨pc-0x1d180,by omega⟩
  simp [OriginalLineFraction.program,OriginalLineFraction.bytesProgram,OriginalInterceptVector.program,
    OriginalInterceptVector.bytesProgram,OriginalDivMemory.program,OriginalDivMemory.bytesProgram,r2c691,r2c2d0,r1d180] at h

def continueFraction (s : X86Control.State) : X86Control.State :=
  if s.pc=0x2c691 then OriginalLineFraction.result s.core else s
def Ready (s : X86Control.State) : Prop :=
  s.pc=0x2c691 → OriginalInterceptVector.Safe (OriginalLineFraction.setup s.core)

theorem continue_execution (s : X86Control.State) (safe : Ready s) :
    ∃ n≤80, X86Routine.Prefix program [] n s (continueFraction s) := by
  by_cases atCall : s.pc=0x2c691
  · obtain ⟨n,hn,hp⟩ := OriginalLineFraction.execution s.core s.flags (safe atCall)
    rw [OriginalPathXStep.at_pc _ _ atCall] at hp
    exact ⟨n,hn,by simpa only [continueFraction,if_pos atCall] using hp.transfer program [] contains_fraction (by simp)⟩
  · exact ⟨0,by omega,by simpa only [continueFraction,if_neg atCall] using X86Routine.Prefix.nil (program:=program) (exits:=[]) s⟩

def fraction (gun : Fire.Gun) (s : X86Memory.State) := continueFraction (E1M1LineSecondPoint.lineTest gun s)

theorem line_fraction_execution (gun : Fire.Gun) (s : X86Memory.State) (f : Option Flags)
    (c : Weapon.Context) (h : E1M1DischargeSetters.Inputs gun s c)
    (ox oy sx sy ex ey : Fixed)
    (geometry : OriginalPathInit.Inputs (E1M1AimSetup.firstTraversal gun s).core ox oy sx sy ex ey)
    (layout : OriginalAimSetup.Separated (E1M1AimQuery.firstRay gun s).core)
    (xout yout : Int32 × Fixed × Fixed)
    (okX : (Collision.pathStart ox oy sx sy ex ey).xStep=.ok xout)
    (okY : (Collision.pathStart ox oy sx sy ex ey).yStep=.ok yout)
    (safe : Ready (E1M1LineSecondPoint.lineTest gun s)) :
    ∃ n≤621, X86CodeMemory.Prefix FloorCaller.cm program [] n
      ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ (fraction gun s) := by
  obtain ⟨n,hn,a⟩ := E1M1LineSecondPoint.line_test_execution gun s f c h
    ox oy sx sy ex ey geometry layout xout yout okX okY
  have a := a.transfer program [] contains_prior (by simp)
  obtain ⟨m,hm,b⟩ := continue_execution (E1M1LineSecondPoint.lineTest gun s) safe
  exact ⟨n+m,by omega,E1M1PspriteStep.prefix_trans a (X86CodeMemory.lift_success b FloorCaller.cm)⟩

/-- Supply the helper precondition from encoded callback inputs and the live
engine's successful arithmetic, only on the path that reaches this call. -/
theorem ready (s : X86Control.State) (trace : Collision.Divline) (line : Collision.Line) (p v : Word)
    (h : s.pc=0x2c691 → OriginalLineFraction.Inputs s.core trace line p v)
    (ok : (Collision.interceptVector trace ⟨line.x,line.y,line.dx,line.dy⟩).isOk=true) : Ready s := by
  intro atCall
  exact OriginalInterceptVector.safe_of_success (OriginalLineFraction.setup s.core) trace _ _ _
    (OriginalLineFraction.encoded s.core trace line p v (h atCall)) ok

theorem crossed_live (s : X86Control.State) (trace : Collision.Divline) (line : Collision.Line) (p v : Word)
    (atCall : s.pc=0x2c691) (h : OriginalLineFraction.Inputs s.core trace line p v)
    (ok : (Collision.interceptVector trace ⟨line.x,line.y,line.dx,line.dy⟩).isOk=true) :
    (Collision.interceptVector trace ⟨line.x,line.y,line.dx,line.dy⟩).toOption.map (fun v => v.raw.toBitVec)=
      some ((continueFraction s).core.regs 0) ∧
    (continueFraction s).pc=0x2c6bb ∧ (continueFraction s).core.regs 4=s.core.regs 4 := by
  simp only [continueFraction,if_pos atCall]
  exact ⟨OriginalLineFraction.live s.core trace line (OriginalLineFraction.encoded s.core trace line p v h) ok,
    (OriginalLineFraction.returned s.core).1,(OriginalLineFraction.returned s.core).2.1⟩
end Doom.Proofs.E1M1LineFraction
