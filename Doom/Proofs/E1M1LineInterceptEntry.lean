import Doom.Proofs.E1M1LineCell
import Doom.Proofs.OriginalLineInterceptEntry
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1LineInterceptEntry
open Verification X86 X86Memory X86Control BlockSummary

def program (pc : Nat) : Option (X86Routine.Op × Nat) :=
  match E1M1LineCell.program pc with
  | some op => some op
  | none => OriginalLineInterceptEntry.program pc

theorem contains_prior (pc : Nat) (h : E1M1LineCell.program pc≠none) :
    program pc=E1M1LineCell.program pc := by
  unfold program
  cases hp : E1M1LineCell.program pc <;> simp_all

theorem contains_entry (pc : Nat) (h : OriginalLineInterceptEntry.program pc≠none) :
    program pc=OriginalLineInterceptEntry.program pc := by
  have range : (0x2c5f0≤pc ∧ pc<0x2c637) ∨ (0x2c64d≤pc ∧ pc<0x2c65f) := by
    by_cases r : 0x2c5f0≤pc ∧ pc<0x2c637
    · exact Or.inl r
    · by_cases q : 0x2c64d≤pc ∧ pc<0x2c65f
      · exact Or.inr q
      · simp [OriginalLineInterceptEntry.program,OriginalLineInterceptEntry.bytesProgram,r,q] at h
  rcases range with r | r
  · have all : ∀ i : Fin 71, program (0x2c5f0+i.val)=OriginalLineInterceptEntry.program (0x2c5f0+i.val) := by decide
    have eq : 0x2c5f0+(pc-0x2c5f0)=pc := by omega
    simpa only [eq] using all ⟨pc-0x2c5f0,by omega⟩
  · have all : ∀ i : Fin 18, program (0x2c64d+i.val)=OriginalLineInterceptEntry.program (0x2c64d+i.val) := by decide
    have eq : 0x2c64d+(pc-0x2c64d)=pc := by omega
    simpa only [eq] using all ⟨pc-0x2c64d,by omega⟩

/-- Only a real arrival at the line callback enters its side-test setup. -/
def continueCallback (s : X86Control.State) : X86Control.State :=
  if s.pc=0x2c5f0 then OriginalLineInterceptEntry.first s.core else s

theorem continue_execution (s : X86Control.State) :
    ∃ n, n≤22 ∧ X86Routine.Prefix program [] n s (continueCallback s) := by
  by_cases h : s.pc=0x2c5f0
  · obtain ⟨n,hn,path⟩ := OriginalLineInterceptEntry.first_execution s.core s.flags
    rw [OriginalPathXStep.at_pc _ _ h] at path
    exact ⟨n,hn,by simpa only [continueCallback,if_pos h] using path.transfer program [] contains_entry (by simp)⟩
  · exact ⟨0,by omega,by simpa only [continueCallback,if_neg h] using X86Routine.Prefix.nil (program:=program) (exits:=[]) s⟩

def firstPoint (gun : Fire.Gun) (s : X86Memory.State) := continueCallback (E1M1LineCell.firstCell gun s)

/-- Continuous original firing extends the first-cell prefix through callback
branch selection to its first real point-side helper call. Earlier terminal
boundaries stay unchanged; this does not assert that every shot finds a line. -/
theorem first_point_execution (gun : Fire.Gun) (s : X86Memory.State) (f : Option Flags)
    (c : Weapon.Context) (h : E1M1DischargeSetters.Inputs gun s c)
    (ox oy sx sy ex ey : Fixed)
    (geometry : OriginalPathInit.Inputs (E1M1AimSetup.firstTraversal gun s).core ox oy sx sy ex ey)
    (layout : OriginalAimSetup.Separated (E1M1AimQuery.firstRay gun s).core)
    (xout yout : Int32 × Fixed × Fixed)
    (okX : (Collision.pathStart ox oy sx sy ex ey).xStep=.ok xout)
    (okY : (Collision.pathStart ox oy sx sy ex ey).yStep=.ok yout) :
    ∃ n, n≤401 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n
      ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ (firstPoint gun s) := by
  obtain ⟨n,hn,a⟩ := E1M1LineCell.first_cell_execution gun s f c h
    ox oy sx sy ex ey geometry layout xout yout okX okY
  have a := a.transfer program [] contains_prior (by simp)
  obtain ⟨m,hm,b⟩ := continue_execution (E1M1LineCell.firstCell gun s)
  exact ⟨n+m,by omega,E1M1PspriteStep.prefix_trans a (X86CodeMemory.lift_success b FloorCaller.cm)⟩

theorem callback_live (s : X86Control.State) (trace : Collision.Divline) (line : Collision.Line)
    (linePtr vertexPtr : Word) (entry : s.pc=0x2c5f0)
    (h : OriginalLineInterceptEntry.Inputs s.core trace line linePtr vertexPtr) :
    OriginalLineInterceptEntry.Ready s.core (continueCallback s) trace line linePtr := by
  simpa only [continueCallback,if_pos entry] using OriginalLineInterceptEntry.live s.core trace line linePtr vertexPtr h

end Doom.Proofs.E1M1LineInterceptEntry
