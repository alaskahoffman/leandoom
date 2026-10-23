import Doom.Proofs.E1M1LineInterceptEntry
import Doom.Proofs.OriginalLineSide
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1LineSide
open Verification X86 X86Memory X86Control BlockSummary

def program (pc : Nat) : Option (X86Routine.Op × Nat) :=
  match E1M1LineInterceptEntry.program pc with
  | some op => some op
  | none => OriginalLineSide.program pc

theorem contains_prior (pc : Nat) (h : E1M1LineInterceptEntry.program pc≠none) :
    program pc=E1M1LineInterceptEntry.program pc := by
  unfold program
  cases hp : E1M1LineInterceptEntry.program pc <;> simp_all

theorem contains_entry (pc : Nat) (h : OriginalLineSide.program pc≠none) :
    program pc=OriginalLineSide.program pc := by
  have range : 0x2c010≤pc ∧ pc<0x2c0b3 := by
    by_cases r : 0x2c010≤pc ∧ pc<0x2c0b3
    · exact r
    · simp [OriginalLineSide.program,OriginalLineSide.bytesProgram,r] at h
  have all : ∀ i : Fin 163, program (0x2c010+i.val)=OriginalLineSide.program (0x2c010+i.val) := by decide
  have eq : 0x2c010+(pc-0x2c010)=pc := by omega
  simpa only [eq] using all ⟨pc-0x2c010,by omega⟩

/-- Execute the complete linedef helper only when the real call reaches it. -/
def continueSide (s : X86Control.State) : X86Control.State :=
  if s.pc=0x2c010 then OriginalLineSide.result s.core else s

theorem continue_execution (s : X86Control.State) :
    ∃ n, n≤34 ∧ X86Routine.Prefix program [] n s (continueSide s) := by
  by_cases h : s.pc=0x2c010
  · obtain ⟨n,hn,path⟩ := OriginalLineSide.execution s.core s.flags
    rw [OriginalPathXStep.at_pc _ _ h] at path
    exact ⟨n,hn,by simpa only [continueSide,if_pos h] using path.transfer program [] contains_entry (by simp)⟩
  · exact ⟨0,by omega,by simpa only [continueSide,if_neg h] using X86Routine.Prefix.nil (program:=program) (exits:=[]) s⟩

def firstSide (gun : Fire.Gun) (s : X86Memory.State) := continueSide (E1M1LineInterceptEntry.firstPoint gun s)

/-- The short-trace branch now returns from its first point-side helper.
The divline helper and earlier boundaries remain at their previous PCs. -/
theorem first_side_execution (gun : Fire.Gun) (s : X86Memory.State) (f : Option Flags)
    (c : Weapon.Context) (h : E1M1DischargeSetters.Inputs gun s c)
    (ox oy sx sy ex ey : Fixed)
    (geometry : OriginalPathInit.Inputs (E1M1AimSetup.firstTraversal gun s).core ox oy sx sy ex ey)
    (layout : OriginalAimSetup.Separated (E1M1AimQuery.firstRay gun s).core)
    (xout yout : Int32 × Fixed × Fixed)
    (okX : (Collision.pathStart ox oy sx sy ex ey).xStep=.ok xout)
    (okY : (Collision.pathStart ox oy sx sy ex ey).yStep=.ok yout) :
    ∃ n, n≤435 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n
      ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ (firstSide gun s) := by
  obtain ⟨n,hn,a⟩ := E1M1LineInterceptEntry.first_point_execution gun s f c h
    ox oy sx sy ex ey geometry layout xout yout okX okY
  have a := a.transfer program [] contains_prior (by simp)
  obtain ⟨m,hm,b⟩ := continue_execution (E1M1LineInterceptEntry.firstPoint gun s)
  exact ⟨n+m,by omega,E1M1PspriteStep.prefix_trans a (X86CodeMemory.lift_success b FloorCaller.cm)⟩

theorem helper_live (s : X86Control.State) (line : Collision.Line) (x y : Fixed)
    (linePtr vertexPtr : Word) (entry : s.pc=0x2c010)
    (h : OriginalLineSide.Inputs s.core line x y linePtr vertexPtr) :
    (continueSide s).core.regs 0=OriginalLineSide.bit (line.pointSide x y) := by
  simpa only [continueSide,if_pos entry] using OriginalLineSide.live s.core line x y linePtr vertexPtr h

/-- Additional line fields and separation supplied at the enclosing callback,
covering both its writes and the helper's four saves. -/
structure LineData (s : X86Memory.State) (line : Collision.Line) (p v : Word) : Prop where
  dx : load32 s.memory (p+8)=line.dx.raw.toBitVec
  dy : load32 s.memory (p+12)=line.dy.raw.toBitVec
  safe : ∀ a∈[p,v,v+4,p+8,p+12], ∀ off∈[(4#32),8,12,16,20,40,44,48,52,56],
    Apart a (s.regs 4-off)

theorem entry_inputs (s : X86Memory.State) (trace : Collision.Divline) (line : Collision.Line)
    (p v : Word) (h : OriginalLineInterceptEntry.Inputs s trace line p v)
    (short : trace.usesDivlineTest=false) (data : LineData s line p v) :
    OriginalLineSide.Inputs (OriginalLineInterceptEntry.first s).core line trace.x trace.y p v := by
  have ready := OriginalLineInterceptEntry.live s trace line p v h
  have keep (a : Word) (ha : a∈[p,v,v+4,p+8,p+12]) :
      load32 (OriginalLineInterceptEntry.first s).core.memory a=load32 s.memory a := by
    apply OriginalLineInterceptEntry.first_frame
    · intro off ho; apply data.safe a ha off
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ho ⊢
      rcases ho with rfl|rfl|rfl|rfl|rfl <;> simp
    · exact data.safe a ha 40 (by simp)
  constructor
  · simpa only [short,Bool.false_eq_true,if_false] using ready.pointX
  · simpa only [short,Bool.false_eq_true,if_false] using ready.pointY
  · simpa only [short,Bool.false_eq_true,if_false] using ready.dataArg
  · rw [keep _ (by simp),h.vertex]
  · rw [keep _ (by simp),h.vertexX]
  · rw [keep _ (by simp),h.vertexY]
  · rw [keep _ (by simp),data.dx]
  · rw [keep _ (by simp),data.dy]
  · intro a ha off ho
    rw [ready.stack]
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
    rcases ho with rfl|rfl|rfl|rfl
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using data.safe a ha (44#32) (by simp)
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using data.safe a ha (48#32) (by simp)
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using data.safe a ha (52#32) (by simp)
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using data.safe a ha (56#32) (by simp)

theorem short_result (s : X86Memory.State) (trace : Collision.Divline) (line : Collision.Line)
    (p v : Word) (h : OriginalLineInterceptEntry.Inputs s trace line p v)
    (short : trace.usesDivlineTest=false) (data : LineData s line p v) :
    let t := continueSide (OriginalLineInterceptEntry.first s)
    t.core.regs 0=OriginalLineSide.bit (line.pointSide trace.x trace.y) ∧ t.pc=0x2c65f := by
  have ready := OriginalLineInterceptEntry.live s trace line p v h
  have pc : (OriginalLineInterceptEntry.first s).pc=0x2c010 := by
    simpa [short,OriginalLineInterceptEntry.callee] using ready.pc
  have value := helper_live (OriginalLineInterceptEntry.first s) line trace.x trace.y p v pc
    (entry_inputs s trace line p v h short data)
  refine ⟨value,?_⟩
  simp only [continueSide,if_pos pc]
  rw [(OriginalLineSide.returned (OriginalLineInterceptEntry.first s).core).2.2.2.2.2,ready.stack,ready.returnWord]
  simp [short,OriginalLineInterceptEntry.returnPc]
end Doom.Proofs.E1M1LineSide
