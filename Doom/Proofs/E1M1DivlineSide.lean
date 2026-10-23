import Doom.Proofs.E1M1LineSide
import Doom.Proofs.OriginalDivlineSide
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1DivlineSide
open Verification X86 X86Memory X86Control BlockSummary

def program (pc : Nat) : Option (X86Routine.Op × Nat) :=
  match E1M1LineSide.program pc with
  | some op => some op
  | none => OriginalDivlineSide.program pc

theorem contains_prior (pc : Nat) (h : E1M1LineSide.program pc≠none) :
    program pc=E1M1LineSide.program pc := by
  unfold program
  cases hp : E1M1LineSide.program pc <;> simp_all

theorem contains_entry (pc : Nat) (h : OriginalDivlineSide.program pc≠none) :
    program pc=OriginalDivlineSide.program pc := by
  have range : 0x2c1e0≤pc ∧ pc<0x2c2a7 := by
    by_cases r : 0x2c1e0≤pc ∧ pc<0x2c2a7
    · exact r
    · simp [OriginalDivlineSide.program,OriginalDivlineSide.bytesProgram,r] at h
  have all : ∀ i : Fin 199, program (0x2c1e0+i.val)=OriginalDivlineSide.program (0x2c1e0+i.val) := by decide
  have eq : 0x2c1e0+(pc-0x2c1e0)=pc := by omega
  simpa only [eq] using all ⟨pc-0x2c1e0,by omega⟩

/-- Execute the complete divline helper only when the real call reaches it. -/
def continueSide (s : X86Control.State) : X86Control.State :=
  if s.pc=0x2c1e0 then OriginalDivlineSide.result s.core else s

theorem continue_execution (s : X86Control.State) :
    ∃ n, n≤44 ∧ X86Routine.Prefix program [] n s (continueSide s) := by
  by_cases h : s.pc=0x2c1e0
  · obtain ⟨n,hn,path⟩ := OriginalDivlineSide.execution s.core s.flags
    rw [OriginalPathXStep.at_pc _ _ h] at path
    exact ⟨n,hn,by simpa only [continueSide,if_pos h] using path.transfer program [] contains_entry (by simp)⟩
  · exact ⟨0,by omega,by simpa only [continueSide,if_neg h] using X86Routine.Prefix.nil (program:=program) (exits:=[]) s⟩

def firstSide (gun : Fire.Gun) (s : X86Memory.State) := continueSide (E1M1LineSide.firstSide gun s)

/-- Both trace-size branches now return from their first point-side helper.
Earlier boundaries and the returned short-trace branch retain their PCs. -/
theorem first_side_execution (gun : Fire.Gun) (s : X86Memory.State) (f : Option Flags)
    (c : Weapon.Context) (h : E1M1DischargeSetters.Inputs gun s c)
    (ox oy sx sy ex ey : Fixed)
    (geometry : OriginalPathInit.Inputs (E1M1AimSetup.firstTraversal gun s).core ox oy sx sy ex ey)
    (layout : OriginalAimSetup.Separated (E1M1AimQuery.firstRay gun s).core)
    (xout yout : Int32 × Fixed × Fixed)
    (okX : (Collision.pathStart ox oy sx sy ex ey).xStep=.ok xout)
    (okY : (Collision.pathStart ox oy sx sy ex ey).yStep=.ok yout) :
    ∃ n, n≤479 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n
      ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ (firstSide gun s) := by
  obtain ⟨n,hn,a⟩ := E1M1LineSide.first_side_execution gun s f c h
    ox oy sx sy ex ey geometry layout xout yout okX okY
  have a := a.transfer program [] contains_prior (by simp)
  obtain ⟨m,hm,b⟩ := continue_execution (E1M1LineSide.firstSide gun s)
  exact ⟨n+m,by omega,E1M1PspriteStep.prefix_trans a (X86CodeMemory.lift_success b FloorCaller.cm)⟩

theorem helper_live (s : X86Control.State) (line : Collision.Divline) (x y : Fixed)
    (linePtr : Word) (entry : s.pc=0x2c1e0)
    (h : OriginalDivlineSide.Inputs s.core line x y linePtr) :
    (continueSide s).core.regs 0=OriginalDivlineSide.bit (line.pointSide x y) := by
  simpa only [continueSide,if_pos entry] using OriginalDivlineSide.live s.core line x y linePtr h

/-- Protect the trace globals through the enclosing callback and helper saves. -/
structure TraceData (s : X86Memory.State) : Prop where
  safe : ∀ a∈[(0x2ba10#32),0x2ba14,0x2ba18,0x2ba1c],
    ∀ off∈[(4#32),8,12,16,20,40,44,48,52,56], Apart a (s.regs 4-off)

theorem entry_inputs (s : X86Memory.State) (trace : Collision.Divline) (line : Collision.Line)
    (p v : Word) (h : OriginalLineInterceptEntry.Inputs s trace line p v)
    (wide : trace.usesDivlineTest=true) (data : TraceData s) :
    OriginalDivlineSide.Inputs (OriginalLineInterceptEntry.first s).core trace line.x line.y 0x2ba10 := by
  have ready := OriginalLineInterceptEntry.live s trace line p v h
  have keep (a : Word) (ha : a∈[(0x2ba10#32),0x2ba14,0x2ba18,0x2ba1c]) :
      load32 (OriginalLineInterceptEntry.first s).core.memory a=load32 s.memory a := by
    apply OriginalLineInterceptEntry.first_frame
    · intro off ho; apply data.safe a ha off
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ho ⊢
      rcases ho with rfl|rfl|rfl|rfl|rfl <;> simp
    · exact data.safe a ha 40 (by simp)
  constructor
  · simpa only [wide,if_true] using ready.pointX
  · simpa only [wide,if_true] using ready.pointY
  · simpa only [wide,if_true] using ready.dataArg
  · rw [keep _ (by simp),h.traceX]
  · change load32 _ (0x2ba14#32)=_; rw [keep _ (by simp)]; exact h.traceY
  · change load32 _ (0x2ba18#32)=_; rw [keep _ (by simp)]; exact h.traceDX
  · change load32 _ (0x2ba1c#32)=_; rw [keep _ (by simp)]; exact h.traceDY
  · intro a ha off ho
    change a∈[(0x2ba10#32),0x2ba14,0x2ba18,0x2ba1c] at ha
    rw [ready.stack]
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
    rcases ho with rfl|rfl|rfl|rfl
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using data.safe a ha (44#32) (by simp)
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using data.safe a ha (48#32) (by simp)
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using data.safe a ha (52#32) (by simp)
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using data.safe a ha (56#32) (by simp)

theorem wide_result (s : X86Memory.State) (trace : Collision.Divline) (line : Collision.Line)
    (p v : Word) (h : OriginalLineInterceptEntry.Inputs s trace line p v)
    (wide : trace.usesDivlineTest=true) (data : TraceData s) :
    let t := continueSide (OriginalLineInterceptEntry.first s)
    t.core.regs 0=OriginalDivlineSide.bit (trace.pointSide line.x line.y) ∧ t.pc=0x2c637 := by
  have ready := OriginalLineInterceptEntry.live s trace line p v h
  have pc : (OriginalLineInterceptEntry.first s).pc=0x2c1e0 := by
    simpa [wide,OriginalLineInterceptEntry.callee] using ready.pc
  have value := helper_live (OriginalLineInterceptEntry.first s) trace line.x line.y 0x2ba10 pc
    (entry_inputs s trace line p v h wide data)
  refine ⟨value,?_⟩
  simp only [continueSide,if_pos pc]
  rw [(OriginalDivlineSide.returned (OriginalLineInterceptEntry.first s).core).2.2.2.2.2,ready.stack,ready.returnWord]
  simp [wide,OriginalLineInterceptEntry.returnPc]
end Doom.Proofs.E1M1DivlineSide
