import Doom.Proofs.E1M1DivlineSide
import Doom.Proofs.OriginalLineSecondPoint
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1LineSecondPoint
open Verification X86 X86Memory X86Control BlockSummary

def program (pc : Nat) : Option (X86Routine.Op × Nat) :=
  match E1M1DivlineSide.program pc with
  | some op => some op
  | none => OriginalLineSecondPoint.program pc

theorem contains_prior (pc : Nat) (h : E1M1DivlineSide.program pc≠none) :
    program pc=E1M1DivlineSide.program pc := by
  unfold program
  cases hp : E1M1DivlineSide.program pc <;> simp_all

theorem contains_second (pc : Nat) (h : OriginalLineSecondPoint.program pc≠none) :
    program pc=OriginalLineSecondPoint.program pc := by
  by_cases r0 : 0x2c637≤pc ∧ pc<0x2c64d
  · have all : ∀ i : Fin 22, program (0x2c637+i.val)=OriginalLineSecondPoint.program (0x2c637+i.val) := by decide
    have eq : 0x2c637+(pc-0x2c637)=pc := by omega
    simpa only [eq] using all ⟨pc-0x2c637,by omega⟩
  by_cases r1 : 0x2c65f≤pc ∧ pc<0x2c691
  · have all : ∀ i : Fin 50, program (0x2c65f+i.val)=OriginalLineSecondPoint.program (0x2c65f+i.val) := by decide
    have eq : 0x2c65f+(pc-0x2c65f)=pc := by omega
    simpa only [eq] using all ⟨pc-0x2c65f,by omega⟩
  by_cases r2 : 0x2c711≤pc ∧ pc<0x2c71a
  · have all : ∀ i : Fin 9, program (0x2c711+i.val)=OriginalLineSecondPoint.program (0x2c711+i.val) := by decide
    have eq : 0x2c711+(pc-0x2c711)=pc := by omega
    simpa only [eq] using all ⟨pc-0x2c711,by omega⟩
  by_cases r3 : 0x2c1e0≤pc ∧ pc<0x2c2a7
  · have all : ∀ i : Fin 199, program (0x2c1e0+i.val)=OriginalLineSecondPoint.program (0x2c1e0+i.val) := by decide
    have eq : 0x2c1e0+(pc-0x2c1e0)=pc := by omega
    simpa only [eq] using all ⟨pc-0x2c1e0,by omega⟩
  by_cases r4 : 0x2c010≤pc ∧ pc<0x2c0b3
  · have all : ∀ i : Fin 163, program (0x2c010+i.val)=OriginalLineSecondPoint.program (0x2c010+i.val) := by decide
    have eq : 0x2c010+(pc-0x2c010)=pc := by omega
    simpa only [eq] using all ⟨pc-0x2c010,by omega⟩
  simp [OriginalLineSecondPoint.program,OriginalLineSecondPoint.bytesProgram,OriginalLineSecondPoint.localBytes,
    OriginalDivlineSide.program,OriginalDivlineSide.bytesProgram,OriginalLineSide.program,OriginalLineSide.bytesProgram,r0,r1,r2,r3,r4] at h

def continueTest (s : X86Control.State) : X86Control.State :=
  if s.pc=0x2c637 then OriginalLineSecondPoint.result true s.core
  else if s.pc=0x2c65f then OriginalLineSecondPoint.result false s.core else s

theorem continue_execution (s : X86Control.State) :
    ∃ n, n≤62 ∧ X86Routine.Prefix program [] n s (continueTest s) := by
  by_cases hw : s.pc=0x2c637
  · obtain ⟨n,hn,path⟩ := OriginalLineSecondPoint.execution true s.core s.flags
    change X86Routine.Prefix _ _ _ ⟨s.core,s.flags,0x2c637⟩ _ at path
    rw [OriginalPathXStep.at_pc _ _ hw] at path
    exact ⟨n,hn,by simpa only [continueTest,if_pos hw] using path.transfer program [] contains_second (by simp)⟩
  · by_cases hs : s.pc=0x2c65f
    · obtain ⟨n,hn,path⟩ := OriginalLineSecondPoint.execution false s.core s.flags
      change X86Routine.Prefix _ _ _ ⟨s.core,s.flags,0x2c65f⟩ _ at path
      rw [OriginalPathXStep.at_pc _ _ hs] at path
      exact ⟨n,hn,by simpa only [continueTest,if_neg hw,if_pos hs] using path.transfer program [] contains_second (by simp)⟩
    · exact ⟨0,by omega,by simpa only [continueTest,if_neg hw,if_neg hs] using X86Routine.Prefix.nil (program:=program) (exits:=[]) s⟩

def lineTest (gun : Fire.Gun) (s : X86Memory.State) := continueTest (E1M1DivlineSide.firstSide gun s)

theorem line_test_execution (gun : Fire.Gun) (s : X86Memory.State) (f : Option Flags)
    (c : Weapon.Context) (h : E1M1DischargeSetters.Inputs gun s c)
    (ox oy sx sy ex ey : Fixed)
    (geometry : OriginalPathInit.Inputs (E1M1AimSetup.firstTraversal gun s).core ox oy sx sy ex ey)
    (layout : OriginalAimSetup.Separated (E1M1AimQuery.firstRay gun s).core)
    (xout yout : Int32 × Fixed × Fixed)
    (okX : (Collision.pathStart ox oy sx sy ex ey).xStep=.ok xout)
    (okY : (Collision.pathStart ox oy sx sy ex ey).yStep=.ok yout) :
    ∃ n, n≤541 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n
      ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ (lineTest gun s) := by
  obtain ⟨n,hn,a⟩ := E1M1DivlineSide.first_side_execution gun s f c h
    ox oy sx sy ex ey geometry layout xout yout okX okY
  have a := a.transfer program [] contains_prior (by simp)
  obtain ⟨m,hm,b⟩ := continue_execution (E1M1DivlineSide.firstSide gun s)
  exact ⟨n+m,by omega,E1M1PspriteStep.prefix_trans a (X86CodeMemory.lift_success b FloorCaller.cm)⟩

theorem at_return (s : X86Control.State) (wide : Bool) (entry : s.pc=OriginalLineSecondPoint.startPc wide) :
    continueTest s=OriginalLineSecondPoint.result wide s.core := by
  cases wide <;> simp [OriginalLineSecondPoint.startPc] at entry <;> simp [continueTest,entry]

theorem rejected_live (s : X86Control.State) (trace : Collision.Divline) (line : Collision.Line)
    (p v w : Word) (entry : s.pc=OriginalLineSecondPoint.startPc trace.usesDivlineTest)
    (h : OriginalLineSecondPoint.Inputs s.core trace line p v w)
    (same : OriginalLineSecondPoint.firstSide trace line=OriginalLineSecondPoint.lastSide trace line) :
    (continueTest s).core.regs 0=(1#32) ∧
    (continueTest s).pc=(load32 s.core.memory (s.core.regs 4+36)).toNat ∧
    Collision.lineIntercept trace line=.ok none := by
  rw [at_return s trace.usesDivlineTest entry]
  exact OriginalLineSecondPoint.rejection s.core trace line p v w h same

/-- Additional endpoint data at the enclosing callback, before either side call. -/
structure LineData (s : X86Memory.State) (line : Collision.Line) (p v w : Word) : Prop where
  vertex2 : load32 s.memory (p+4)=w
  x2 : load32 s.memory w=(line.x+line.dx).raw.toBitVec
  y2 : load32 s.memory (w+4)=(line.y+line.dy).raw.toBitVec
  dx : load32 s.memory (p+8)=line.dx.raw.toBitVec
  dy : load32 s.memory (p+12)=line.dy.raw.toBitVec
  safe : ∀ a∈OriginalLineSecondPoint.reads p v w,
    ∀ off∈[(4#32),8,12,16,20,40,44,48,52,56], Apart a (s.regs 4-off)

def firstReturn (s : X86Memory.State) :=
  E1M1DivlineSide.continueSide (E1M1LineSide.continueSide (OriginalLineInterceptEntry.first s))

theorem first_return_form (s : X86Memory.State) (trace : Collision.Divline) (line : Collision.Line)
    (p v : Word) (h : OriginalLineInterceptEntry.Inputs s trace line p v) :
    firstReturn s=if trace.usesDivlineTest then OriginalDivlineSide.result (OriginalLineInterceptEntry.first s).core
      else OriginalLineSide.result (OriginalLineInterceptEntry.first s).core := by
  have r := OriginalLineInterceptEntry.live s trace line p v h
  cases hw : trace.usesDivlineTest
  · have pc : (OriginalLineInterceptEntry.first s).pc=0x2c010 := by simpa [OriginalLineInterceptEntry.callee,hw] using r.pc
    have ret : (OriginalLineSide.result (OriginalLineInterceptEntry.first s).core).pc=0x2c65f := by
      rw [(OriginalLineSide.returned _).2.2.2.2.2,r.stack,r.returnWord]
      simp [OriginalLineInterceptEntry.returnPc,hw]
    simp [firstReturn,E1M1DivlineSide.continueSide,E1M1LineSide.continueSide,pc,ret,hw]
  · have pc : (OriginalLineInterceptEntry.first s).pc=0x2c1e0 := by simpa [OriginalLineInterceptEntry.callee,hw] using r.pc
    simp [firstReturn,E1M1DivlineSide.continueSide,E1M1LineSide.continueSide,pc,hw]

theorem first_return_regs (s : X86Memory.State) (trace : Collision.Divline) (line : Collision.Line)
    (p v : Word) (h : OriginalLineInterceptEntry.Inputs s trace line p v) :
    (firstReturn s).core.regs 4=s.regs 4-(36#32) ∧ (firstReturn s).core.regs 1=p ∧
    (firstReturn s).pc=OriginalLineSecondPoint.startPc trace.usesDivlineTest := by
  have r := OriginalLineInterceptEntry.live s trace line p v h
  rw [first_return_form s trace line p v h]
  cases hw : trace.usesDivlineTest
  · simp only [Bool.false_eq_true,if_false]
    have k := OriginalLineSide.returned (OriginalLineInterceptEntry.first s).core
    rw [r.stack,r.lineSaved,r.returnWord] at k
    refine ⟨?_,k.2.1,?_⟩
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using k.1
    · simpa [OriginalLineInterceptEntry.returnPc,OriginalLineSecondPoint.startPc,hw] using k.2.2.2.2.2
  · simp only [if_true]
    have k := OriginalDivlineSide.returned (OriginalLineInterceptEntry.first s).core
    rw [r.stack,r.lineSaved,r.returnWord] at k
    refine ⟨?_,k.2.1,?_⟩
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using k.1
    · simpa [OriginalLineInterceptEntry.returnPc,OriginalLineSecondPoint.startPc,hw] using k.2.2.2.2.2

theorem first_return_frame (s : X86Memory.State) (trace : Collision.Divline) (line : Collision.Line)
    (p v : Word) (h : OriginalLineInterceptEntry.Inputs s trace line p v) (a : Word)
    (safe : ∀ off∈[(4#32),8,12,16,20,40,44,48,52,56], Apart a (s.regs 4-off)) :
    load32 (firstReturn s).core.memory a=load32 s.memory a := by
  have r := OriginalLineInterceptEntry.live s trace line p v h
  have inner : ∀ off∈[(4#32),8,12,16], Apart a ((OriginalLineInterceptEntry.first s).core.regs 4-off) := by
    intro off ho
    rw [r.stack]
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
    rcases ho with rfl|rfl|rfl|rfl
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe (44#32) (by simp)
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe (48#32) (by simp)
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe (52#32) (by simp)
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe (56#32) (by simp)
  have outer : load32 (OriginalLineInterceptEntry.first s).core.memory a=load32 s.memory a := by
    apply OriginalLineInterceptEntry.first_frame
    · intro off ho; apply safe off
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ho ⊢
      rcases ho with rfl|rfl|rfl|rfl|rfl <;> simp
    · exact safe 40 (by simp)
  rw [first_return_form s trace line p v h]
  split
  · exact (OriginalDivlineSide.frame _ a inner).trans outer
  · exact (OriginalLineSide.frame _ a inner).trans outer

theorem entry_inputs (s : X86Memory.State) (trace : Collision.Divline) (line : Collision.Line)
    (p v w : Word) (h : OriginalLineInterceptEntry.Inputs s trace line p v) (data : LineData s line p v w) :
    OriginalLineSecondPoint.Inputs (firstReturn s).core trace line p v w := by
  have r := first_return_regs s trace line p v h
  have keep (a : Word) (ha : a∈OriginalLineSecondPoint.reads p v w) :=
    first_return_frame s trace line p v h a (data.safe a ha)
  constructor
  · cases hw : trace.usesDivlineTest
    · have d : E1M1LineSide.LineData s line p v := by
        refine ⟨data.dx,data.dy,?_⟩
        intro a ha off ho
        apply data.safe a ?_ off ho
        simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
        rcases ha with rfl|rfl|rfl|rfl|rfl <;> simp [OriginalLineSecondPoint.reads]
      have k := (E1M1LineSide.short_result s trace line p v h hw d).1
      rw [first_return_form s trace line p v h]
      have pc := (OriginalLineInterceptEntry.live s trace line p v h).pc
      simpa [OriginalLineSecondPoint.firstSide,hw,E1M1LineSide.continueSide,pc,OriginalLineInterceptEntry.callee] using k
    · have d : E1M1DivlineSide.TraceData s := by
        constructor
        intro a ha off ho
        apply data.safe a ?_ off ho
        simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
        rcases ha with rfl|rfl|rfl|rfl <;> simp [OriginalLineSecondPoint.reads]
      have k := (E1M1DivlineSide.wide_result s trace line p v h hw d).1
      rw [first_return_form s trace line p v h]
      have pc := (OriginalLineInterceptEntry.live s trace line p v h).pc
      simpa [OriginalLineSecondPoint.firstSide,hw,E1M1DivlineSide.continueSide,pc,OriginalLineInterceptEntry.callee,
        OriginalDivlineSide.bit,OriginalLineSide.bit] using k
  · exact r.2.1
  · rw [keep _ (by simp [OriginalLineSecondPoint.reads]),h.vertex]
  · rw [keep _ (by simp [OriginalLineSecondPoint.reads]),data.vertex2]
  · rw [keep _ (by simp [OriginalLineSecondPoint.reads]),h.vertexX]
  · rw [keep _ (by simp [OriginalLineSecondPoint.reads]),h.vertexY]
  · rw [keep _ (by simp [OriginalLineSecondPoint.reads]),data.x2]
  · rw [keep _ (by simp [OriginalLineSecondPoint.reads]),data.y2]
  · rw [keep _ (by simp [OriginalLineSecondPoint.reads]),data.dx]
  · rw [keep _ (by simp [OriginalLineSecondPoint.reads]),data.dy]
  · rw [keep _ (by simp [OriginalLineSecondPoint.reads]),h.traceX]
  · rw [keep _ (by simp [OriginalLineSecondPoint.reads]),h.traceY]
  · rw [keep _ (by simp [OriginalLineSecondPoint.reads]),h.traceDX]
  · rw [keep _ (by simp [OriginalLineSecondPoint.reads]),h.traceDY]
  · intro a ha off ho
    rw [r.1]
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
    rcases ho with rfl|rfl|rfl|rfl|rfl
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using data.safe a ha (40#32) (by simp)
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using data.safe a ha (44#32) (by simp)
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using data.safe a ha (48#32) (by simp)
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using data.safe a ha (52#32) (by simp)
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using data.safe a ha (56#32) (by simp)

theorem callback_rejection (s : X86Memory.State) (trace : Collision.Divline) (line : Collision.Line)
    (p v w : Word) (h : OriginalLineInterceptEntry.Inputs s trace line p v) (data : LineData s line p v w)
    (same : OriginalLineSecondPoint.firstSide trace line=OriginalLineSecondPoint.lastSide trace line) :
    (continueTest (firstReturn s)).core.regs 0=(1#32) ∧
    (continueTest (firstReturn s)).pc=(load32 s.memory (s.regs 4)).toNat ∧
    Collision.lineIntercept trace line=.ok none := by
  have r := first_return_regs s trace line p v h
  have k := rejected_live (firstReturn s) trace line p v w r.2.2 (entry_inputs s trace line p v w h data) same
  have keep : load32 (firstReturn s).core.memory (s.regs 4)=load32 s.memory (s.regs 4) := by
    apply first_return_frame s trace line p v h
    intro off ho
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
    rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simpa only [BitVec.sub_zero] using OriginalLineSide.slots_apart (s.regs 4) (0#32) _ (by unfold Apart; decide)
  have addr : (firstReturn s).core.regs 4+(36#32)=s.regs 4 := by
    rw [r.1]; simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  change _ ∧ (continueTest (firstReturn s)).pc=(load32 (firstReturn s).core.memory ((firstReturn s).core.regs 4+(36#32))).toNat ∧ _ at k
  rw [addr,keep] at k
  exact k
end Doom.Proofs.E1M1LineSecondPoint
