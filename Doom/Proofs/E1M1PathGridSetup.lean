import Doom.Proofs.E1M1PathIntercept
import Doom.Proofs.OriginalPathYStep
import Doom.Proofs.OriginalPathSecondIntercept
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1PathGridSetup
open Verification X86 X86Memory X86Control BlockSummary

def program (pc : Nat) : Option (X86Routine.Op × Nat) :=
  match E1M1PathIntercept.program pc with
  | some op => some op
  | none => match OriginalPathYStep.program pc with
    | some op => some op
    | none => OriginalPathSecondIntercept.program pc

theorem contains_prior (pc : Nat) (h : E1M1PathIntercept.program pc≠none) :
    program pc=E1M1PathIntercept.program pc := by
  unfold program
  cases hp : E1M1PathIntercept.program pc <;> simp_all

theorem contains_y (pc : Nat) (h : OriginalPathYStep.program pc≠none) :
    program pc=OriginalPathYStep.program pc := by
  by_cases y : 0x2ca10≤pc ∧ pc<0x2ca5f
  · have all : ∀ i : Fin 79, program (0x2ca10+i.val)=OriginalPathYStep.program (0x2ca10+i.val) := by decide
    have eq : 0x2ca10+(pc-0x2ca10)=pc := by omega
    simpa only [eq] using all ⟨pc-0x2ca10,by omega⟩
  · by_cases a : 0x418d8≤pc ∧ pc<0x418df
    · have all : ∀ i : Fin 7, program (0x418d8+i.val)=OriginalPathYStep.program (0x418d8+i.val) := by decide
      have eq : 0x418d8+(pc-0x418d8)=pc := by omega
      simpa only [eq] using all ⟨pc-0x418d8,by omega⟩
    · have d : 0x1d180≤pc ∧ pc<0x1d1c1 := by
        by_cases d : 0x1d180≤pc ∧ pc<0x1d1c1
        · exact d
        · simp [OriginalPathYStep.program,y,a,OriginalDivMemory.program,OriginalDivMemory.bytesProgram,d] at h
      have all : ∀ i : Fin 65, program (0x1d180+i.val)=OriginalPathYStep.program (0x1d180+i.val) := by decide
      have eq : 0x1d180+(pc-0x1d180)=pc := by omega
      simpa only [eq] using all ⟨pc-0x1d180,by omega⟩

theorem contains_second (pc : Nat) (h : OriginalPathSecondIntercept.program pc≠none) :
    program pc=OriginalPathSecondIntercept.program pc := by
  have range : 0x2ca5f≤pc ∧ pc<0x2ca7f := by
    by_cases r : 0x2ca5f≤pc ∧ pc<0x2ca7f
    · exact r
    · simp [OriginalPathSecondIntercept.program,OriginalPathSecondIntercept.bytesProgram,r] at h
  have all : ∀ i : Fin 32, program (0x2ca5f+i.val)=OriginalPathSecondIntercept.program (0x2ca5f+i.val) := by decide
  have eq : 0x2ca5f+(pc-0x2ca5f)=pc := by omega
  simpa only [eq] using all ⟨pc-0x2ca5f,by omega⟩

def after (s : X86Memory.State) := OriginalPathSecondIntercept.result (OriginalPathYStep.result s).core
def firstGrid (gun : Fire.Gun) (s : X86Memory.State) := after (E1M1PathIntercept.firstIntercept gun s).core

theorem after_execution (s : X86Memory.State) (safe : OriginalPathYStep.Safe s) :
    ∃ n, n≤51 ∧ X86Routine.Prefix program [] n
      ⟨s,OriginalPathYStep.comparison s,0x2ca10⟩ (after s) := by
  obtain ⟨n,hn,a⟩ := OriginalPathYStep.execution s safe
  have a := a.transfer program [] contains_y (by simp)
  have b := (OriginalPathSecondIntercept.execution (OriginalPathYStep.result s).core
    (OriginalPathYStep.result s).flags).transfer program [] contains_second (by simp)
  rw [OriginalPathXStep.at_pc _ _ (OriginalPathYStep.result_pc s)] at b
  exact ⟨n+10,by omega,OriginalGroupBounds.prefix_join a b⟩

theorem first_grid_execution (gun : Fire.Gun) (s : X86Memory.State) (f : Option Flags)
    (c : Weapon.Context) (h : E1M1DischargeSetters.Inputs gun s c)
    (safeX : OriginalPathXStep.Safe (E1M1PathInit.firstPath gun s).core)
    (safeY : OriginalPathYStep.Safe (E1M1PathIntercept.firstIntercept gun s).core) :
    ∃ n, n≤338 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n
      ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ (firstGrid gun s) := by
  obtain ⟨n,hn,a⟩ := E1M1PathIntercept.first_intercept_execution gun s f c h safeX
  have a := a.transfer program [] contains_prior (by simp)
  obtain ⟨m,hm,b⟩ := after_execution (E1M1PathIntercept.firstIntercept gun s).core safeY
  have b := X86CodeMemory.lift_success b FloorCaller.cm
  have seam : (⟨(E1M1PathIntercept.firstIntercept gun s).core,
      OriginalPathYStep.comparison (E1M1PathIntercept.firstIntercept gun s).core,0x2ca10⟩ : X86Control.State)=
      E1M1PathIntercept.firstIntercept gun s := by rfl
  rw [seam] at b
  exact ⟨n+m,by omega,E1M1PspriteStep.prefix_trans a b⟩

theorem second_inputs (s : X86Memory.State) (p : Collision.PathStart) (out : Int32 × Fixed × Fixed)
    (h : OriginalPathYStep.Inputs s p) (ok : p.yStep=.ok out)
    (x : s.regs 6=p.x1.raw.toBitVec)
    (bx : load32 s.memory (s.regs 4+(12#32))=p.startBlockX.toBitVec)
    (by_ : load32 s.memory (s.regs 4+(16#32))=p.startBlockY.toBitVec) :
    OriginalPathSecondIntercept.Inputs (OriginalPathYStep.result s).core p out.2.1 out.2.2 := by
  have obs := (OriginalPathYStep.live s p out h ok).2
  constructor
  · rw [(OriginalPathYStep.preserved s).2]; exact x
  · exact congrArg (fun v => v.2.1) obs
  · exact congrArg (fun v => v.2.2) obs
  · rw [(OriginalPathYStep.preserved s).1,OriginalPathYStep.local_preserved _ _ (by simp)]
    exact bx
  · rw [(OriginalPathYStep.preserved s).1,OriginalPathYStep.local_preserved _ _ (by simp)]
    exact by_

theorem second_local (s : X86Memory.State) (off : Word) (h : off∈[12,16,20,24,28,32,40,44]) :
    load32 (OriginalPathSecondIntercept.result s).core.memory (s.regs 4+off)=
      load32 s.memory (s.regs 4+off) := by
  apply OriginalPathSecondIntercept.frame
  apply OriginalPathXStep.apart_translate
  simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> unfold Apart <;> decide

theorem after_local (s : X86Memory.State) (off : Word) (h : off∈[12,16,20,24,32,40,44]) :
    load32 (after s).core.memory (s.regs 4+off)=load32 s.memory (s.regs 4+off) := by
  have member : off∈[12,16,20,24,28,32,40,44] := by
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at h ⊢
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp
  have frame := second_local (OriginalPathYStep.result s).core off member
  rw [(OriginalPathYStep.preserved s).1] at frame
  unfold after
  rw [frame,OriginalPathYStep.local_preserved s off h]

theorem first_local (s : X86Memory.State) (off : Word) (h : off∈[12,16,20,24,28,32]) :
    load32 (OriginalPathIntercept.result s).core.memory (s.regs 4+off)=load32 s.memory (s.regs 4+off) := by
  apply OriginalPathIntercept.frame
  intro a ha
  have separate : Apart off a := by
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at h ha
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl <;> rcases ha with rfl|rfl|rfl <;> unfold Apart <;> decide
  exact OriginalPathXStep.apart_translate _ _ _ separate

/-- The initial cell indices survive both preceding executable blocks. -/
theorem blocks_from_init (s : X86Memory.State) (ox oy sx sy ex ey : Fixed)
    (h : OriginalPathInit.Inputs s ox oy sx sy ex ey) :
    let t := OriginalPathIntercept.result (OriginalPathXStep.result (OriginalPathInit.result s).core).core
    load32 t.core.memory (t.core.regs 4+(12#32))=(Collision.pathStart ox oy sx sy ex ey).startBlockX.toBitVec ∧
    load32 t.core.memory (t.core.regs 4+(16#32))=(Collision.pathStart ox oy sx sy ex ey).startBlockY.toBitVec := by
  have ready := OriginalPathInit.ready s ox oy sx sy ex ey h
  have sp (s : X86Memory.State) : (OriginalPathIntercept.result s).core.regs 4=s.regs 4 := rfl
  dsimp only
  rw [sp]
  constructor
  · rw [first_local _ _ (by simp),PathXStepFrame.stack,PathXStepFrame.local_preserved _ _ (by simp),ready.stack]
    have addr : s.regs 4-60+(12#32)=s.regs 4-48 := by simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rw [addr]
    exact congrArg (fun v => v.1) ready.blocks
  · rw [first_local _ _ (by simp),PathXStepFrame.stack,PathXStepFrame.local_preserved _ _ (by simp),ready.stack]
    have addr : s.regs 4-60+(16#32)=s.regs 4-44 := by simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rw [addr]
    exact congrArg (fun v => v.2.1) ready.blocks

/-- Complete numeric grid-walk initialization, before either cell visitor runs. -/
structure Ready (sp : Word) (t : X86Control.State) (p : Collision.PathStart)
    (xout yout : Int32 × Fixed × Fixed) : Prop where
  xIntercept : t.core.regs 5=(Collision.pathFirstIntercept p.x1 yout.2.1 yout.2.2).raw.toBitVec
  yIntercept : load32 t.core.memory (sp+(44#32))=(Collision.pathFirstIntercept p.y1 xout.2.1 xout.2.2).raw.toBitVec
  xDirection : load32 t.core.memory (sp+(32#32))=xout.1.toBitVec
  yDirection : load32 t.core.memory (sp+(28#32))=yout.1.toBitVec
  xStride : load32 t.core.memory (sp+(36#32))=yout.2.2.raw.toBitVec
  yStride : load32 t.core.memory (sp+(40#32))=xout.2.2.raw.toBitVec
  mapX : t.core.regs 6=p.startBlockX.toBitVec
  mapY : t.core.regs 1=p.startBlockY.toBitVec
  counter : t.core.regs 7=0
  stack : t.core.regs 4=sp
  pc : t.pc=0x2ca7f

/-- Both successful production axis calculations imply the complete original
numeric setup, with earlier encodings transported rather than re-assumed. -/
theorem grid_observation_from_init (s : X86Memory.State) (ox oy sx sy ex ey : Fixed)
    (h : OriginalPathInit.Inputs s ox oy sx sy ex ey)
    (xout yout : Int32 × Fixed × Fixed)
    (okX : (Collision.pathStart ox oy sx sy ex ey).xStep=.ok xout)
    (okY : (Collision.pathStart ox oy sx sy ex ey).yStep=.ok yout) :
    let x := OriginalPathXStep.result (OriginalPathInit.result s).core
    let t := OriginalPathIntercept.result x.core
    OriginalPathYStep.Safe t.core ∧ Ready (x.core.regs 4) (after t.core)
      (Collision.pathStart ox oy sx sy ex ey) xout yout := by
  let x := OriginalPathXStep.result (OriginalPathInit.result s).core
  let t := OriginalPathIntercept.result x.core
  have first := OriginalPathIntercept.live x.core _ _ _
    (E1M1PathIntercept.inputs_from_xstep s ox oy sx sy ex ey h xout okX)
  have yInputs := (OriginalPathYStep.inputs_from_intercept x.core t _ _ _ first).1
  have y := OriginalPathYStep.live t.core _ yout yInputs okY
  have blocks := blocks_from_init s ox oy sx sy ex ey h
  have second := OriginalPathSecondIntercept.live (OriginalPathYStep.result t.core).core _ _ _
    (second_inputs t.core _ yout yInputs okY first.startX blocks.1 blocks.2)
  have ysp := (OriginalPathYStep.preserved t.core).1
  have tsp : t.core.regs 4=x.core.regs 4 := first.stack
  have dir := second_local (OriginalPathYStep.result t.core).core (28#32) (by simp)
  rw [ysp] at dir
  have xObs := (OriginalPathXStep.live (OriginalPathInit.result s).core _ xout
    (E1M1PathXStep.inputs_from_init _ _ _ _ _ _ _ h) okX).2
  have xDir : load32 x.core.memory (x.core.regs 4+(32#32))=xout.1.toBitVec := by
    rw [PathXStepFrame.stack]
    exact congrArg (fun v => v.1) xObs
  refine ⟨y.1,?_⟩
  constructor
  · exact second.firstIntercept
  · rw [←tsp,after_local _ _ (by simp),tsp]
    exact first.firstIntercept
  · rw [←tsp,after_local _ _ (by simp),tsp,first_local _ _ (by simp)]
    exact xDir
  · rw [←tsp]
    change load32 (after t.core).core.memory (t.core.regs 4+(28#32))=_
    unfold after
    rw [dir]
    exact congrArg (fun v => v.1) y.2
  · rw [←tsp,←ysp]
    exact second.strideSlot
  · rw [←tsp,after_local _ _ (by simp),tsp]
    exact first.strideSlot
  · exact second.mapX
  · exact second.mapY
  · exact second.counter
  · exact second.stack.trans (ysp.trans tsp)
  · exact second.pc

/-- Continuous original firing execution now reaches the first grid-cell visit.
Sound/encoding assumptions remain explicit; cell visitors and callbacks are next. -/
theorem first_grid_correspondence (gun : Fire.Gun) (s : X86Memory.State) (f : Option Flags)
    (c : Weapon.Context) (h : E1M1DischargeSetters.Inputs gun s c)
    (ox oy sx sy ex ey : Fixed)
    (geometry : OriginalPathInit.Inputs (E1M1AimSetup.firstTraversal gun s).core ox oy sx sy ex ey)
    (xout yout : Int32 × Fixed × Fixed)
    (okX : (Collision.pathStart ox oy sx sy ex ey).xStep=.ok xout)
    (okY : (Collision.pathStart ox oy sx sy ex ey).yStep=.ok yout) :
    ∃ n, n≤338 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n
      ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ (firstGrid gun s) ∧
    Ready ((E1M1PathXStep.firstXStep gun s).core.regs 4) (firstGrid gun s)
      (Collision.pathStart ox oy sx sy ex ey) xout yout := by
  have observed := grid_observation_from_init _ ox oy sx sy ex ey geometry xout yout okX okY
  have safeX := (OriginalPathXStep.live (E1M1PathInit.firstPath gun s).core _ xout
    (E1M1PathXStep.inputs_from_init _ _ _ _ _ _ _ geometry) okX).1
  obtain ⟨n,hn,path⟩ := first_grid_execution gun s f c h safeX observed.1
  exact ⟨n,hn,path,observed.2⟩
end Doom.Proofs.E1M1PathGridSetup
