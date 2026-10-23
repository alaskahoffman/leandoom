import Doom.Proofs.OriginalLineGeometry
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1LineGeometry
open Verification X86 X86Memory X86Control BlockSummary OriginalLineGeometry

def joinedBytes (vertices delta horizontal vertical copy cache advance : List UInt8) : X86Routine.Program := fun pc =>
  if pc<0x2e358 then bytesProgram vertices delta horizontal vertical pc
  else OriginalLineLoad.joinedBytes copy cache advance pc
def program := joinedBytes verticesBytes deltaBytes horizontalBytes verticalBytes
  OriginalLineLoad.copyBytes OriginalLineCache.cacheBytes OriginalLineLoad.advanceBytes

theorem geometry_agrees (pc : Nat) (h : OriginalLineGeometry.program pc≠none) :
    program pc=OriginalLineGeometry.program pc := by
  have lt : pc<0x2e358 := by
    by_cases yes : pc<0x2e358
    · exact yes
    · have a : ¬(0x2e2b2≤pc ∧ pc<0x2e2d6) := by omega
      have b : ¬(0x2e2d6≤pc ∧ pc<0x2e2ec) := by omega
      have c : ¬(0x2e326≤pc ∧ pc<0x2e33d) := by omega
      have d : ¬(0x2e33d≤pc ∧ pc<0x2e358) := by omega
      simp [OriginalLineGeometry.program,bytesProgram,a,b,c,d] at h
  simp [program,joinedBytes,lt,OriginalLineGeometry.program]
theorem load_agrees (pc : Nat) (h : OriginalLineLoad.program pc≠none) :
    program pc=OriginalLineLoad.program pc := by
  have ge : ¬pc<0x2e358 := by
    intro lt
    have a : ¬(0x2e368≤pc ∧ pc<0x2e3ac) := by omega
    have b : ¬(0x2e358≤pc ∧ pc<0x2e368) := by omega
    have c : ¬(0x2e3ac≤pc ∧ pc<0x2e3c1) := by omega
    simp [OriginalLineLoad.program,OriginalLineLoad.joinedBytes,OriginalLineLoad.bytesProgram,a,b,c] at h
  simp [program,joinedBytes,ge,OriginalLineLoad.program]

def result (s : X86Memory.State) := OriginalLineLoad.result (bounds s).core

theorem joined_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x2e29a,0x2e3c1] 42 ⟨s,f,0x2e326⟩=some (result s) := by
  have active (pc : Nat) (h : program pc≠none) : pc∉[0x2e29a,0x2e3c1] := by
    intro member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl <;> exact h (by decide)
  obtain ⟨a,ha,pa,_⟩ := X86Routine.run_path (bounds_execution s f)
  have pa := pa.transfer program [0x2e29a,0x2e3c1] geometry_agrees (fun pc h => active pc (by rw [geometry_agrees pc h]; exact h))
  obtain ⟨b,hb,pb,last⟩ := X86Routine.run_path (OriginalLineLoad.joined_execution (bounds s).core (bounds s).flags)
  have pb := pb.transfer program [0x2e29a,0x2e3c1] load_agrees (fun pc h => active pc (by rw [load_agrees pc h]; exact h))
  have tail : X86Routine.run program [0x2e29a,0x2e3c1] 0 (result s)=some (result s) := by
    simp only [X86Routine.run]; exact if_pos last
  exact (OriginalGroupBounds.prefix_join pa pb).finish tail 42 (by omega)

@[simp] theorem bounds_reg (s : X86Memory.State) (r : Reg) (h0 : r≠0) (h2 : r≠2) :
    (bounds s).core.regs r=s.regs r := by simp [bounds,horizontal,axis_reg,h0,h2]

def SafeWord (s : X86Memory.State) (a : Word) : Prop :=
  ∀ off∈[(34#32),38,30,26], Apart a (s.regs 3+off)

theorem half_preserved (s : X86Memory.State) (a : Word) (safe : SafeWord s a) :
    load16 (bounds s).core.memory a=load16 s.memory a := by
  have h := congrArg (fun w : Word => w.extractLsb' 0 16) (bounds_frame s a safe)
  simpa only [load32,BitVec.extractLsb'_append_eq_right,load16] using h

def load_source (e : OriginalGroupOutput.Line) (s : X86Memory.State)
    (h : E1M1LineLoad.Source e s)
    (rawFront : SafeWord s (s.regs 1+10)) (rawBack : SafeWord s (s.regs 1+12))
    (base : SafeWord s 0x2c118)
    (frontSide : h.frontIndex≠65535 → SafeWord s (E1M1NoiseGraph.sideAddress h.sides h.frontIndex))
    (backSide : h.backIndex≠65535 → SafeWord s (E1M1NoiseGraph.sideAddress h.sides h.backIndex)) :
    E1M1LineLoad.Source e (bounds s).core := by
  have reg1 := bounds_reg s 1 (by decide) (by decide)
  have reg3 := bounds_reg s 3 (by decide) (by decide)
  refine ⟨h.frontIndex,h.backIndex,h.sides,reg3.trans h.line,
    (bounds_frame s _ base).trans h.base,?_,?_,?_,?_,?_,h.copyBase,h.copyFront,h.copyBack,h.cacheBase,h.cacheBack⟩
  · rw [reg1,half_preserved s _ rawFront]; exact h.frontRead
  · rw [reg1,half_preserved s _ rawBack]; exact h.backRead
  · simpa only [reg1] using h.nextRead
  · simp only [E1M1LineCache.target]; split
    · rename_i absent; simpa only [E1M1LineCache.target,if_pos absent] using h.frontSide
    · rename_i present
      rw [bounds_frame s _ (frontSide present)]
      simpa only [E1M1LineCache.target,if_neg present] using h.frontSide
  · simp only [E1M1LineCache.target]; split
    · rename_i absent; simpa only [E1M1LineCache.target,if_pos absent] using h.backSide
    · rename_i present
      rw [bounds_frame s _ (backSide present)]
      simpa only [E1M1LineCache.target,if_neg present] using h.backSide

/-- Protect every bounding-box word against all later index/cache writes, using
actual field offsets rather than a new separation premise at each call. -/
theorem field_safe (line off : Word) (member : off∈[(34#32),38,30,26]) :
    E1M1LineLoad.CopySafe (line+off) line ∧ Apart (line+off) (line+46) ∧ Apart (line+off) (line+50) := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl
  all_goals refine ⟨⟨?_,?_⟩,?_,?_⟩
  all_goals exact HalfMemory.translate _ _ _ _ _ (by unfold HalfMemory.Separate; decide +kernel)

theorem bounds_survive (s : X86Memory.State) (off : Word) (member : off∈[(34#32),38,30,26]) :
    load32 (result s).core.memory (s.regs 3+off)=load32 (bounds s).core.memory (s.regs 3+off) := by
  obtain ⟨copy,front,back⟩ := field_safe (s.regs 3) off member
  exact E1M1LineLoad.frame (bounds s).core _
    (by simpa only [bounds_reg s 3 (by decide) (by decide)] using copy)
    (by simpa only [bounds_reg s 3 (by decide) (by decide)] using front)
    (by simpa only [bounds_reg s 3 (by decide) (by decide)] using back)

/-- The longer actual suffix preserves bounds and establishes scan inputs, given
raw WAD/side-table relations before bounds are computed. Slope classification is
still an earlier, separate obligation. -/
theorem establishes (e : OriginalGroupOutput.Line) (s : X86Memory.State) (f : Option Flags)
    (h : E1M1LineLoad.Source e s)
    (rawFront : SafeWord s (s.regs 1+10)) (rawBack : SafeWord s (s.regs 1+12))
    (base : SafeWord s 0x2c118)
    (frontSide : h.frontIndex≠65535 → SafeWord s (E1M1NoiseGraph.sideAddress h.sides h.frontIndex))
    (backSide : h.backIndex≠65535 → SafeWord s (E1M1NoiseGraph.sideAddress h.sides h.backIndex)) :
    ∃ out, X86Routine.run program [0x2e29a,0x2e3c1] 42 ⟨s,f,0x2e326⟩=some out ∧
      OriginalGroupOutput.Inputs [e] out.core.memory ∧
      (∀ off∈[(34#32),38,30,26], load32 out.core.memory (e.address+off)=load32 (bounds s).core.memory (e.address+off)) := by
  have source := load_source e s h rawFront rawBack base frontSide backSide
  obtain ⟨out,run,input,_⟩ := E1M1LineLoad.establishes e (bounds s).core (bounds s).flags source
  rw [OriginalLineLoad.joined_execution] at run
  have eq := Option.some.inj run
  subst out
  refine ⟨result s,joined_execution s f,input,?_⟩
  intro off member
  simpa only [h.line] using bounds_survive s off member

end Doom.Proofs.E1M1LineGeometry
