import Doom.Proofs.E1M1AimCeiling
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1AimCeilingEntry
open Verification X86 X86Memory X86Control BlockSummary Collision
attribute [local irreducible] load32 store32

def reached (s : X86Memory.State) := (E1M1AimFloorEntry.result s).core
def result (s : X86Memory.State) := E1M1AimCeiling.result (reached s)
def ReadSafe (s : X86Memory.State) : Prop :=
  E1M1NoiseLedger.Protect [(0x2b9a8#32),(0x2c1e8#32)] (E1M1AimOpeningFrame.writes (s.regs 4))
def ClipSafe (s : X86Memory.State) (line front back : Word) : Prop :=
  E1M1NoiseLedger.Protect [line+(46#32),line+(50#32),front+(4#32),back+(4#32),
    (0x2c034#32),(0x2b9a8#32),(0x2c1e8#32)] (E1M1AimClipFrame.writes (s.regs 4-(24#32)))

/-- Transport the ceiling operands across the completed floor branch. -/
theorem inputs (s : X86Memory.State) (hit : Intercept) (line front back ff fc bf bc : Word)
    (h : E1M1AimMapped.Inputs s hit line front back ff fc bf bc)
    (clip : ClipSafe s line front back) (reads : ReadSafe s) :
    OriginalAimCeiling.fc (reached s)=fc ∧ OriginalAimCeiling.bc (reached s)=bc ∧
    OriginalAimCeiling.high (reached s)=(if bc.toInt≤fc.toInt then bc else fc) ∧
    OriginalAimCeiling.shootZ (reached s)=load32 s.memory (0x2b9a8#32) ∧
    OriginalAimCeiling.old (reached s)=load32 s.memory (0x2c1e8#32) ∧
    (reached s).regs 4=s.regs 4-(24#32) ∧
    (reached s).regs 3=(E1M1AimFloorEntry.reached s).regs 0 := by
  have floorImage := E1M1AimFloorEntry.inputs s hit line front back ff fc bf bc h
  have floorRegs := E1M1AimClipFrame.floor_regs (E1M1AimFloorEntry.reached s)
  have keep (a : Word) (ha : a∈[line+(46#32),line+(50#32),front+(4#32),back+(4#32),
      (0x2c034#32),(0x2b9a8#32),(0x2c1e8#32)]) :
      load32 (reached s).memory a=load32 (E1M1AimOpeningFrame.result s).core.memory a := by
    rw [show (reached s).memory=(E1M1AimFloor.result (E1M1AimFloorEntry.reached s)).core.memory from rfl]
    rw [E1M1AimClipFrame.floor_frame]
    · rw [E1M1AimFloorEntry.memory]
    · simpa only [floorImage.2.2.2] using clip a ha
  have oldMap (a : Word) (ha : a∈E1M1OpeningHeights.reads line front back) :=
    E1M1AimOpeningFrame.output_frame s a (h.mapSafe a ha)
  have arg := E1M1AimOpeningFrame.line_argument s hit line h.record h.pointerSafe
  have img := E1M1AimOpeningFrame.transport s line front back ff fc bf bc h.mapSafe h.image
  have safe := E1M1AimOpeningFrame.helper_safe s line front back arg.2 h.mapSafe
  have heights := E1M1OpeningHeights.heights (E1M1AimOpeningFrame.helper s) front back ff fc bf bc safe
    (by simpa only [arg.2] using img.side) (by simpa only [arg.2] using img.frontPtr)
    (by simpa only [arg.2] using img.backPtr) img.frontFloor img.frontCeiling img.backFloor img.backCeiling
  have localSafe : E1M1AimOpening.Safe (E1M1AimOpeningFrame.caller s) := by
    simpa [E1M1AimOpening.Safe,E1M1AimOpening.CallerSafe,(E1M1AimOpeningFrame.stack s).1,BitVec.sub_sub] using h.helperSafe
  have regs := E1M1AimOpening.helper_return (E1M1AimOpeningFrame.caller s) localSafe
  have ecx : (E1M1AimOpeningFrame.result s).core.regs 1=line := by
    simpa [E1M1AimOpeningFrame.result,E1M1AimOpening.result,OriginalAimOpening.gate,OriginalAimOpening.loaded,put,write,arg.1] using regs.2.1
  have r1 : (reached s).regs 1=line := by
    rw [show (reached s).regs 1=(E1M1AimFloor.result (E1M1AimFloorEntry.reached s)).core.regs 1 from rfl,floorRegs.1]
    simpa [E1M1AimFloorEntry.reached,E1M1AimDistance.result,OriginalAimDistance.result,OriginalAimDistance.shifted,multiply,OriginalAimDistance.inputs,OriginalAimDistance.first,put,write,eax,edx,ebx] using ecx
  constructor
  · simp only [OriginalAimCeiling.fc,OriginalAimCeiling.front,r1]
    rw [keep (line+(46#32)) (by simp),oldMap _ (by simp [E1M1OpeningHeights.reads]),h.image.frontPtr]
    rw [keep (front+(4#32)) (by simp),oldMap _ (by simp [E1M1OpeningHeights.reads]),h.image.frontCeiling]
  constructor
  · simp only [OriginalAimCeiling.bc,OriginalAimCeiling.back,r1]
    rw [keep (line+(50#32)) (by simp),oldMap _ (by simp [E1M1OpeningHeights.reads]),h.image.backPtr]
    rw [keep (back+(4#32)) (by simp),oldMap _ (by simp [E1M1OpeningHeights.reads]),h.image.backCeiling]
  constructor
  · unfold OriginalAimCeiling.high
    rw [keep _ (by simp)]
    simpa only [E1M1AimOpeningFrame.result,E1M1AimOpening.result,OriginalAimOpening.gate,OriginalAimOpening.loaded,put,E1M1AimOpening.opened,E1M1AimOpeningFrame.helper] using heights.1
  constructor
  · unfold OriginalAimCeiling.shootZ
    rw [keep _ (by simp),E1M1AimOpeningFrame.output_frame s _ (reads _ (by simp))]
  constructor
  · unfold OriginalAimCeiling.old
    rw [keep _ (by simp),E1M1AimOpeningFrame.output_frame s _ (reads _ (by simp))]
  exact ⟨floorRegs.2.1.trans floorImage.2.2.2,floorRegs.2.2⟩

theorem upper_safe (s : X86Memory.State) (line front back : Word)
    (sp : (reached s).regs 4=s.regs 4-(24#32)) (safe : ClipSafe s line front back) :
    E1M1AimCeiling.UpperSafe (reached s) := by
  intro off member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl <;> rw [sp] <;> apply safe (0x2c1e8#32) (by simp) <;>
    simp [E1M1AimClipFrame.writes]

/-- Both clipping operations joined from callback entry, with no intermediate
arithmetic operands assumed. Source division success remains conditional. -/
theorem execution (s : X86Memory.State) (f : Option Flags) (hit : Intercept)
    (line front back ff fc bf bc : Word) (distance z lower upper floorSlope ceilingSlope : Fixed)
    (h : E1M1AimMapped.Inputs s hit line front back ff fc bf bc)
    (distanceReads : E1M1AimDistance.ReadSafe s) (floorReads : E1M1AimFloorEntry.ReadSafe s)
    (reads : ReadSafe s) (clip : ClipSafe s line front back)
    (range : load32 s.memory (0x2b9b8#32)=distance.raw.toBitVec)
    (eye : load32 s.memory (0x2b9a8#32)=z.raw.toBitVec)
    (bottom : load32 s.memory (0x2c1e4#32)=lower.raw.toBitVec)
    (top : load32 s.memory (0x2c1e8#32)=upper.raw.toBitVec)
    (pass : (if ff.toInt≤bf.toInt then bf else ff).toInt < (if bc.toInt≤fc.toInt then bc else fc).toInt)
    (floorOk : bf≠ff → checkedPathDiv (⟨Int32.ofBitVec (if ff.toInt≤bf.toInt then bf else ff)⟩-z)
      (distance*hit.frac)=.ok floorSlope)
    (ceilingOk : fc≠bc → checkedPathDiv (⟨Int32.ofBitVec (if bc.toInt≤fc.toInt then bc else fc)⟩-z)
      (distance*hit.frac)=.ok ceilingSlope) :
    (∃ n, n≤128 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1AimCeiling.program [] n ⟨s,f,0x2b760⟩ (result s)) ∧
    (result s).pc=0x2b800 ∧
    load32 (result s).core.memory (0x2c1e4#32)=(if bf=ff then lower.raw else max lower.raw floorSlope.raw).toBitVec ∧
    load32 (result s).core.memory (0x2c1e8#32)=(if fc=bc then upper.raw else min upper.raw ceilingSlope.raw).toBitVec := by
  have pre := E1M1AimFloorEntry.execution s f hit line front back ff fc bf bc distance z lower floorSlope h distanceReads floorReads range eye bottom pass floorOk
  have image := inputs s hit line front back ff fc bf bc h clip reads
  have dist := (E1M1AimDistance.execution s f hit line front back ff fc bf bc distance h distanceReads range pass).2.1
  have division (different : fc≠bc) := E1M1AimCeiling.division_success (reached s)
    ⟨Int32.ofBitVec (if bc.toInt≤fc.toInt then bc else fc)⟩ z (distance*hit.frac) ceilingSlope
    (by simpa using image.2.2.1) (image.2.2.2.1.trans eye) (image.2.2.2.2.2.2.trans dist) (ceilingOk different)
  have safe : E1M1AimCeiling.Safe (reached s) := by
    intro different; apply (division _).1; simpa only [image.1,image.2.1] using different
  obtain ⟨n,hn,p⟩ := pre.1
  have p := p.transfer E1M1AimCeiling.program [] E1M1AimCeiling.contains_floor (by simp)
  obtain ⟨m,hm,q⟩ := E1M1AimCeiling.execution (reached s) (E1M1AimFloorEntry.result s).flags safe
  have q := X86CodeMemory.lift_success q FloorCaller.cm
  change X86CodeMemory.Prefix FloorCaller.cm E1M1AimCeiling.program [] m
    ⟨(E1M1AimFloorEntry.result s).core,(E1M1AimFloorEntry.result s).flags,0x2b7d1⟩ _ at q
  rw [OriginalPathXStep.at_pc _ _ pre.2.1] at q
  constructor
  · exact ⟨n+m,by omega,E1M1PspriteStep.prefix_trans p q⟩
  constructor
  · unfold result E1M1AimCeiling.result
    split <;> simp_all [OriginalAimCeiling.gate,OriginalAimCeiling.clipped]
  constructor
  · change load32 (E1M1AimCeiling.result (reached s)).core.memory _=_
    rw [E1M1AimCeiling.frame]
    · exact pre.2.2
    · intro a ha
      simp only [E1M1AimCeiling.writes,List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl|rfl
      all_goals first
        | exact (by unfold Apart; decide : Apart (0x2c1e4#32) (0x2c1e8#32))
        | rw [image.2.2.2.2.2.1]; apply floorReads (0x2c1e4#32) (by simp); simp [E1M1AimOpeningFrame.writes,E1M1AimOpeningFrame.pushes,BitVec.sub_sub]
  · have updated := E1M1AimCeiling.upper_update (reached s) ceilingSlope (upper_safe s line front back image.2.2.2.2.2.1 clip) (by
      intro different; apply (division _).2; simpa only [image.1,image.2.1] using different)
    rw [image.1,image.2.1,image.2.2.2.2.1,top,Int32.toInt_toBitVec] at updated
    change load32 (E1M1AimCeiling.result (reached s)).core.memory _=_
    rw [updated]
    by_cases same : fc=bc
    · simp [same]
    · simp [same,min,minOfLe,Int32.le_iff_toInt_le,apply_ite]
      split <;> intro impossible <;> omega
end Doom.Proofs.E1M1AimCeilingEntry
