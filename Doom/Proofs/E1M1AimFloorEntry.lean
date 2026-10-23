import Doom.Proofs.E1M1AimFloor
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1AimFloorEntry
open Verification X86 X86Memory X86Control BlockSummary Collision
attribute [local irreducible] load32 store32

def reached (s : X86Memory.State) := (E1M1AimDistance.result s).core
def result (s : X86Memory.State) := E1M1AimFloor.result (reached s)
def ReadSafe (s : X86Memory.State) : Prop :=
  E1M1NoiseLedger.Protect [(0x2b9a8#32),(0x2c1e4#32)] (E1M1AimOpeningFrame.writes (s.regs 4))

theorem memory (s : X86Memory.State) : (reached s).memory=(E1M1AimOpeningFrame.result s).core.memory := by
  simp only [reached,E1M1AimDistance.result,OriginalAimDistance.result,OriginalAimDistance.shifted,multiply,OriginalAimDistance.inputs,OriginalAimDistance.first,put]

/-- Map words, computed opening bottom, and stack position at the floor branch
are derived from the original callback-entry image. -/
theorem inputs (s : X86Memory.State) (hit : Intercept)
    (line front back ff fc bf bc : Word)
    (h : E1M1AimMapped.Inputs s hit line front back ff fc bf bc) :
    OriginalAimFloor.ff (reached s)=ff ∧ OriginalAimFloor.bf (reached s)=bf ∧
    OriginalAimFloor.low (reached s)=(if ff.toInt≤bf.toInt then bf else ff) ∧
    (reached s).regs 4=s.regs 4-(24#32) := by
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
  have mem := memory s
  have r1 : (reached s).regs 1=line := by
    simpa [reached,E1M1AimDistance.result,OriginalAimDistance.result,OriginalAimDistance.shifted,multiply,OriginalAimDistance.inputs,OriginalAimDistance.first,put,write,eax,edx,ebx] using ecx
  have keep (a : Word) (ha : a∈E1M1OpeningHeights.reads line front back) : load32 (reached s).memory a=load32 s.memory a := by
    rw [mem]; exact E1M1AimOpeningFrame.output_frame s a (h.mapSafe a ha)
  constructor
  · simp only [OriginalAimFloor.ff,OriginalAimFloor.front,r1]
    rw [keep (line+(46#32)) (by simp [E1M1OpeningHeights.reads]),h.image.frontPtr,keep front (by simp [E1M1OpeningHeights.reads]),h.image.frontFloor]
  constructor
  · simp only [OriginalAimFloor.bf,OriginalAimFloor.back,r1]
    rw [keep (line+(50#32)) (by simp [E1M1OpeningHeights.reads]),h.image.backPtr,keep back (by simp [E1M1OpeningHeights.reads]),h.image.backFloor]
  constructor
  · unfold OriginalAimFloor.low
    rw [mem]
    simpa only [E1M1AimOpeningFrame.result,E1M1AimOpening.result,OriginalAimOpening.gate,OriginalAimOpening.loaded,put,E1M1AimOpening.opened,E1M1AimOpeningFrame.helper] using heights.2
  · simpa [reached,E1M1AimDistance.result,OriginalAimDistance.result,OriginalAimDistance.shifted,multiply,OriginalAimDistance.inputs,OriginalAimDistance.first,put,write,eax,edx,ebx] using (E1M1AimOpeningFrame.output_regs s h.helperSafe).2

theorem preserved (s : X86Memory.State) (safe : ReadSafe s) :
    OriginalAimFloor.shootZ (reached s)=load32 s.memory (0x2b9a8#32) ∧
    OriginalAimFloor.old (reached s)=load32 s.memory (0x2c1e4#32) := by
  simp only [OriginalAimFloor.shootZ,OriginalAimFloor.old,memory]
  constructor <;> exact E1M1AimOpeningFrame.output_frame s _ (safe _ (by simp))

theorem lower_safe (s : X86Memory.State) (sp : (reached s).regs 4=s.regs 4-(24#32))
    (safe : ReadSafe s) : E1M1AimFloor.LowerSafe (reached s) := by
  intro off member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl <;> rw [sp] <;>
    apply safe (0x2c1e4#32) (by simp) <;>
    simp [E1M1AimOpeningFrame.writes,E1M1AimOpeningFrame.pushes,BitVec.sub_sub]

/-- Continuous callback entry through floor clipping. Division success is a
source arithmetic premise, needed only when the two floor heights differ. -/
theorem execution (s : X86Memory.State) (f : Option Flags) (hit : Intercept)
    (line front back ff fc bf bc : Word) (distance z lower slope : Fixed)
    (h : E1M1AimMapped.Inputs s hit line front back ff fc bf bc)
    (distanceReads : E1M1AimDistance.ReadSafe s) (reads : ReadSafe s)
    (range : load32 s.memory (0x2b9b8#32)=distance.raw.toBitVec)
    (eye : load32 s.memory (0x2b9a8#32)=z.raw.toBitVec)
    (bound : load32 s.memory (0x2c1e4#32)=lower.raw.toBitVec)
    (pass : (if ff.toInt≤bf.toInt then bf else ff).toInt < (if bc.toInt≤fc.toInt then bc else fc).toInt)
    (ok : bf≠ff → checkedPathDiv (⟨Int32.ofBitVec (if ff.toInt≤bf.toInt then bf else ff)⟩-z)
      (distance*hit.frac)=.ok slope) :
    (∃ n, n≤90 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1AimFloor.program [] n ⟨s,f,0x2b760⟩ (result s)) ∧
    (result s).pc=0x2b7d1 ∧
    load32 (result s).core.memory (0x2c1e4#32)=
      (if bf=ff then lower.raw else max lower.raw slope.raw).toBitVec := by
  have pre := E1M1AimDistance.execution s f hit line front back ff fc bf bc distance h distanceReads range pass
  have image := inputs s hit line front back ff fc bf bc h
  have globals := preserved s reads
  have division (different : bf≠ff) := E1M1AimFloor.division_success (reached s)
    ⟨Int32.ofBitVec (if ff.toInt≤bf.toInt then bf else ff)⟩ z (distance*hit.frac) slope
    (by simpa using image.2.2.1) (globals.1.trans eye) pre.2.1 (ok different)
  have safe : E1M1AimFloor.Safe (reached s) := by
    intro different; apply (division _).1; simpa only [image.1,image.2.1] using different
  obtain ⟨n,hn,p⟩ := pre.1
  have p := p.transfer E1M1AimFloor.program [] E1M1AimFloor.contains_distance (by simp)
  obtain ⟨m,hm,q⟩ := E1M1AimFloor.execution (reached s) none safe
  have q := X86CodeMemory.lift_success q FloorCaller.cm
  constructor
  · exact ⟨n+m,by omega,E1M1PspriteStep.prefix_trans p q⟩
  constructor
  · unfold result E1M1AimFloor.result
    split <;> simp_all [OriginalAimFloor.gate,OriginalAimFloor.clipped]
  · have updated := E1M1AimFloor.lower_update (reached s) slope (lower_safe s image.2.2.2 reads) (by
      intro different; apply (division _).2; simpa only [image.1,image.2.1] using different)
    rw [image.1,image.2.1,globals.2,bound,Int32.toInt_toBitVec] at updated
    change load32 (E1M1AimFloor.result (reached s)).core.memory _=_
    rw [updated]
    by_cases same : bf=ff
    · simp [same]
    · simp [same,max,maxOfLe,Int32.le_iff_toInt_le,apply_ite]
      split
      · intro le
        have eq : lower.raw=slope.raw := Int32.toInt_inj.mp (by omega)
        rw [eq]
      · intro le; omega
end Doom.Proofs.E1M1AimFloorEntry
