import Doom.Proofs.OriginalAimWindow
import Doom.Proofs.E1M1AimReturnFrame
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1AimWindow
open Verification X86 X86Memory X86Control BlockSummary Collision
attribute [local irreducible] load32 store32

def program : X86Routine.Program := fun pc =>
  match OriginalAimWindow.program pc with
  | some op => some op
  | none => E1M1AimCeiling.program pc

theorem contains_window (pc : Nat) (h : OriginalAimWindow.program pc≠none) :
    program pc=OriginalAimWindow.program pc := by
  unfold program; cases eq : OriginalAimWindow.program pc <;> simp_all

theorem contains_ceiling (pc : Nat) (h : E1M1AimCeiling.program pc≠none) :
    program pc=E1M1AimCeiling.program pc := by
  have absent : OriginalAimWindow.program pc=none := by
    by_cases a : 0x2b800≤pc ∧ pc<0x2b81a
    · have all : ∀ i : Fin 26, E1M1AimCeiling.program (0x2b800+i.val)=none := by decide
      have eq : 0x2b800+(pc-0x2b800)=pc := by omega
      exact False.elim (h (by simpa only [eq] using all ⟨pc-0x2b800,by omega⟩))
    · by_cases b : 0x2b89d≤pc ∧ pc<0x2b8a9
      · have all : ∀ i : Fin 12, E1M1AimCeiling.program (0x2b89d+i.val)=none := by decide
        have eq : 0x2b89d+(pc-0x2b89d)=pc := by omega
        exact False.elim (h (by simpa only [eq] using all ⟨pc-0x2b89d,by omega⟩))
      · simp [OriginalAimWindow.program,OriginalAimWindow.bytesProgram,a,b]
  simp [program,absent]

def result (s : X86Memory.State) := OriginalAimWindow.result (E1M1AimCeilingEntry.result s).core

theorem restored (s : X86Memory.State) (hit : Intercept) (line front back ff fc bf bc : Word)
    (h : E1M1AimMapped.Inputs s hit line front back ff fc bf bc)
    (safe : E1M1AimReturnFrame.Safe s) :
    (result s).core.regs 4=s.regs 4+(4#32) ∧
    (result s).pc=(load32 s.memory (s.regs 4)).toNat ∧
    (result s).core.regs 5=s.regs 5 ∧ (result s).core.regs 7=s.regs 7 ∧
    (result s).core.regs 6=s.regs 6 ∧ (result s).core.regs 2=s.regs 2 ∧
    (result s).core.regs 1=s.regs 1 ∧ (result s).core.regs 3=s.regs 3 := by
  have sp := E1M1AimReturnFrame.stack s hit line front back ff fc bf bc h
  have slots (off : Word) (member : off∈E1M1AimReturnFrame.slots) :=
    E1M1AimReturnFrame.saved_slot s hit line front back ff fc bf bc off h safe member
  have values := E1M1AimReturnFrame.saved_values s
  have fields := OriginalAimWindow.result_fields (E1M1AimCeilingEntry.result s).core
  have regs := OriginalAimWindow.result_saved_regs (E1M1AimCeilingEntry.result s).core
  have ret : load32 (E1M1AimCeilingEntry.result s).core.memory (s.regs 4)=
      load32 (OriginalAimGuard.saved s).memory (s.regs 4) := by
    simpa only [show (0 : Word)=(0#32) from rfl,BitVec.sub_zero] using slots 0 (by simp [E1M1AimReturnFrame.slots])
  rw [E1M1AimWall.saved_frame s _ (E1M1AimWall.return_safe _)] at ret
  constructor
  · simpa [result,sp,BitVec.sub_eq_add_neg,BitVec.add_assoc] using fields.2.1
  constructor
  · simpa [result,sp,BitVec.sub_add_cancel,ret] using fields.2.2.2
  have keep (off : Word) (member : off∈E1M1AimReturnFrame.slots) :
      load32 (E1M1AimCeilingEntry.result s).core.memory (s.regs 4+(-off))=
      load32 (OriginalAimGuard.saved s).memory (s.regs 4+(-off)) := by
    simpa only [BitVec.sub_eq_add_neg] using slots off member
  simp only [sp,BitVec.sub_eq_add_neg,BitVec.add_assoc] at regs values
  simp only [show -(24#32)+(4#32)=-(20#32) from rfl, show -(24#32)+(8#32)=-(16#32) from rfl, show -(24#32)+(12#32)=-(12#32) from rfl, show -(24#32)+(16#32)=-(8#32) from rfl, show -(24#32)+(20#32)=-(4#32) from rfl] at regs
  rw [keep (24#32) (by simp [E1M1AimReturnFrame.slots]),keep (20#32) (by simp [E1M1AimReturnFrame.slots]),
    keep (16#32) (by simp [E1M1AimReturnFrame.slots]),keep (12#32) (by simp [E1M1AimReturnFrame.slots]),
    keep (8#32) (by simp [E1M1AimReturnFrame.slots]),keep (4#32) (by simp [E1M1AimReturnFrame.slots])] at regs
  rw [values.1,values.2.1,values.2.2.1,values.2.2.2.1,values.2.2.2.2.1,values.2.2.2.2.2] at regs
  exact regs

/-- Continuous two-sided open-portal callback, including the original signed
window decision, six restores and actual RET on both boolean outcomes. -/
theorem execution (s : X86Memory.State) (f : Option Flags) (hit : Intercept)
    (line front back ff fc bf bc : Word) (distance z lower upper floorSlope ceilingSlope : Fixed)
    (h : E1M1AimMapped.Inputs s hit line front back ff fc bf bc)
    (distanceReads : E1M1AimDistance.ReadSafe s) (floorReads : E1M1AimFloorEntry.ReadSafe s)
    (reads : E1M1AimCeilingEntry.ReadSafe s) (clip : E1M1AimCeilingEntry.ClipSafe s line front back)
    (range : load32 s.memory (0x2b9b8#32)=distance.raw.toBitVec)
    (eye : load32 s.memory (0x2b9a8#32)=z.raw.toBitVec)
    (bottom : load32 s.memory (0x2c1e4#32)=lower.raw.toBitVec)
    (top : load32 s.memory (0x2c1e8#32)=upper.raw.toBitVec)
    (pass : (if ff.toInt≤bf.toInt then bf else ff).toInt < (if bc.toInt≤fc.toInt then bc else fc).toInt)
    (floorOk : bf≠ff → checkedPathDiv (⟨Int32.ofBitVec (if ff.toInt≤bf.toInt then bf else ff)⟩-z)
      (distance*hit.frac)=.ok floorSlope)
    (ceilingOk : fc≠bc → checkedPathDiv (⟨Int32.ofBitVec (if bc.toInt≤fc.toInt then bc else fc)⟩-z)
      (distance*hit.frac)=.ok ceilingSlope)
    (returnSafe : E1M1AimReturnFrame.Safe s) :
    (∃ n, n≤139 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2b760⟩ (result s)) ∧
    (result s).core.regs 0=(if (if bf=ff then lower.raw else max lower.raw floorSlope.raw).toInt <
      (if fc=bc then upper.raw else min upper.raw ceilingSlope.raw).toInt then 1 else 0) ∧
    (result s).core.regs 4=s.regs 4+(4#32) ∧
    (result s).pc=(load32 s.memory (s.regs 4)).toNat ∧
    (result s).core.regs 5=s.regs 5 ∧ (result s).core.regs 7=s.regs 7 ∧
    (result s).core.regs 6=s.regs 6 ∧ (result s).core.regs 2=s.regs 2 ∧
    (result s).core.regs 1=s.regs 1 ∧ (result s).core.regs 3=s.regs 3 ∧
    load32 (result s).core.memory (0x2c1e4#32)=(if bf=ff then lower.raw else max lower.raw floorSlope.raw).toBitVec ∧
    load32 (result s).core.memory (0x2c1e8#32)=(if fc=bc then upper.raw else min upper.raw ceilingSlope.raw).toBitVec := by
  have pre := E1M1AimCeilingEntry.execution s f hit line front back ff fc bf bc distance z lower upper floorSlope ceilingSlope h distanceReads floorReads reads clip range eye bottom top pass floorOk ceilingOk
  obtain ⟨n,hn,p⟩ := pre.1
  have p := p.transfer program [] contains_ceiling (by simp)
  have q := (X86CodeMemory.lift_success (OriginalAimWindow.execution (E1M1AimCeilingEntry.result s).core
    (E1M1AimCeilingEntry.result s).flags) FloorCaller.cm).transfer program [] contains_window (by simp)
  rw [OriginalPathXStep.at_pc _ _ pre.2.1] at q
  have fields := OriginalAimWindow.result_fields (E1M1AimCeilingEntry.result s).core
  have restored := restored s hit line front back ff fc bf bc h returnSafe
  constructor
  · exact ⟨n+11,by omega,E1M1PspriteStep.prefix_trans p q⟩
  constructor
  · simpa only [result,OriginalAimWindow.lower,OriginalAimWindow.upper,pre.2.2.1,pre.2.2.2,Int32.toInt_toBitVec] using fields.1
  refine ⟨restored.1,restored.2.1,restored.2.2.1,restored.2.2.2.1,restored.2.2.2.2.1,
    restored.2.2.2.2.2.1,restored.2.2.2.2.2.2.1,restored.2.2.2.2.2.2.2,?_⟩
  change load32 (OriginalAimWindow.result (E1M1AimCeilingEntry.result s).core).core.memory _=_ ∧
    load32 (OriginalAimWindow.result (E1M1AimCeilingEntry.result s).core).core.memory _=_
  rw [fields.2.2.1]
  exact pre.2.2
end Doom.Proofs.E1M1AimWindow
