import Doom.Proofs.OriginalAimDistance
import Doom.Proofs.E1M1AimMapped
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1AimDistance
open Verification X86 X86Memory X86Control BlockSummary Collision
attribute [local irreducible] load32 store32

def program : X86Routine.Program := fun pc =>
  match OriginalAimDistance.program pc with
  | some op => some op
  | none => E1M1AimOpening.program pc

theorem contains_distance (pc : Nat) (h : OriginalAimDistance.program pc≠none) :
    program pc=OriginalAimDistance.program pc := by
  unfold program
  cases eq : OriginalAimDistance.program pc <;> simp_all

theorem contains_opening (pc : Nat) (h : E1M1AimOpening.program pc≠none) :
    program pc=E1M1AimOpening.program pc := by
  have absent : OriginalAimDistance.program pc=none := by
    by_cases inside : 0x2b797≤pc ∧ pc<0x2b7a6
    · have all : ∀ i : Fin 15, E1M1AimOpening.program (0x2b797+i.val)=none := by decide
      have eq : 0x2b797+(pc-0x2b797)=pc := by omega
      exact False.elim (h (by simpa only [eq] using all ⟨pc-0x2b797,by omega⟩))
    · simp [OriginalAimDistance.program,OriginalAimDistance.bytesProgram,inside]
  simp [program,absent]

def ReadSafe (s : X86Memory.State) : Prop :=
  E1M1NoiseLedger.Protect [s.regs 0,(0x2b9b8#32)] (E1M1AimOpeningFrame.writes (s.regs 4))
def result (s : X86Memory.State) : X86Control.State :=
  ⟨OriginalAimDistance.result (E1M1AimOpeningFrame.result s).core,none,0x2b7a6⟩

/-- The exact fraction and range used by the next multiplication come from
callback-entry memory, surviving every prologue and opening-helper write. -/
theorem operands (s : X86Memory.State) (hit : Intercept) (line : Word) (distance : Fixed)
    (record : OriginalLineFinish.RecordAt s.memory (s.regs 0) hit line)
    (helperSafe : E1M1AimOpening.CallerSafe s) (reads : ReadSafe s)
    (range : load32 s.memory (0x2b9b8#32)=distance.raw.toBitVec) :
    OriginalAimDistance.range (E1M1AimOpeningFrame.result s).core=distance.raw.toBitVec ∧
    OriginalAimDistance.fraction (E1M1AimOpeningFrame.result s).core=hit.frac.raw.toBitVec := by
  constructor
  · change load32 (E1M1AimOpeningFrame.result s).core.memory (0x2b9b8#32)=_
    rw [E1M1AimOpeningFrame.output_frame s _ (reads _ (by simp)),range]
  · unfold OriginalAimDistance.fraction
    rw [(E1M1AimOpeningFrame.output_regs s helperSafe).1]
    rw [E1M1AimOpeningFrame.output_frame s _ (reads _ (by simp))]
    exact record.1

/-- Open two-sided hit: execute continuously from callback entry through the
real opening CALL/RET, then the original distance product. All images and
separations are at callback entry; no reached arithmetic operands are assumed. -/
theorem execution (s : X86Memory.State) (f : Option Flags) (hit : Intercept)
    (line front back ff fc bf bc : Word) (distance : Fixed)
    (h : E1M1AimMapped.Inputs s hit line front back ff fc bf bc)
    (reads : ReadSafe s) (range : load32 s.memory (0x2b9b8#32)=distance.raw.toBitVec)
    (pass : (if ff.toInt≤bf.toInt then bf else ff).toInt <
      (if bc.toInt≤fc.toInt then bc else fc).toInt) :
    (∃ n, n≤53 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2b760⟩ (result s)) ∧
    (result s).core.regs 0=(distance*hit.frac).raw.toBitVec ∧
    (result s).core.regs 2=(distance*hit.frac).raw.toBitVec ∧
    (result s).pc=0x2b7a6 ∧
    (result s).core.memory=(E1M1AimOpeningFrame.result s).core.memory := by
  have run := E1M1AimMapped.execution s f hit line front back ff fc bf bc h
  have pc : (E1M1AimOpeningFrame.result s).pc=0x2b797 := by
    rw [run.2,if_neg (by omega)]
  obtain ⟨n,hn,p⟩ := run.1
  have p := p.transfer program [] contains_opening (by simp)
  have q := (X86CodeMemory.lift_success (OriginalAimDistance.execution
    (E1M1AimOpeningFrame.result s).core (E1M1AimOpeningFrame.result s).flags) FloorCaller.cm).transfer
    program [] contains_distance (by simp)
  rw [OriginalPathXStep.at_pc _ _ pc] at q
  have inputs := operands s hit line distance h.record h.helperSafe reads range
  have arithmetic := OriginalAimDistance.arithmetic (E1M1AimOpeningFrame.result s).core distance hit.frac inputs.1 inputs.2
  exact ⟨⟨n+5,by omega,E1M1PspriteStep.prefix_trans p q⟩,arithmetic.1,arithmetic.2.1,rfl,arithmetic.2.2.1⟩
end Doom.Proofs.E1M1AimDistance
