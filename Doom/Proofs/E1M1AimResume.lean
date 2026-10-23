import Doom.Proofs.E1M1AimIteration
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1AimResume
open Verification X86 X86Memory X86Control BlockSummary Collision
attribute [local irreducible] load32 store32

def program : X86Routine.Program := fun pc =>
  match E1M1AimWindow.program pc with
  | some op => some op
  | none => OriginalInterceptGate.program pc

theorem contains_window (pc : Nat) (h : E1M1AimWindow.program pc≠none) :
    program pc=E1M1AimWindow.program pc := by
  unfold program
  cases eq : E1M1AimWindow.program pc <;> simp_all

theorem contains_gate (pc : Nat) (h : OriginalInterceptGate.program pc≠none) :
    program pc=OriginalInterceptGate.program pc := by
  have range : 0x2c85e≤pc ∧ pc<0x2c887 := by
    by_cases inside : 0x2c85e≤pc ∧ pc<0x2c887
    · exact inside
    · simp [OriginalInterceptGate.program,OriginalInterceptGate.bytesProgram,inside] at h
  have all : ∀ i : Fin 41, program (0x2c85e+i.val)=OriginalInterceptGate.program (0x2c85e+i.val) := by decide
  have eq : 0x2c85e+(pc-0x2c85e)=pc := by omega
  simpa only [eq] using all ⟨pc-0x2c85e,by omega⟩

def result (s : X86Memory.State) := OriginalInterceptGate.resumed (E1M1AimWindow.result s).core

/-- Run the open-line callback and its actual enclosing stop/continue branch.
Continuation marks the selected fraction; both paths retain the clipped globals.
The selected-record/global separation is an entry-layout premise. -/
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
    (returnSafe : E1M1AimReturnFrame.Safe s)
    (returnWord : load32 s.memory (s.regs 4)=0x2c86d)
    (markSafe : Apart (0x2c1e4#32) (s.regs 3) ∧ Apart (0x2c1e8#32) (s.regs 3)) :
    (∃ n, n≤144 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2b760⟩ (result s)) ∧
    (result s).pc=(if (if bf=ff then lower.raw else max lower.raw floorSlope.raw).toInt <
      (if fc=bc then upper.raw else min upper.raw ceilingSlope.raw).toInt then 0x2c83a else 0x2c88c) ∧
    (result s).core.regs 4=s.regs 4+(4#32) ∧
    (result s).core.regs 3=s.regs 3 ∧
    ((if bf=ff then lower.raw else max lower.raw floorSlope.raw).toInt <
      (if fc=bc then upper.raw else min upper.raw ceilingSlope.raw).toInt →
      load32 (result s).core.memory (s.regs 3)=0x7fffffff) ∧
    load32 (result s).core.memory (0x2c1e4#32)=(if bf=ff then lower.raw else max lower.raw floorSlope.raw).toBitVec ∧
    load32 (result s).core.memory (0x2c1e8#32)=(if fc=bc then upper.raw else min upper.raw ceilingSlope.raw).toBitVec := by
  have run := E1M1AimWindow.execution s f hit line front back ff fc bf bc distance z lower upper floorSlope ceilingSlope h distanceReads floorReads reads clip range eye bottom top pass floorOk ceilingOk returnSafe
  obtain ⟨n,hn,p⟩ := run.1
  have p := p.transfer program [] contains_window (by simp)
  have pc : (E1M1AimWindow.result s).pc=0x2c86d := by rw [run.2.2.2.1,returnWord]; rfl
  have q := (X86CodeMemory.lift_success (OriginalInterceptGate.resume_execution (E1M1AimWindow.result s).core
    (E1M1AimWindow.result s).flags) FloorCaller.cm).transfer program [] contains_gate (by simp)
  rw [OriginalPathXStep.at_pc _ _ pc] at q
  have bound : OriginalInterceptGate.resumeSteps (E1M1AimWindow.result s).core≤5 := by
    unfold OriginalInterceptGate.resumeSteps; split <;> omega
  refine ⟨⟨_,by omega,E1M1PspriteStep.prefix_trans p q⟩,?_⟩
  have eax := run.2.1
  have sp := run.2.2.1
  have ebx := run.2.2.2.2.2.2.2.2.2.1
  have bounds := run.2.2.2.2.2.2.2.2.2.2
  by_cases go : (if bf=ff then lower.raw else max lower.raw floorSlope.raw).toInt <
    (if fc=bc then upper.raw else min upper.raw ceilingSlope.raw).toInt
  · simp only [go,↓reduceIte] at eax ⊢
    simp [result,OriginalInterceptGate.resumed,OriginalInterceptGate.marked,OriginalInterceptGate.restored,
      eax,put,write,sp,ebx,load_store,load_store_apart _ _ _ _ markSafe.1,
      load_store_apart _ _ _ _ markSafe.2,bounds]
  · simp only [go,↓reduceIte] at eax ⊢
    simp [result,OriginalInterceptGate.resumed,OriginalInterceptGate.restored,eax,put,write,sp,ebx,bounds]
end Doom.Proofs.E1M1AimResume
