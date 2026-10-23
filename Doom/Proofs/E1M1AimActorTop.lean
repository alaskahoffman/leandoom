import Doom.Proofs.OriginalAimActorTop
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimActorTop
open Verification X86 X86Memory X86Control BlockSummary Collision
attribute [local irreducible] load32 store32

def program : X86Routine.Program := fun pc =>
  match OriginalAimActorTop.program pc with
  | some op => some op
  | none => E1M1AimActorSkip.program pc

theorem contains_top (pc : Nat) (h : OriginalAimActorTop.program pc≠none) :
    program pc=OriginalAimActorTop.program pc := by
  unfold program; cases eq : OriginalAimActorTop.program pc <;> simp_all

theorem contains_skip (pc : Nat) (h : E1M1AimActorSkip.program pc≠none) :
    program pc=E1M1AimActorSkip.program pc := by
  have absent : OriginalAimActorTop.program pc=none := by
    by_cases inside : 0x2b843≤pc ∧ pc<0x2b875
    · have all : ∀ i : Fin 50, E1M1AimActorSkip.program (0x2b843+i.val)=none := by decide
      have eq : 0x2b843+(pc-0x2b843)=pc := by omega
      exact False.elim (h (by simpa only [eq] using all ⟨pc-0x2b843,by omega⟩))
    · simp [OriginalAimActorTop.program,OriginalAimActorTop.bytesProgram,inside]
  simp [program,absent]

theorem contains_division (pc : Nat) (h : OriginalDivMemory.program pc≠none) :
    program pc=OriginalDivMemory.program pc := by
  have inside : 0x1d180≤pc ∧ pc<0x1d1c1 := by
    by_cases hn : 0x1d180≤pc ∧ pc<0x1d1c1
    · exact hn
    · exact False.elim (h (by simp [OriginalDivMemory.program,OriginalDivMemory.bytesProgram,hn]))
  have all : ∀ i : Fin 65, program (0x1d180+i.val)=OriginalDivMemory.program (0x1d180+i.val) := by decide
  have eq : 0x1d180+(pc-0x1d180)=pc := by omega
  simpa only [eq] using all ⟨pc-0x1d180,by omega⟩

def call := OriginalAimActorTop.called
def divided (s : X86Memory.State) := OriginalDivMemory.result (call s)
def result (s : X86Memory.State) := OriginalAimActorTop.gate (divided s).core

def ReadSafe (s : X86Memory.State) (a : Word) : Prop :=
  ∀ off∈[(4#32),8,12,16], Apart a (s.regs 4-off)

theorem call_fields (s : X86Memory.State) :
    (call s).regs 4=s.regs 4-4 ∧
    (call s).memory=store32 s.memory (s.regs 4-4) 0x2b869 := by
  simp [call,OriginalAimActorTop.called,OriginalAimActorTop.argument,OriginalAimActorTop.den,
    OriginalAimActorTop.top,OriginalAimActorTop.e,OriginalAimActorTop.v,OriginalAimActorTop.h,
    OriginalAimActorTop.d,OriginalAimActorTop.shifted,OriginalAimDistance.shifted,multiply,
    OriginalAimDistance.inputs,OriginalAimDistance.first,X86Routine.pushWord,put,X86.write,eax,edx]

theorem returned (s : X86Memory.State) : (divided s).pc=0x2b869 := by
  rw [divided,(OriginalDivMemory.restored_registers (call s)).2.2.2.2]
  rw [(call_fields s).1,(call_fields s).2,load_store]; rfl

/-- All protected words survive the real CALL and FixedDiv's three saves. -/
theorem frame (s : X86Memory.State) (a : Word) (safe : ReadSafe s a) :
    load32 (result s).core.memory a=load32 s.memory a := by
  have sp := (call_fields s).1
  have saves : ∀ off∈[(4#32),8,12], Apart a ((call s).regs 4-off) := by
    intro off member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl <;> rw [sp] <;>
      simpa only [BitVec.sub_sub,show (4#32)+4=8 from rfl,show (4#32)+8=12 from rfl,
        show (4#32)+12=16 from rfl] using safe _ (by simp)
  change load32 (divided s).core.memory a=_
  rw [divided,OriginalDivMemory.result_frame (call s) a saves,(call_fields s).2,
    load_store_apart _ _ _ _ (safe 4 (by simp))]

/-- Reuse the proved FixedDiv correspondence for the actor's wrapped numerator
and computed distance. Successful source arithmetic discharges IDIV safety. -/
theorem division_success (s : X86Memory.State) (range frac targetZ targetHeight shootZ slope : Fixed)
    (r : OriginalAimDistance.range s=range.raw.toBitVec)
    (f : OriginalAimDistance.fraction s=frac.raw.toBitVec)
    (z0 : OriginalAimActorTop.z s=targetZ.raw.toBitVec)
    (ht : OriginalAimActorTop.height s=targetHeight.raw.toBitVec)
    (eye0 : OriginalAimActorTop.eye s=shootZ.raw.toBitVec)
    (ok : checkedPathDiv (targetZ+targetHeight-shootZ) (range*frac)=.ok slope) :
    OriginalDivMemory.Safe (call s) ∧ (divided s).core.regs 0=slope.raw.toBitVec := by
  have operands := OriginalAimActorTop.operands s range frac targetZ targetHeight shootZ r f z0 ht eye0
  have num : (⟨Int32.ofBitVec ((call s).regs 0)⟩ : Fixed)=targetZ+targetHeight-shootZ := by rw [call,operands.1]; simp
  have den : (⟨Int32.ofBitVec ((call s).regs 2)⟩ : Fixed)=range*frac := by rw [call,operands.2.1]; simp
  have fixed : Fixed.divChecked (targetZ+targetHeight-shootZ) (range*frac)=.ok slope := by
    unfold checkedPathDiv at ok
    cases he : Fixed.divChecked (targetZ+targetHeight-shootZ) (range*frac) <;> simp_all [Except.mapError]
  have safe := OriginalDivMemory.safe_of_fixed_success (call s) (by rw [num,den,fixed]; rfl)
  have value := OriginalDivMemory.result_matches_fixed (call s) safe
  rw [num,den,fixed] at value
  simp only [Except.toOption,Option.map_some,Option.some.injEq] at value
  exact ⟨safe,value.symm⟩

/-- Eligible actor top slope through actual division RET and signed lower-window
comparison. Equality is admitted; a strictly lower top takes the skip branch. -/
theorem execution (s : X86Memory.State) (f : Option Flags)
    (range frac targetZ targetHeight shootZ lower slope : Fixed)
    (r : OriginalAimDistance.range s=range.raw.toBitVec)
    (fraction : OriginalAimDistance.fraction s=frac.raw.toBitVec)
    (z0 : OriginalAimActorTop.z s=targetZ.raw.toBitVec)
    (ht : OriginalAimActorTop.height s=targetHeight.raw.toBitVec)
    (eye0 : OriginalAimActorTop.eye s=shootZ.raw.toBitVec)
    (bound : load32 s.memory (0x2c1e4#32)=lower.raw.toBitVec)
    (safe : ReadSafe s (0x2c1e4#32))
    (ok : checkedPathDiv (targetZ+targetHeight-shootZ) (range*frac)=.ok slope) :
    (∃ n≤41, X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2b843⟩ (result s)) ∧
    (result s).pc=(if slope.raw<lower.raw then 0x2b875 else 0x2b881) ∧
    (result s).core.regs 6=slope.raw.toBitVec ∧ (result s).core.regs 7=slope.raw.toBitVec ∧
    (result s).core.regs 3=(range*frac).raw.toBitVec ∧
    (result s).core.regs 1=s.regs 1 ∧ (result s).core.regs 4=s.regs 4 ∧
    load32 (result s).core.memory (0x2c1e4#32)=lower.raw.toBitVec := by
  have success := division_success s range frac targetZ targetHeight shootZ slope r fraction z0 ht eye0 ok
  have first := (OriginalAimActorTop.call_execution s f).transfer program [] contains_top (by simp)
  obtain ⟨n,hn,mid⟩ := OriginalDivMemory.execution_path (call s) none success.1
  have mid := mid.transfer program [] contains_division (by simp)
  have tail := (OriginalAimActorTop.gate_execution (divided s).core (divided s).flags).transfer
    program [] contains_top (by simp)
  rw [OriginalPathXStep.at_pc _ _ (returned s)] at tail
  have run := X86CodeMemory.lift_success (OriginalGroupBounds.prefix_join
    (OriginalGroupBounds.prefix_join first mid) tail) FloorCaller.cm
  have operands := OriginalAimActorTop.operands s range frac targetZ targetHeight shootZ r fraction z0 ht eye0
  have regs := OriginalDivMemory.restored_registers (call s)
  have low : OriginalAimActorTop.lower (divided s).core=lower.raw.toBitVec :=
    (frame s _ safe).trans bound
  refine ⟨⟨12+n+4,by omega,run⟩,?_,?_,?_,?_,?_,?_,(frame s _ safe).trans bound⟩
  · simp only [result,OriginalAimActorTop.gate,success.2,low,Int32.toInt_toBitVec,← Int32.lt_iff_toInt_lt]
  · simp [result,OriginalAimActorTop.gate,OriginalAimActorTop.slopes,OriginalAimActorTop.savedSlope,put,X86.write,success.2]
  · simp [result,OriginalAimActorTop.gate,OriginalAimActorTop.slopes,OriginalAimActorTop.savedSlope,put,X86.write,success.2]
  · simpa [result,divided,OriginalAimActorTop.gate,OriginalAimActorTop.slopes,OriginalAimActorTop.savedSlope,put,X86.write] using regs.2.2.1.trans operands.2.2.1
  · simpa [result,divided,OriginalAimActorTop.gate,OriginalAimActorTop.slopes,OriginalAimActorTop.savedSlope,put,X86.write] using regs.2.1.trans operands.2.2.2.1
  · simpa [result,divided,OriginalAimActorTop.gate,OriginalAimActorTop.slopes,OriginalAimActorTop.savedSlope,put,X86.write,
      (call_fields s).1,BitVec.sub_add_cancel] using regs.2.2.2.1
end Doom.Proofs.E1M1AimActorTop
