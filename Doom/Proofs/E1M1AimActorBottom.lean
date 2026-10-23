import Doom.Proofs.OriginalAimActorBottom
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1AimActorBottom
open Verification X86 X86Memory X86Control BlockSummary Collision
attribute [local irreducible] load32 store32

def program : X86Routine.Program := fun pc =>
  match OriginalAimActorBottom.program pc with
  | some op => some op
  | none => E1M1AimActorReject.program pc

theorem contains_bottom (pc : Nat) (h : OriginalAimActorBottom.program pc≠none) :
    program pc=OriginalAimActorBottom.program pc := by
  unfold program; cases eq : OriginalAimActorBottom.program pc <;> simp_all

theorem contains_prior (pc : Nat) (h : E1M1AimActorReject.program pc≠none) :
    program pc=E1M1AimActorReject.program pc := by
  have absent : OriginalAimActorBottom.program pc=none := by
    by_cases inside : 0x2b881≤pc ∧ pc<0x2b89d
    · have all : ∀ i : Fin 28, E1M1AimActorReject.program (0x2b881+i.val)=none := by decide
      have eq : 0x2b881+(pc-0x2b881)=pc := by omega
      exact False.elim (h (by simpa only [eq] using all ⟨pc-0x2b881,by omega⟩))
    · simp [OriginalAimActorBottom.program,OriginalAimActorBottom.bytesProgram,inside]
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

def call := OriginalAimActorBottom.called
def divided (s : X86Memory.State) := OriginalDivMemory.result (call s)
def result (s : X86Memory.State) := OriginalAimActorBottom.gate (divided s).core

def ReadSafe (s : X86Memory.State) (a : Word) : Prop :=
  ∀ off∈[(4#32),8,12,16], Apart a (s.regs 4-off)

theorem call_fields (s : X86Memory.State) :
    (call s).regs 4=s.regs 4-4 ∧
    (call s).memory=store32 s.memory (s.regs 4-4) 0x2b893 := by
  simp [call,OriginalAimActorBottom.called,OriginalAimActorBottom.argument,OriginalAimActorBottom.subtracted,
    OriginalAimActorBottom.loaded,OriginalAimActorBottom.eyeLoaded,X86Routine.pushWord,put,X86.write]

theorem returned (s : X86Memory.State) : (divided s).pc=0x2b893 := by
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

/-- The original division helper leaves EDI intact as well as restoring ESI. -/
theorem division_edi (s : X86Memory.State) : (OriginalDivMemory.result s).core.regs 7=s.regs 7 := by
  unfold OriginalDivMemory.result OriginalDivMemory.body
  split <;> simp [OriginalDivMemory.restored,OriginalDivMemory.divided,OriginalDivMemory.saturated,
    OriginalDivMemory.guarded,put,write,OriginalDivMemory.saved_reg]

/-- Successful source bottom division supplies machine IDIV safety. -/
theorem division_success (s : X86Memory.State) (distance targetZ shootZ slope : Fixed)
    (dist : s.regs 3=distance.raw.toBitVec)
    (z0 : OriginalAimActorBottom.z s=targetZ.raw.toBitVec)
    (eye0 : OriginalAimActorBottom.eye s=shootZ.raw.toBitVec)
    (ok : checkedPathDiv (targetZ-shootZ) distance=.ok slope) :
    OriginalDivMemory.Safe (call s) ∧ (divided s).core.regs 0=slope.raw.toBitVec := by
  have operands := OriginalAimActorBottom.operands s distance targetZ shootZ dist z0 eye0
  have num : (⟨Int32.ofBitVec ((call s).regs 0)⟩ : Fixed)=targetZ-shootZ := by rw [call,operands.1]; simp
  have den : (⟨Int32.ofBitVec ((call s).regs 2)⟩ : Fixed)=distance := by rw [call,operands.2.1]; simp
  have fixed : Fixed.divChecked (targetZ-shootZ) distance=.ok slope := by
    unfold checkedPathDiv at ok
    cases he : Fixed.divChecked (targetZ-shootZ) distance <;> simp_all [Except.mapError]
  have safe := OriginalDivMemory.safe_of_fixed_success (call s) (by rw [num,den,fixed]; rfl)
  have value := OriginalDivMemory.result_matches_fixed (call s) safe
  rw [num,den,fixed] at value
  simp only [Except.toOption,Option.map_some,Option.some.injEq] at value
  exact ⟨safe,value.symm⟩

/-- Bottom slope through real division RET and the signed upper-window test.
Both saved top-slope copies survive; EBX now holds the upper bound. -/
theorem execution (s : X86Memory.State) (f : Option Flags)
    (distance targetZ shootZ upper slope : Fixed)
    (dist : s.regs 3=distance.raw.toBitVec)
    (z0 : OriginalAimActorBottom.z s=targetZ.raw.toBitVec)
    (eye0 : OriginalAimActorBottom.eye s=shootZ.raw.toBitVec)
    (bound : load32 s.memory (0x2c1e8#32)=upper.raw.toBitVec)
    (safe : ReadSafe s (0x2c1e8#32))
    (ok : checkedPathDiv (targetZ-shootZ) distance=.ok slope) :
    (∃ n≤33, X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2b881⟩ (result s)) ∧
    (result s).pc=(if upper.raw<slope.raw then 0x2b89d else 0x2b8a9) ∧
    (result s).core.regs 0=slope.raw.toBitVec ∧ (result s).core.regs 3=upper.raw.toBitVec ∧
    (result s).core.regs 6=s.regs 6 ∧ (result s).core.regs 7=s.regs 7 ∧
    (result s).core.regs 1=s.regs 1 ∧ (result s).core.regs 4=s.regs 4 ∧
    load32 (result s).core.memory (0x2c1e8#32)=upper.raw.toBitVec := by
  have success := division_success s distance targetZ shootZ slope dist z0 eye0 ok
  have first := (OriginalAimActorBottom.call_execution s f).transfer program [] contains_bottom (by simp)
  obtain ⟨n,hn,mid⟩ := OriginalDivMemory.execution_path (call s) none success.1
  have mid := mid.transfer program [] contains_division (by simp)
  have tail := (OriginalAimActorBottom.gate_execution (divided s).core (divided s).flags).transfer
    program [] contains_bottom (by simp)
  rw [OriginalPathXStep.at_pc _ _ (returned s)] at tail
  have run := X86CodeMemory.lift_success (OriginalGroupBounds.prefix_join
    (OriginalGroupBounds.prefix_join first mid) tail) FloorCaller.cm
  have operands := OriginalAimActorBottom.operands s distance targetZ shootZ dist z0 eye0
  have regs := OriginalDivMemory.restored_registers (call s)
  have up : OriginalAimActorBottom.upper (divided s).core=upper.raw.toBitVec :=
    (frame s _ safe).trans bound
  refine ⟨⟨5+n+3,by omega,run⟩,?_,?_,?_,?_,?_,?_,?_,(frame s _ safe).trans bound⟩
  · simp only [result,OriginalAimActorBottom.gate,success.2,up,Int32.toInt_toBitVec,← Int32.lt_iff_toInt_lt]
  · simpa [result,OriginalAimActorBottom.gate,OriginalAimActorBottom.loadedUpper,put,write] using success.2
  · simp [result,OriginalAimActorBottom.gate,OriginalAimActorBottom.loadedUpper,put,write,up]
  · simpa [result,divided,OriginalAimActorBottom.gate,OriginalAimActorBottom.loadedUpper,put,write] using regs.1.trans operands.2.2.2.1
  · simpa [result,divided,OriginalAimActorBottom.gate,OriginalAimActorBottom.loadedUpper,put,write] using (division_edi (call s)).trans operands.2.2.2.2.1
  · simpa [result,divided,OriginalAimActorBottom.gate,OriginalAimActorBottom.loadedUpper,put,write] using regs.2.1.trans operands.2.2.1
  · simpa [result,divided,OriginalAimActorBottom.gate,OriginalAimActorBottom.loadedUpper,put,write,
      (call_fields s).1,BitVec.sub_add_cancel] using regs.2.2.2.1
end Doom.Proofs.E1M1AimActorBottom
