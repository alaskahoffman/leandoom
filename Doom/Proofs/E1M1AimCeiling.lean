import Doom.Proofs.OriginalAimCeiling
import Doom.Proofs.E1M1AimClipFrame
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1AimCeiling
open Verification X86 X86Memory X86Control BlockSummary Collision
attribute [local irreducible] load32 store32

def program : X86Routine.Program := fun pc =>
  match OriginalAimCeiling.program pc with
  | some op => some op
  | none => match E1M1AimFloor.program pc with
    | some op => some op
    | none => OriginalDivMemory.program pc

theorem contains_ceiling (pc : Nat) (h : OriginalAimCeiling.program pc≠none) :
    program pc=OriginalAimCeiling.program pc := by
  unfold program; cases eq : OriginalAimCeiling.program pc <;> simp_all

theorem contains_floor (pc : Nat) (h : E1M1AimFloor.program pc≠none) :
    program pc=E1M1AimFloor.program pc := by
  have absent : OriginalAimCeiling.program pc=none := by
    by_cases inside : 0x2b7d1≤pc ∧ pc<0x2b800
    · have all : ∀ i : Fin 47, E1M1AimFloor.program (0x2b7d1+i.val)=none := by decide
      have eq : 0x2b7d1+(pc-0x2b7d1)=pc := by omega
      exact False.elim (h (by simpa only [eq] using all ⟨pc-0x2b7d1,by omega⟩))
    · simp [OriginalAimCeiling.program,OriginalAimCeiling.bytesProgram,inside]
  simp [program,absent]; cases eq : E1M1AimFloor.program pc <;> simp_all

theorem contains_division (pc : Nat) (h : OriginalDivMemory.program pc≠none) :
    program pc=OriginalDivMemory.program pc := by
  have inside : 0x1d180≤pc ∧ pc<0x1d1c1 := by
    by_cases hn : 0x1d180≤pc ∧ pc<0x1d1c1
    · exact hn
    · exact False.elim (h (by simp [OriginalDivMemory.program,OriginalDivMemory.bytesProgram,hn]))
  have all : ∀ i : Fin 65, program (0x1d180+i.val)=OriginalDivMemory.program (0x1d180+i.val) := by decide
  have eq : 0x1d180+(pc-0x1d180)=pc := by omega
  simpa only [eq] using all ⟨pc-0x1d180,by omega⟩

def input (s : X86Memory.State) := OriginalAimCeiling.c3 s
def call (s : X86Memory.State) := OriginalAimCeiling.called (input s)
def divided (s : X86Memory.State) := OriginalDivMemory.result (call s)
def result (s : X86Memory.State) : X86Control.State :=
  if OriginalAimCeiling.fc s=OriginalAimCeiling.bc s then OriginalAimCeiling.gate s
  else OriginalAimCeiling.clipped (divided s).core

def Safe (s : X86Memory.State) : Prop :=
  OriginalAimCeiling.fc s≠OriginalAimCeiling.bc s → OriginalDivMemory.Safe (call s)
def UpperSafe (s : X86Memory.State) : Prop :=
  ∀ off∈[(4#32),8,12,16], Apart (0x2c1e8#32) (s.regs 4-off)

theorem returned (s : X86Memory.State) : (divided s).pc=0x2b7f3 := by
  rw [divided,(OriginalDivMemory.restored_registers (call s)).2.2.2.2]
  simp [call,OriginalAimCeiling.called,X86Routine.pushWord,put,write,load_store]

/-- Execute the real ceiling branch including FixedDiv's saves, body and RET. -/
theorem execution (s : X86Memory.State) (f : Option Flags) (safe : Safe s) :
    ∃ n, n≤38 ∧ X86Routine.Prefix program [] n ⟨s,f,0x2b7d1⟩ (result s) := by
  have gate := (OriginalAimCeiling.gate_execution s f).transfer program [] contains_ceiling (by simp)
  by_cases same : OriginalAimCeiling.fc s=OriginalAimCeiling.bc s
  · exact ⟨5,by omega,by simpa [result,same] using gate⟩
  · have pc : (OriginalAimCeiling.gate s).pc=0x2b7df := by simp [OriginalAimCeiling.gate,same]
    have invoke := (OriginalAimCeiling.call_execution (OriginalAimCeiling.gate s).core (OriginalAimCeiling.gate s).flags).transfer program [] contains_ceiling (by simp)
    rw [OriginalPathXStep.at_pc _ _ pc] at invoke
    obtain ⟨n,hn,division⟩ := OriginalDivMemory.execution_path (call s) none (safe same)
    have division := division.transfer program [] contains_division (by simp)
    obtain ⟨m,hm,clip⟩ := OriginalAimCeiling.clip_execution (divided s).core (divided s).flags
    have clip := clip.transfer program [] contains_ceiling (by simp)
    rw [OriginalPathXStep.at_pc _ _ (returned s)] at clip
    exact ⟨5+5+n+m,by omega,by simpa only [result,if_neg same] using
      OriginalGroupBounds.prefix_join (OriginalGroupBounds.prefix_join (OriginalGroupBounds.prefix_join gate invoke) division) clip⟩

/-- The old upper bound survives the CALL and all three helper pushes. -/
theorem upper_preserved (s : X86Memory.State) (safe : UpperSafe s) :
    OriginalAimCeiling.old (divided s).core=OriginalAimCeiling.old s := by
  have sp : (call s).regs 4=s.regs 4-4 := by
    simp [call,input,OriginalAimCeiling.called,OriginalAimCeiling.argument,OriginalAimCeiling.distance,OriginalAimCeiling.eye,OriginalAimCeiling.loaded,OriginalAimCeiling.c3,OriginalAimCeiling.c2,OriginalAimCeiling.c1,X86Routine.pushWord,put,write]
  have saves : ∀ off∈[(4#32),8,12], Apart (0x2c1e8#32) ((call s).regs 4-off) := by
    intro off member; simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl <;> rw [sp] <;>
      simpa only [BitVec.sub_sub,show (4#32)+4=8 from rfl,show (4#32)+8=12 from rfl,show (4#32)+12=16 from rfl] using safe _ (by simp)
  unfold OriginalAimCeiling.old divided
  rw [OriginalDivMemory.result_frame (call s) _ saves]
  simp only [call,OriginalAimCeiling.called,X86Routine.pushWord,put]
  rw [load_store_apart]
  · rfl
  · simpa [input,OriginalAimCeiling.argument,OriginalAimCeiling.distance,OriginalAimCeiling.eye,OriginalAimCeiling.loaded,OriginalAimCeiling.c3,OriginalAimCeiling.c2,OriginalAimCeiling.c1,put,write] using safe 4 (by simp)

theorem division_success (s : X86Memory.State) (top z distance slope : Fixed)
    (b : OriginalAimCeiling.high s=top.raw.toBitVec)
    (z0 : OriginalAimCeiling.shootZ s=z.raw.toBitVec)
    (d : s.regs 3=distance.raw.toBitVec)
    (ok : checkedPathDiv (top-z) distance=.ok slope) :
    OriginalDivMemory.Safe (call s) ∧ (divided s).core.regs 0=slope.raw.toBitVec := by
  have num : (⟨Int32.ofBitVec ((call s).regs 0)⟩ : Fixed)=top-z := by
    simp [call,input,OriginalAimCeiling.called,OriginalAimCeiling.argument,OriginalAimCeiling.distance,OriginalAimCeiling.eye,OriginalAimCeiling.loaded,OriginalAimCeiling.numerator,OriginalAimCeiling.high,OriginalAimCeiling.shootZ,OriginalAimCeiling.c3,OriginalAimCeiling.c2,OriginalAimCeiling.c1,X86Routine.pushWord,put,write] at *
    rw [b,z0]; rfl
  have den : (⟨Int32.ofBitVec ((call s).regs 2)⟩ : Fixed)=distance := by
    simp [call,input,OriginalAimCeiling.called,OriginalAimCeiling.argument,OriginalAimCeiling.distance,OriginalAimCeiling.eye,OriginalAimCeiling.loaded,OriginalAimCeiling.c3,OriginalAimCeiling.c2,OriginalAimCeiling.c1,X86Routine.pushWord,put,write,d]
  have fixed : Fixed.divChecked (top-z) distance=.ok slope := by
    unfold checkedPathDiv at ok
    cases he : Fixed.divChecked (top-z) distance <;> simp_all [Except.mapError]
  have safe := OriginalDivMemory.safe_of_fixed_success (call s) (by rw [num,den,fixed]; rfl)
  have value := OriginalDivMemory.result_matches_fixed (call s) safe
  rw [num,den,fixed] at value
  simp only [Except.toOption,Option.map_some,Option.some.injEq] at value
  exact ⟨safe,value.symm⟩

/-- Exact signed upper-window update; equal ceilings perform no division. -/
theorem upper_update (s : X86Memory.State) (slope : Fixed)
    (safe : UpperSafe s)
    (value : OriginalAimCeiling.fc s≠OriginalAimCeiling.bc s →
      (divided s).core.regs 0=slope.raw.toBitVec) :
    load32 (result s).core.memory (0x2c1e8#32)=
      if OriginalAimCeiling.fc s=OriginalAimCeiling.bc s then OriginalAimCeiling.old s
      else if (OriginalAimCeiling.old s).toInt≤slope.raw.toInt then OriginalAimCeiling.old s
      else slope.raw.toBitVec := by
  by_cases same : OriginalAimCeiling.fc s=OriginalAimCeiling.bc s
  · simp [result,same,OriginalAimCeiling.gate,OriginalAimCeiling.c3,OriginalAimCeiling.c2,OriginalAimCeiling.c1,put,OriginalAimCeiling.old]
  · have old := upper_preserved s safe
    simp only [result,if_neg same,OriginalAimCeiling.clipped,value same,Int32.toInt_toBitVec,old]
    split <;> simp_all [OriginalAimCeiling.lowered,OriginalAimCeiling.old,load_store,eax]
def writes (sp : Word) : List Word := [sp-(4#32),sp-(8#32),sp-(12#32),sp-(16#32),(0x2c1e8#32)]

/-- A reusable frame for all ceiling-branch stores, with wrapping addresses. -/
theorem frame (s : X86Memory.State) (a : Word)
    (safe : ∀ b∈writes (s.regs 4), Apart a b) :
    load32 (E1M1AimCeiling.result s).core.memory a=load32 s.memory a := by
  have sp : (E1M1AimCeiling.call s).regs 4=s.regs 4-(4#32) := by
    simp [E1M1AimCeiling.call,E1M1AimCeiling.input,OriginalAimCeiling.called,OriginalAimCeiling.argument,OriginalAimCeiling.distance,OriginalAimCeiling.eye,OriginalAimCeiling.loaded,OriginalAimCeiling.c3,OriginalAimCeiling.c2,OriginalAimCeiling.c1,X86Routine.pushWord,put,write,BitVec.sub_add_cancel]
  have saves : ∀ off∈[(4#32),8,12], Apart a ((E1M1AimCeiling.call s).regs 4-off) := by
    intro off member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl <;> rw [sp] <;> apply safe <;> simp [writes,BitVec.sub_sub]
  have division : load32 (E1M1AimCeiling.divided s).core.memory a=load32 s.memory a := by
    rw [E1M1AimCeiling.divided,OriginalDivMemory.result_frame _ _ saves]
    simp only [E1M1AimCeiling.call,OriginalAimCeiling.called,X86Routine.pushWord,put]
    rw [load_store_apart]
    · rfl
    · simpa [E1M1AimCeiling.input,OriginalAimCeiling.argument,OriginalAimCeiling.distance,OriginalAimCeiling.eye,OriginalAimCeiling.loaded,OriginalAimCeiling.c3,OriginalAimCeiling.c2,OriginalAimCeiling.c1,put,write] using safe _ (by simp [writes])
  unfold E1M1AimCeiling.result
  split
  · rfl
  · simp only [OriginalAimCeiling.clipped]
    split
    · exact division
    · simp only [OriginalAimCeiling.lowered]
      rw [load_store_apart _ _ _ _ (safe _ (by simp [writes]))]
      exact division
end Doom.Proofs.E1M1AimCeiling
