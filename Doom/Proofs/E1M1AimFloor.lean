import Doom.Proofs.OriginalAimFloor
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1AimFloor
open Verification X86 X86Memory X86Control BlockSummary Collision
attribute [local irreducible] load32 store32

def program : X86Routine.Program := fun pc =>
  match OriginalAimFloor.program pc with
  | some op => some op
  | none => match E1M1AimDistance.program pc with
    | some op => some op
    | none => OriginalDivMemory.program pc

theorem contains_floor (pc : Nat) (h : OriginalAimFloor.program pc≠none) :
    program pc=OriginalAimFloor.program pc := by
  unfold program; cases eq : OriginalAimFloor.program pc <;> simp_all

theorem contains_distance (pc : Nat) (h : E1M1AimDistance.program pc≠none) :
    program pc=E1M1AimDistance.program pc := by
  have absent : OriginalAimFloor.program pc=none := by
    by_cases inside : 0x2b7a6≤pc ∧ pc<0x2b7d1
    · have all : ∀ i : Fin 43, E1M1AimDistance.program (0x2b7a6+i.val)=none := by decide
      have eq : 0x2b7a6+(pc-0x2b7a6)=pc := by omega
      exact False.elim (h (by simpa only [eq] using all ⟨pc-0x2b7a6,by omega⟩))
    · simp [OriginalAimFloor.program,OriginalAimFloor.bytesProgram,inside]
  simp [program,absent]; cases eq : E1M1AimDistance.program pc <;> simp_all

theorem contains_division (pc : Nat) (h : OriginalDivMemory.program pc≠none) :
    program pc=OriginalDivMemory.program pc := by
  have inside : 0x1d180≤pc ∧ pc<0x1d1c1 := by
    by_cases hn : 0x1d180≤pc ∧ pc<0x1d1c1
    · exact hn
    · exact False.elim (h (by simp [OriginalDivMemory.program,OriginalDivMemory.bytesProgram,hn]))
  have all : ∀ i : Fin 65, program (0x1d180+i.val)=OriginalDivMemory.program (0x1d180+i.val) := by decide
  have eq : 0x1d180+(pc-0x1d180)=pc := by omega
  simpa only [eq] using all ⟨pc-0x1d180,by omega⟩

def input (s : X86Memory.State) := OriginalAimFloor.c4 s
def call (s : X86Memory.State) := OriginalAimFloor.called (input s)
def divided (s : X86Memory.State) := OriginalDivMemory.result (call s)
def result (s : X86Memory.State) : X86Control.State :=
  if OriginalAimFloor.bf s=OriginalAimFloor.ff s then OriginalAimFloor.gate s
  else OriginalAimFloor.clipped (divided s).core

def Safe (s : X86Memory.State) : Prop :=
  OriginalAimFloor.bf s≠OriginalAimFloor.ff s → OriginalDivMemory.Safe (call s)
def LowerSafe (s : X86Memory.State) : Prop :=
  ∀ off∈[(4#32),8,12,16], Apart (0x2c1e4#32) (s.regs 4-off)

theorem returned (s : X86Memory.State) : (divided s).pc=0x2b7c4 := by
  rw [divided,(OriginalDivMemory.restored_registers (call s)).2.2.2.2]
  simp [call,OriginalAimFloor.called,X86Routine.pushWord,put,write,load_store]

/-- Execute the real floor branch including FixedDiv's saves, body and RET. -/
theorem execution (s : X86Memory.State) (f : Option Flags) (safe : Safe s) :
    ∃ n, n≤37 ∧ X86Routine.Prefix program [] n ⟨s,f,0x2b7a6⟩ (result s) := by
  have gate := (OriginalAimFloor.gate_execution s f).transfer program [] contains_floor (by simp)
  by_cases same : OriginalAimFloor.bf s=OriginalAimFloor.ff s
  · exact ⟨6,by omega,by simpa [result,same] using gate⟩
  · have pc : (OriginalAimFloor.gate s).pc=0x2b7b4 := by simp [OriginalAimFloor.gate,same]
    have invoke := (OriginalAimFloor.call_execution (OriginalAimFloor.gate s).core (OriginalAimFloor.gate s).flags).transfer program [] contains_floor (by simp)
    rw [OriginalPathXStep.at_pc _ _ pc] at invoke
    obtain ⟨n,hn,division⟩ := OriginalDivMemory.execution_path (call s) none (safe same)
    have division := division.transfer program [] contains_division (by simp)
    obtain ⟨m,hm,clip⟩ := OriginalAimFloor.clip_execution (divided s).core (divided s).flags
    have clip := clip.transfer program [] contains_floor (by simp)
    rw [OriginalPathXStep.at_pc _ _ (returned s)] at clip
    exact ⟨6+3+n+m,by omega,by simpa only [result,if_neg same] using
      OriginalGroupBounds.prefix_join (OriginalGroupBounds.prefix_join (OriginalGroupBounds.prefix_join gate invoke) division) clip⟩

/-- The old lower bound survives the CALL and all three helper pushes. -/
theorem lower_preserved (s : X86Memory.State) (safe : LowerSafe s) :
    OriginalAimFloor.old (divided s).core=OriginalAimFloor.old s := by
  have sp : (call s).regs 4=s.regs 4-4 := by
    simp [call,input,OriginalAimFloor.called,OriginalAimFloor.argument,OriginalAimFloor.c4,OriginalAimFloor.c3,OriginalAimFloor.c2,OriginalAimFloor.c1,X86Routine.pushWord,put,write]
  have saves : ∀ off∈[(4#32),8,12], Apart (0x2c1e4#32) ((call s).regs 4-off) := by
    intro off member; simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl <;> rw [sp] <;>
      simpa only [BitVec.sub_sub,show (4#32)+4=8 from rfl,show (4#32)+8=12 from rfl,show (4#32)+12=16 from rfl] using safe _ (by simp)
  unfold OriginalAimFloor.old divided
  rw [OriginalDivMemory.result_frame (call s) _ saves]
  simp only [call,OriginalAimFloor.called,X86Routine.pushWord,put]
  rw [load_store_apart]
  · rfl
  · simpa [input,OriginalAimFloor.argument,OriginalAimFloor.c4,OriginalAimFloor.c3,OriginalAimFloor.c2,OriginalAimFloor.c1,put,write] using safe 4 (by simp)

theorem division_success (s : X86Memory.State) (bottom z distance slope : Fixed)
    (b : OriginalAimFloor.low s=bottom.raw.toBitVec)
    (z0 : OriginalAimFloor.shootZ s=z.raw.toBitVec)
    (d : s.regs 2=distance.raw.toBitVec)
    (ok : checkedPathDiv (bottom-z) distance=.ok slope) :
    OriginalDivMemory.Safe (call s) ∧ (divided s).core.regs 0=slope.raw.toBitVec := by
  have num : (⟨Int32.ofBitVec ((call s).regs 0)⟩ : Fixed)=bottom-z := by
    simp [call,input,OriginalAimFloor.called,OriginalAimFloor.argument,OriginalAimFloor.numerator,OriginalAimFloor.low,OriginalAimFloor.shootZ,OriginalAimFloor.c4,OriginalAimFloor.c3,OriginalAimFloor.c2,OriginalAimFloor.c1,X86Routine.pushWord,put,write] at *
    rw [b,z0]; rfl
  have den : (⟨Int32.ofBitVec ((call s).regs 2)⟩ : Fixed)=distance := by
    simp [call,input,OriginalAimFloor.called,OriginalAimFloor.argument,OriginalAimFloor.c4,OriginalAimFloor.c3,OriginalAimFloor.c2,OriginalAimFloor.c1,X86Routine.pushWord,put,write,d]
  have fixed : Fixed.divChecked (bottom-z) distance=.ok slope := by
    unfold checkedPathDiv at ok
    cases he : Fixed.divChecked (bottom-z) distance <;> simp_all [Except.mapError]
  have safe := OriginalDivMemory.safe_of_fixed_success (call s) (by rw [num,den,fixed]; rfl)
  have value := OriginalDivMemory.result_matches_fixed (call s) safe
  rw [num,den,fixed] at value
  simp only [Except.toOption,Option.map_some,Option.some.injEq] at value
  exact ⟨safe,value.symm⟩

/-- Exact signed lower-window update; equal floors perform no division. -/
theorem lower_update (s : X86Memory.State) (slope : Fixed)
    (safe : LowerSafe s)
    (value : OriginalAimFloor.bf s≠OriginalAimFloor.ff s →
      (divided s).core.regs 0=slope.raw.toBitVec) :
    load32 (result s).core.memory (0x2c1e4#32)=
      if OriginalAimFloor.bf s=OriginalAimFloor.ff s then OriginalAimFloor.old s
      else if slope.raw.toInt≤(OriginalAimFloor.old s).toInt then OriginalAimFloor.old s
      else slope.raw.toBitVec := by
  by_cases same : OriginalAimFloor.bf s=OriginalAimFloor.ff s
  · simp [result,same,OriginalAimFloor.gate,OriginalAimFloor.c4,OriginalAimFloor.c3,OriginalAimFloor.c2,OriginalAimFloor.c1,put,OriginalAimFloor.old]
  · have old := lower_preserved s safe
    simp only [result,if_neg same,OriginalAimFloor.clipped,value same,Int32.toInt_toBitVec,old]
    split <;> simp_all [OriginalAimFloor.raised,OriginalAimFloor.old,load_store,eax]
end Doom.Proofs.E1M1AimFloor
