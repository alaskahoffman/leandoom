import Doom.Proofs.E1M1LineCache
import Doom.Proofs.HalfMemory
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalLineLoad
open Verification X86 X86Memory X86Control BlockSummary
def copyBytes : List UInt8 := [0x66,0x8b,0x41,0xa,0x66,0x89,0x43,0x16,0x66,0x8b,0x41,0xc,0x66,0x89,0x43,0x18]
def advanceBytes : List UInt8 := [0x8b,0x35,0x34,0xc1,0x2,0x0,0x45,0x83,0xc1,0xe,0x83,0xc3,0x3e,0x39,0xf5,0xf,0x8c,0xd9,0xfe,0xff,0xff]
def bytesProgram (copy advance : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2e358≤pc ∧ pc<0x2e368 then X86Routine.decodeAt copy (pc-0x2e358)
  else if 0x2e3ac≤pc ∧ pc<0x2e3c1 then X86Routine.decodeAt advance (pc-0x2e3ac) else none
def localProgram := bytesProgram copyBytes advanceBytes
def listed : X86Routine.Program
  | 0x2e358 => some (.loadHalf 0 ⟨some 1,none,0,10⟩,4)
  | 0x2e35c => some (.storeHalf ⟨some 3,none,0,22⟩ 0,4)
  | 0x2e360 => some (.loadHalf 0 ⟨some 1,none,0,12⟩,4)
  | 0x2e364 => some (.storeHalf ⟨some 3,none,0,24⟩ 0,4)
  | 0x2e3ac => some (.control (.block (.load 6 ⟨none,none,0,0x2c134⟩)),6)
  | 0x2e3b2 => some (.addImmediate 5 1,1)
  | 0x2e3b3 => some (.addImmediate 1 14,3)
  | 0x2e3b6 => some (.addImmediate 3 62,3)
  | 0x2e3b9 => some (.compareRegisters 5 6,2)
  | 0x2e3bb => some (.jumpSigned 3 (-295),6)
  | _ => none
theorem decoded (pc : Nat) (h : listed pc≠none) : localProgram pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

/-- A 16-bit MOV retains the upper half of EAX and does not change flags. -/
def ax (old : Word) (v : BitVec 16) : Word := (old &&& 0xffff0000) ||| v.zeroExtend 32
def first (s : X86Memory.State) : BitVec 16 := load16 s.memory (s.regs 1+10)
def firstMemory (s : X86Memory.State) : Memory := X86Routine.store16 s.memory (s.regs 3+22) (first s)
/-- The second source is read AFTER the first destination has been written. -/
def second (s : X86Memory.State) : BitVec 16 := load16 (firstMemory s) (s.regs 1+12)
def copied (s : X86Memory.State) : X86Memory.State :=
  {put s 0 (ax (ax (s.regs 0) (first s)) (second s)) with
    memory := X86Routine.store16 (firstMemory s) (s.regs 3+24) (second s)}
def advanced (s : X86Memory.State) : X86Control.State :=
  let t := put s 6 (load32 s.memory 0x2c134)
  let t := put t 5 (s.regs 5+1)
  let t := put t 1 (s.regs 1+14)
  let t := put t 3 (s.regs 3+62)
  ⟨t,some (compare32 (s.regs 5+1) (load32 s.memory 0x2c134)),
    if (s.regs 5+1).toInt<(load32 s.memory 0x2c134).toInt then 0x2e29a else 0x2e3c1⟩

@[simp] theorem ax_low (old : Word) (v : BitVec 16) : (ax old v).extractLsb' 0 16=v := by
  simp [ax,BitVec.extractLsb'_or,BitVec.extractLsb'_and,BitVec.extractLsb'_setWidth_of_le (show 0+16≤32 from by decide)]
private theorem low_ax (old : Word) (v : BitVec 16) :
    ((old &&& (0xffff0000#32)) ||| v.zeroExtend 32).extractLsb' 0 16=v := ax_low old v
@[local simp] private theorem step_2e358 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e368] (n+1) ⟨s,f,0x2e358⟩ =
      (X86Routine.execute (.loadHalf 0 ⟨some 1,none,0,10⟩) ⟨s,f,0x2e35c⟩).bind (X86Routine.run listed [0x2e368] n) := by rfl
@[local simp] private theorem step_2e35c (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e368] (n+1) ⟨s,f,0x2e35c⟩ =
      (X86Routine.execute (.storeHalf ⟨some 3,none,0,22⟩ 0) ⟨s,f,0x2e360⟩).bind (X86Routine.run listed [0x2e368] n) := by rfl
@[local simp] private theorem step_2e360 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e368] (n+1) ⟨s,f,0x2e360⟩ =
      (X86Routine.execute (.loadHalf 0 ⟨some 1,none,0,12⟩) ⟨s,f,0x2e364⟩).bind (X86Routine.run listed [0x2e368] n) := by rfl
@[local simp] private theorem step_2e364 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e368] (n+1) ⟨s,f,0x2e364⟩ =
      (X86Routine.execute (.storeHalf ⟨some 3,none,0,24⟩ 0) ⟨s,f,0x2e368⟩).bind (X86Routine.run listed [0x2e368] n) := by rfl
@[local simp] private theorem stop_2e368 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e368] n ⟨s,f,0x2e368⟩=some ⟨s,f,0x2e368⟩ := by cases n <;> rfl
theorem copy_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run localProgram [0x2e368] 4 ⟨s,f,0x2e358⟩=some (⟨copied s,f,0x2e368⟩) := by
  have run : X86Routine.run listed [0x2e368] 4 ⟨s,f,0x2e358⟩=some (⟨copied s,f,0x2e368⟩) := by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      X86Block.Address.eval,X86.execute,blockPreservesFlags,copied,firstMemory,first,second,advanced,
      ax,low_ax,PlayerArmor.cmp_lt,put,write,BitVec.add_assoc,-BitVec.toInt_add]
    all_goals
      funext r
      by_cases h : r=0 <;> simp [write,h]
  rw [X86Routine.run_sound localProgram listed decoded _ _ _ (by rw [run]; simp),run]
@[local simp] private theorem step_2e3ac (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e29a,0x2e3c1] (n+1) ⟨s,f,0x2e3ac⟩ =
      (X86Routine.execute (.control (.block (.load 6 ⟨none,none,0,0x2c134⟩))) ⟨s,f,0x2e3b2⟩).bind (X86Routine.run listed [0x2e29a,0x2e3c1] n) := by rfl
@[local simp] private theorem step_2e3b2 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e29a,0x2e3c1] (n+1) ⟨s,f,0x2e3b2⟩ =
      (X86Routine.execute (.addImmediate 5 1) ⟨s,f,0x2e3b3⟩).bind (X86Routine.run listed [0x2e29a,0x2e3c1] n) := by rfl
@[local simp] private theorem step_2e3b3 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e29a,0x2e3c1] (n+1) ⟨s,f,0x2e3b3⟩ =
      (X86Routine.execute (.addImmediate 1 14) ⟨s,f,0x2e3b6⟩).bind (X86Routine.run listed [0x2e29a,0x2e3c1] n) := by rfl
@[local simp] private theorem step_2e3b6 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e29a,0x2e3c1] (n+1) ⟨s,f,0x2e3b6⟩ =
      (X86Routine.execute (.addImmediate 3 62) ⟨s,f,0x2e3b9⟩).bind (X86Routine.run listed [0x2e29a,0x2e3c1] n) := by rfl
@[local simp] private theorem step_2e3b9 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e29a,0x2e3c1] (n+1) ⟨s,f,0x2e3b9⟩ =
      (X86Routine.execute (.compareRegisters 5 6) ⟨s,f,0x2e3bb⟩).bind (X86Routine.run listed [0x2e29a,0x2e3c1] n) := by rfl
@[local simp] private theorem step_2e3bb (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e29a,0x2e3c1] (n+1) ⟨s,f,0x2e3bb⟩ =
      (X86Routine.execute (.jumpSigned 3 (-295)) ⟨s,f,0x2e3c1⟩).bind (X86Routine.run listed [0x2e29a,0x2e3c1] n) := by rfl
@[local simp] private theorem stop_2e29a (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e29a,0x2e3c1] n ⟨s,f,0x2e29a⟩=some ⟨s,f,0x2e29a⟩ := by cases n <;> rfl
@[local simp] private theorem stop_2e3c1 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e29a,0x2e3c1] n ⟨s,f,0x2e3c1⟩=some ⟨s,f,0x2e3c1⟩ := by cases n <;> rfl
theorem advance_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run localProgram [0x2e29a,0x2e3c1] 6 ⟨s,f,0x2e3ac⟩=some (advanced s) := by
  have run : X86Routine.run listed [0x2e29a,0x2e3c1] 6 ⟨s,f,0x2e3ac⟩=some (advanced s) := by
    have opposite : (load32 s.memory (0x2c134#32)).toInt≤(s.regs 5+(1#32)).toInt ↔
        ¬(s.regs 5+(1#32)).toInt<(load32 s.memory (0x2c134#32)).toInt := by omega
    by_cases less : (s.regs 5+(1#32)).toInt<(load32 s.memory (0x2c134#32)).toInt
    all_goals simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      X86Block.Address.eval,X86.execute,blockPreservesFlags,copied,firstMemory,first,second,advanced,
      PlayerHeight.cmp_ge_prop,opposite,less,put,write,BitVec.add_assoc,-BitVec.toInt_add]
  rw [X86Routine.run_sound localProgram listed decoded _ _ _ (by rw [run]; simp),run]

/-- The linked program retains each separately pinned slice's decoder. -/
def joinedBytes (copy cache advance : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2e368≤pc ∧ pc<0x2e3ac then OriginalLineCache.bytesProgram cache pc
  else bytesProgram copy advance pc
def program := joinedBytes copyBytes OriginalLineCache.cacheBytes advanceBytes

theorem cache_agrees (pc : Nat) (h : OriginalLineCache.program pc≠none) :
    program pc=OriginalLineCache.program pc := by
  have inside : 0x2e368≤pc ∧ pc<0x2e3ac := by
    by_cases yes : 0x2e368≤pc ∧ pc<0x2e3ac
    · exact yes
    · simp [OriginalLineCache.program,OriginalLineCache.bytesProgram,yes] at h
  simp [program,joinedBytes,inside,OriginalLineCache.program]
theorem local_agrees (pc : Nat) (h : localProgram pc≠none) :
    program pc=localProgram pc := by
  have outside : ¬(0x2e368≤pc ∧ pc<0x2e3ac) := by
    intro inside
    have a : ¬(0x2e358≤pc ∧ pc<0x2e368) := by omega
    have b : ¬(0x2e3ac≤pc ∧ pc<0x2e3c1) := by omega
    simp [localProgram,bytesProgram,a,b] at h
  simp [program,joinedBytes,outside,localProgram]

def result (s : X86Memory.State) : X86Control.State :=
  advanced (OriginalLineCache.result (copied s)).core

/-- All three segments execute without resetting the machine state. The loop
edge returns to geometry, not directly to the index-copy suffix proved here. -/
theorem joined_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x2e29a,0x2e3c1] 26 ⟨s,f,0x2e358⟩=some (result s) := by
  have active (pc : Nat) (h : program pc≠none) : pc∉[0x2e29a,0x2e3c1] := by
    intro member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl <;> exact h (by decide)
  obtain ⟨a,ha,pa,_⟩ := X86Routine.run_path (copy_execution s f)
  have pa := pa.transfer program [0x2e29a,0x2e3c1] local_agrees (fun pc h => active pc (by rw [local_agrees pc h]; exact h))
  obtain ⟨b,hb,pb,_⟩ := X86Routine.run_path (OriginalLineCache.joined_execution (copied s) f)
  have pb := pb.transfer program [0x2e29a,0x2e3c1] cache_agrees (fun pc h => active pc (by rw [cache_agrees pc h]; exact h))
  obtain ⟨c,hc,pc,last⟩ := X86Routine.run_path (advance_execution (OriginalLineCache.result (copied s)).core (OriginalLineCache.result (copied s)).flags)
  have pc := pc.transfer program [0x2e29a,0x2e3c1] local_agrees (fun pc h => active pc (by rw [local_agrees pc h]; exact h))
  have tail : X86Routine.run program [0x2e29a,0x2e3c1] 0 (result s)=some (result s) := by
    simp only [X86Routine.run]
    exact if_pos last
  exact (OriginalGroupBounds.prefix_join pa (OriginalGroupBounds.prefix_join pb pc)).finish tail 26 (by omega)

@[simp] theorem copied_reg (s : X86Memory.State) (r : Reg) (h : r≠0) :
    (copied s).regs r=s.regs r := by simp [copied,put,write,h]

/-- Both exact halfword destinations remain correct, even with wrapping addresses. -/
theorem copied_indices (s : X86Memory.State) :
    load16 (copied s).memory (s.regs 3+22)=first s ∧
    load16 (copied s).memory (s.regs 3+24)=second s := by
  have apart : HalfMemory.Separate 2 2 (s.regs 3+22) (s.regs 3+24) :=
    HalfMemory.translate _ _ _ _ _ (by unfold HalfMemory.Separate; decide +kernel)
  change load16 (X86Routine.store16 (firstMemory s) (s.regs 3+24) (second s)) (s.regs 3+22)=_ ∧ _
  rw [HalfMemory.half_frame _ _ _ _ apart]
  exact ⟨HalfMemory.readback _ _ _,HalfMemory.readback _ _ _⟩

theorem copied_frame (s : X86Memory.State) (a : Word)
    (hf : HalfMemory.Separate 4 2 a (s.regs 3+22))
    (hb : HalfMemory.Separate 4 2 a (s.regs 3+24)) :
    load32 (copied s).memory a=load32 s.memory a := by
  change load32 (X86Routine.store16 (firstMemory s) (s.regs 3+24) (second s)) a=_
  rw [HalfMemory.word_frame _ _ _ _ hb]
  exact HalfMemory.word_frame _ _ _ _ hf

/-- The advance preserves memory and advances each pointer by its actual record
stride. Its signed branch uses the count loaded after all preceding stores. -/
theorem progress (s : X86Memory.State) :
    (result s).core.memory=(OriginalLineCache.result (copied s)).core.memory ∧
    (result s).core.regs 1=s.regs 1+14 ∧
    (result s).core.regs 3=s.regs 3+62 ∧
    (result s).core.regs 5=s.regs 5+1 := by
  simp [result,advanced,OriginalLineCache.result,OriginalLineCache.front,
    OriginalLineCache.cached_reg,copied_reg,put,write]

end Doom.Proofs.OriginalLineLoad
