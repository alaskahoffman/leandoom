import Doom.Proofs.OriginalGroupOutput
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalLineCache
open Verification X86 X86Memory X86Control BlockSummary
def cacheBytes : List UInt8 := [0xf,0xbf,0x43,0x16,0x83,0xf8,0xff,0x74,0x12,0x6b,0xc0,0x12,0x8b,0x15,0x18,0xc1,0x2,0x0,0x8b,0x44,0x2,0xe,0x89,0x43,0x2e,0xeb,0x7,0xc7,0x43,0x2e,0x0,0x0,0x0,0x0,0xf,0xbf,0x43,0x18,0x83,0xf8,0xff,0x74,0x12,0x6b,0xc0,0x12,0x8b,0x15,0x18,0xc1,0x2,0x0,0x8b,0x44,0x2,0xe,0x89,0x43,0x32,0xeb,0x7,0xc7,0x43,0x32,0x0,0x0,0x0,0x0]
def bytesProgram (cache : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2e368≤pc ∧ pc<0x2e3ac then X86Routine.decodeAt cache (pc-0x2e368) else none
def program := bytesProgram cacheBytes
def listed : X86Routine.Program
  | 0x2e368 => some (.control (.block (.legacy (.movsx16 0 3 22))),4)
  | 0x2e36c => some (.compareRegister 0 0xffffffff,3)
  | 0x2e36f => some (.control (.jumpZero true 18),2)
  | 0x2e371 => some (.multiplyImmediate 0 0 18,3)
  | 0x2e374 => some (.control (.block (.load 2 ⟨none,none,0,0x2c118⟩)),6)
  | 0x2e37a => some (.control (.block (.load 0 ⟨some 2,some 0,0,14⟩)),4)
  | 0x2e37e => some (.control (.block (.store ⟨some 3,none,0,46⟩ 0)),3)
  | 0x2e381 => some (.jump 7,2)
  | 0x2e383 => some (.storeImmediate ⟨some 3,none,0,46⟩ 0,7)
  | 0x2e38a => some (.control (.block (.legacy (.movsx16 0 3 24))),4)
  | 0x2e38e => some (.compareRegister 0 0xffffffff,3)
  | 0x2e391 => some (.control (.jumpZero true 18),2)
  | 0x2e393 => some (.multiplyImmediate 0 0 18,3)
  | 0x2e396 => some (.control (.block (.load 2 ⟨none,none,0,0x2c118⟩)),6)
  | 0x2e39c => some (.control (.block (.load 0 ⟨some 2,some 0,0,14⟩)),4)
  | 0x2e3a0 => some (.control (.block (.store ⟨some 3,none,0,50⟩ 0)),3)
  | 0x2e3a3 => some (.jump 7,2)
  | 0x2e3a5 => some (.storeImmediate ⟨some 3,none,0,50⟩ 0,7)
  | _ => none
theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

/-- Signed index and side pointer are read from the incoming memory of EACH branch. -/
def index (s : X86Memory.State) (off : Word) : Word :=
  (load16 s.memory (s.regs 3+off)).signExtend 32
def value (s : X86Memory.State) (off : Word) : Word :=
  if index s off=0xffffffff then 0
  else load32 s.memory (load32 s.memory 0x2c118 + index s off*18 + 14)
def cached (s : X86Memory.State) (off dest : Word) (pc : Nat) : X86Control.State :=
  let t := if index s off=0xffffffff then put s 0 (index s off)
    else put (put s 2 (load32 s.memory 0x2c118)) 0 (value s off)
  ⟨{t with memory := store32 s.memory (s.regs 3+dest) (value s off)},
    if index s off=0xffffffff then some (compare32 (index s off) 0xffffffff) else none,pc⟩
def front (s : X86Memory.State) := cached s 22 46 0x2e38a
/-- In particular, the back-side lookup sees the preceding front-pointer store. -/
def result (s : X86Memory.State) := cached (front s).core 24 50 0x2e3ac
@[local simp] private theorem step_2e368 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e38a] (n+1) ⟨s,f,0x2e368⟩ =
      (X86Routine.execute (.control (.block (.legacy (.movsx16 0 3 22)))) ⟨s,f,0x2e36c⟩).bind (X86Routine.run listed [0x2e38a] n) := by rfl
@[local simp] private theorem step_2e36c (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e38a] (n+1) ⟨s,f,0x2e36c⟩ =
      (X86Routine.execute (.compareRegister 0 0xffffffff) ⟨s,f,0x2e36f⟩).bind (X86Routine.run listed [0x2e38a] n) := by rfl
@[local simp] private theorem step_2e36f (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e38a] (n+1) ⟨s,f,0x2e36f⟩ =
      (X86Routine.execute (.control (.jumpZero true 18)) ⟨s,f,0x2e371⟩).bind (X86Routine.run listed [0x2e38a] n) := by rfl
@[local simp] private theorem step_2e371 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e38a] (n+1) ⟨s,f,0x2e371⟩ =
      (X86Routine.execute (.multiplyImmediate 0 0 18) ⟨s,f,0x2e374⟩).bind (X86Routine.run listed [0x2e38a] n) := by rfl
@[local simp] private theorem step_2e374 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e38a] (n+1) ⟨s,f,0x2e374⟩ =
      (X86Routine.execute (.control (.block (.load 2 ⟨none,none,0,0x2c118⟩))) ⟨s,f,0x2e37a⟩).bind (X86Routine.run listed [0x2e38a] n) := by rfl
@[local simp] private theorem step_2e37a (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e38a] (n+1) ⟨s,f,0x2e37a⟩ =
      (X86Routine.execute (.control (.block (.load 0 ⟨some 2,some 0,0,14⟩))) ⟨s,f,0x2e37e⟩).bind (X86Routine.run listed [0x2e38a] n) := by rfl
@[local simp] private theorem step_2e37e (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e38a] (n+1) ⟨s,f,0x2e37e⟩ =
      (X86Routine.execute (.control (.block (.store ⟨some 3,none,0,46⟩ 0))) ⟨s,f,0x2e381⟩).bind (X86Routine.run listed [0x2e38a] n) := by rfl
@[local simp] private theorem step_2e381 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e38a] (n+1) ⟨s,f,0x2e381⟩ =
      (X86Routine.execute (.jump 7) ⟨s,f,0x2e383⟩).bind (X86Routine.run listed [0x2e38a] n) := by rfl
@[local simp] private theorem step_2e383 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e38a] (n+1) ⟨s,f,0x2e383⟩ =
      (X86Routine.execute (.storeImmediate ⟨some 3,none,0,46⟩ 0) ⟨s,f,0x2e38a⟩).bind (X86Routine.run listed [0x2e38a] n) := by rfl
@[local simp] private theorem stop_2e38a (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e38a] n ⟨s,f,0x2e38a⟩=some ⟨s,f,0x2e38a⟩ := by cases n <;> rfl
theorem front_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x2e38a] 8 ⟨s,f,0x2e368⟩=some (cached s 22 46 0x2e38a) := by
  have run : X86Routine.run listed [0x2e38a] 8 ⟨s,f,0x2e368⟩=some (cached s 22 46 0x2e38a) := by
    by_cases h : (load16 s.memory (s.regs 3+(22#32))).signExtend 32=(0xffffffff#32)
    all_goals simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      X86Block.Address.eval,X86.execute,blockPreservesFlags,cached,value,index,
      cmp32_zero,put,write,BitVec.add_assoc,h,-BitVec.toInt_add]
    all_goals
      funext r
      simp only [write]
      by_cases h0 : r=0 <;> by_cases h2 : r=2 <;> simp [h0,h2]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]
@[local simp] private theorem step_2e38a (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e3ac] (n+1) ⟨s,f,0x2e38a⟩ =
      (X86Routine.execute (.control (.block (.legacy (.movsx16 0 3 24)))) ⟨s,f,0x2e38e⟩).bind (X86Routine.run listed [0x2e3ac] n) := by rfl
@[local simp] private theorem step_2e38e (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e3ac] (n+1) ⟨s,f,0x2e38e⟩ =
      (X86Routine.execute (.compareRegister 0 0xffffffff) ⟨s,f,0x2e391⟩).bind (X86Routine.run listed [0x2e3ac] n) := by rfl
@[local simp] private theorem step_2e391 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e3ac] (n+1) ⟨s,f,0x2e391⟩ =
      (X86Routine.execute (.control (.jumpZero true 18)) ⟨s,f,0x2e393⟩).bind (X86Routine.run listed [0x2e3ac] n) := by rfl
@[local simp] private theorem step_2e393 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e3ac] (n+1) ⟨s,f,0x2e393⟩ =
      (X86Routine.execute (.multiplyImmediate 0 0 18) ⟨s,f,0x2e396⟩).bind (X86Routine.run listed [0x2e3ac] n) := by rfl
@[local simp] private theorem step_2e396 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e3ac] (n+1) ⟨s,f,0x2e396⟩ =
      (X86Routine.execute (.control (.block (.load 2 ⟨none,none,0,0x2c118⟩))) ⟨s,f,0x2e39c⟩).bind (X86Routine.run listed [0x2e3ac] n) := by rfl
@[local simp] private theorem step_2e39c (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e3ac] (n+1) ⟨s,f,0x2e39c⟩ =
      (X86Routine.execute (.control (.block (.load 0 ⟨some 2,some 0,0,14⟩))) ⟨s,f,0x2e3a0⟩).bind (X86Routine.run listed [0x2e3ac] n) := by rfl
@[local simp] private theorem step_2e3a0 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e3ac] (n+1) ⟨s,f,0x2e3a0⟩ =
      (X86Routine.execute (.control (.block (.store ⟨some 3,none,0,50⟩ 0))) ⟨s,f,0x2e3a3⟩).bind (X86Routine.run listed [0x2e3ac] n) := by rfl
@[local simp] private theorem step_2e3a3 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e3ac] (n+1) ⟨s,f,0x2e3a3⟩ =
      (X86Routine.execute (.jump 7) ⟨s,f,0x2e3a5⟩).bind (X86Routine.run listed [0x2e3ac] n) := by rfl
@[local simp] private theorem step_2e3a5 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e3ac] (n+1) ⟨s,f,0x2e3a5⟩ =
      (X86Routine.execute (.storeImmediate ⟨some 3,none,0,50⟩ 0) ⟨s,f,0x2e3ac⟩).bind (X86Routine.run listed [0x2e3ac] n) := by rfl
@[local simp] private theorem stop_2e3ac (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e3ac] n ⟨s,f,0x2e3ac⟩=some ⟨s,f,0x2e3ac⟩ := by cases n <;> rfl
theorem back_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x2e3ac] 8 ⟨s,f,0x2e38a⟩=some (cached s 24 50 0x2e3ac) := by
  have run : X86Routine.run listed [0x2e3ac] 8 ⟨s,f,0x2e38a⟩=some (cached s 24 50 0x2e3ac) := by
    by_cases h : (load16 s.memory (s.regs 3+(24#32))).signExtend 32=(0xffffffff#32)
    all_goals simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      X86Block.Address.eval,X86.execute,blockPreservesFlags,cached,value,index,
      cmp32_zero,put,write,BitVec.add_assoc,h,-BitVec.toInt_add]
    all_goals
      funext r
      simp only [write]
      by_cases h0 : r=0 <;> by_cases h2 : r=2 <;> simp [h0,h2]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

@[simp] theorem cached_memory (s : X86Memory.State) (off dest : Word) (pc : Nat) :
    (cached s off dest pc).core.memory=store32 s.memory (s.regs 3+dest) (value s off) := rfl
@[simp] theorem cached_reg (s : X86Memory.State) (off dest : Word) (pc : Nat) (r : Reg)
    (h0 : r≠0) (h2 : r≠2) : (cached s off dest pc).core.regs r=s.regs r := by
  simp only [cached]; split <;> simp [put,write,h0,h2]

theorem joined_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x2e3ac] 16 ⟨s,f,0x2e368⟩=some (result s) := by
  obtain ⟨n,hn,path,_⟩ := X86Routine.run_path (front_execution s f)
  have active (pc : Nat) (h : program pc≠none) : pc∉[0x2e3ac] := by
    simpa only [List.mem_singleton] using fun eq => h (by subst pc; decide)
  have path := path.transfer program [0x2e3ac] (fun _ _ => rfl) active
  exact path.finish (back_execution (front s).core (front s).flags) 16 (by omega)

theorem fields_apart (line : Word) : Apart (line+46) (line+50) := by
  have h := PlayerHeight.slots_apart (line+46) 0 1 (by decide)
  change Apart (line+46+(0#32)) (line+46+(4#32)) at h
  simpa [BitVec.add_assoc] using h

/-- Both emitted pointers survive, without assumptions about side-table aliases. -/
theorem readback (s : X86Memory.State) :
    load32 (result s).core.memory (s.regs 3+46)=value s 22 ∧
    load32 (result s).core.memory (s.regs 3+50)=value (front s).core 24 := by
  simp only [result,cached_memory,front,cached_reg s 22 46 0x2e38a 3 (by decide) (by decide)]
  rw [load_store_apart _ _ _ _ (fields_apart _),load_store,load_store]
  exact ⟨rfl,rfl⟩

theorem frame (s : X86Memory.State) (a : Word)
    (hf : Apart a (s.regs 3+46)) (hb : Apart a (s.regs 3+50)) :
    load32 (result s).core.memory a=load32 s.memory a := by
  simp only [result,cached_memory,front,cached_reg s 22 46 0x2e38a 3 (by decide) (by decide)]
  rw [load_store_apart _ _ _ _ hb,load_store_apart _ _ _ _ hf]

/-- The sentinel test is precisely the original signed 16-bit -1 test. -/
theorem sentinel (i : BitVec 16) : i.signExtend 32=(0xffffffff#32) ↔ i=(65535#16) := by
  constructor
  · intro h
    apply BitVec.eq_of_toInt_eq
    have h := congrArg BitVec.toInt h
    simpa [BitVec.toInt_signExtend_of_le (show 16≤32 from by decide)] using h
  · intro h; subst i; decide

theorem lookup (s : X86Memory.State) (off : Word) (i : BitVec 16) (base : Word)
    (hi : load16 s.memory (s.regs 3+off)=i) (hb : load32 s.memory 0x2c118=base) :
    value s off=if i=65535 then 0 else load32 s.memory (E1M1NoiseGraph.sideAddress base i) := by
  simp only [value,index,hi,hb,sentinel]
  simp [E1M1NoiseGraph.sideAddress,BitVec.add_comm,sentinel]

end Doom.Proofs.OriginalLineCache
