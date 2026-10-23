import Doom.Proofs.E1M1LineGeometry
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalLineSetup
open Verification X86 X86Memory X86Control BlockSummary
def metadataBytes : List UInt8 := [0x66,0x8b,0x41,0x4,0x66,0x89,0x43,0x10,0x66,0x8b,0x41,0x6,0x66,0x89,0x43,0x12,0x66,0x8b,0x41,0x8,0x66,0x89,0x43,0x14]
def slopeBytes : List UInt8 := [0x8b,0x43,0x8,0x85,0xc0,0x75,0x9,0xc7,0x43,0x2a,0x1,0x0,0x0,0x0,0xeb,0x2a,0x8b,0x53,0xc,0x85,0xd2,0x75,0x5,0x89,0x53,0x2a,0xeb,0x1e,0x89,0xc2,0x8b,0x43,0xc,0xe8,0x6e,0xee,0xfe,0xff,0x85,0xc0,0x7e,0x9,0xc7,0x43,0x2a,0x2,0x0,0x0,0x0,0xeb,0x7,0xc7,0x43,0x2a,0x3,0x0,0x0,0x0]
def bytesProgram (metadata slope : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2e29a≤pc ∧ pc<0x2e2b2 then X86Routine.decodeAt metadata (pc-0x2e29a)
  else if 0x2e2ec≤pc ∧ pc<0x2e326 then X86Routine.decodeAt slope (pc-0x2e2ec) else none
def program := bytesProgram metadataBytes slopeBytes
def listed : X86Routine.Program
  | 0x2e29a => some (.loadHalf 0 ⟨some 1,none,0,4⟩,4)
  | 0x2e29e => some (.storeHalf ⟨some 3,none,0,16⟩ 0,4)
  | 0x2e2a2 => some (.loadHalf 0 ⟨some 1,none,0,6⟩,4)
  | 0x2e2a6 => some (.storeHalf ⟨some 3,none,0,18⟩ 0,4)
  | 0x2e2aa => some (.loadHalf 0 ⟨some 1,none,0,8⟩,4)
  | 0x2e2ae => some (.storeHalf ⟨some 3,none,0,20⟩ 0,4)
  | 0x2e2ec => some (.control (.block (.legacy (.load 0 3 8))),3)
  | 0x2e2ef => some (.control (.testWord 0 0),2)
  | 0x2e2f1 => some (.control (.jumpZero false 9),2)
  | 0x2e2f3 => some (.storeImmediate ⟨some 3,none,0,42⟩ 1,7)
  | 0x2e2fa => some (.jump 42,2)
  | 0x2e2fc => some (.control (.block (.legacy (.load 2 3 12))),3)
  | 0x2e2ff => some (.control (.testWord 2 2),2)
  | 0x2e301 => some (.control (.jumpZero false 5),2)
  | 0x2e303 => some (.control (.block (.store ⟨some 3,none,0,42⟩ 2)),3)
  | 0x2e306 => some (.jump 30,2)
  | 0x2e308 => some (.control (.block (.legacy (.mov 2 0))),2)
  | 0x2e30a => some (.control (.block (.legacy (.load 0 3 12))),3)
  | 0x2e30d => some (.call (-70034),5)
  | 0x2e312 => some (.control (.testWord 0 0),2)
  | 0x2e314 => some (.jumpSigned 1 9,2)
  | 0x2e316 => some (.storeImmediate ⟨some 3,none,0,42⟩ 2,7)
  | 0x2e31d => some (.jump 7,2)
  | 0x2e31f => some (.storeImmediate ⟨some 3,none,0,42⟩ 3,7)
  | _ => none
theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

/-- Each next source read observes all preceding halfword stores. -/
def copyField (s : X86Memory.State) (src dst : Word) : X86Memory.State :=
  let v := load16 s.memory (s.regs 1+src)
  {put s 0 (OriginalLineLoad.ax (s.regs 0) v) with
    memory := X86Routine.store16 s.memory (s.regs 3+dst) v}
def metadata (s : X86Memory.State) := copyField (copyField (copyField s 4 16) 6 18) 8 20
def dx (s : X86Memory.State) := load32 s.memory (s.regs 3+8)
def dy (s : X86Memory.State) := load32 s.memory (s.regs 3+12)
/-- Axis branches finish classification. The diagonal branch executes CALL,
including the actual return-address store, and stops at FixedDiv's entry. -/
def selected (s : X86Memory.State) : X86Control.State :=
  if dx s=0 then
    ⟨{put s 0 0 with memory := store32 s.memory (s.regs 3+42) 1},some (logical32 0),0x2e326⟩
  else if dy s=0 then
    ⟨{put (put s 0 (dx s)) 2 0 with memory := store32 s.memory (s.regs 3+42) 0},some (logical32 0),0x2e326⟩
  else ⟨X86Routine.pushWord (put (put s 0 (dy s)) 2 (dx s)) 0x2e312,
    some (logical32 (dy s)),0x1d180⟩
def classified (s : X86Memory.State) : X86Control.State :=
  ⟨{s with memory := store32 s.memory (s.regs 3+42) (if (s.regs 0).toInt≤0 then 3 else 2)},
    some (logical32 (s.regs 0)),0x2e326⟩
private theorem low_ax (old : Word) (v : BitVec 16) :
    ((old &&& (0xffff0000#32)) ||| v.zeroExtend 32).extractLsb' 0 16=v := OriginalLineLoad.ax_low old v

@[local simp] private theorem step_2e29a (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e2b2] (n+1) ⟨s,f,0x2e29a⟩ =
      (X86Routine.execute (.loadHalf 0 ⟨some 1,none,0,4⟩) ⟨s,f,0x2e29e⟩).bind (X86Routine.run listed [0x2e2b2] n) := by rfl
@[local simp] private theorem step_2e29e (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e2b2] (n+1) ⟨s,f,0x2e29e⟩ =
      (X86Routine.execute (.storeHalf ⟨some 3,none,0,16⟩ 0) ⟨s,f,0x2e2a2⟩).bind (X86Routine.run listed [0x2e2b2] n) := by rfl
@[local simp] private theorem step_2e2a2 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e2b2] (n+1) ⟨s,f,0x2e2a2⟩ =
      (X86Routine.execute (.loadHalf 0 ⟨some 1,none,0,6⟩) ⟨s,f,0x2e2a6⟩).bind (X86Routine.run listed [0x2e2b2] n) := by rfl
@[local simp] private theorem step_2e2a6 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e2b2] (n+1) ⟨s,f,0x2e2a6⟩ =
      (X86Routine.execute (.storeHalf ⟨some 3,none,0,18⟩ 0) ⟨s,f,0x2e2aa⟩).bind (X86Routine.run listed [0x2e2b2] n) := by rfl
@[local simp] private theorem step_2e2aa (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e2b2] (n+1) ⟨s,f,0x2e2aa⟩ =
      (X86Routine.execute (.loadHalf 0 ⟨some 1,none,0,8⟩) ⟨s,f,0x2e2ae⟩).bind (X86Routine.run listed [0x2e2b2] n) := by rfl
@[local simp] private theorem step_2e2ae (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e2b2] (n+1) ⟨s,f,0x2e2ae⟩ =
      (X86Routine.execute (.storeHalf ⟨some 3,none,0,20⟩ 0) ⟨s,f,0x2e2b2⟩).bind (X86Routine.run listed [0x2e2b2] n) := by rfl
@[local simp] private theorem stop_meta_2e2b2 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e2b2] n ⟨s,f,0x2e2b2⟩=some ⟨s,f,0x2e2b2⟩ := by cases n <;> rfl
theorem metadata_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x2e2b2] 6 ⟨s,f,0x2e29a⟩=some (⟨metadata s,f,0x2e2b2⟩) := by
  have run : X86Routine.run listed [0x2e2b2] 6 ⟨s,f,0x2e29a⟩=some (⟨metadata s,f,0x2e2b2⟩) := by
    all_goals simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      X86Block.Address.eval,X86.execute,blockPreservesFlags,copyField,metadata,
      OriginalLineLoad.ax,low_ax,selected,classified,dx,dy,
      put,write,BitVec.add_assoc,-BitVec.toInt_add]
    all_goals
      funext r
      by_cases h0 : r=0 <;> by_cases h2 : r=2 <;> simp [write,h0,h2]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]
@[local simp] private theorem step_2e2ec (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e326,0x1d180] (n+1) ⟨s,f,0x2e2ec⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 0 3 8)))) ⟨s,f,0x2e2ef⟩).bind (X86Routine.run listed [0x2e326,0x1d180] n) := by rfl
@[local simp] private theorem step_2e2ef (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e326,0x1d180] (n+1) ⟨s,f,0x2e2ef⟩ =
      (X86Routine.execute (.control (.testWord 0 0)) ⟨s,f,0x2e2f1⟩).bind (X86Routine.run listed [0x2e326,0x1d180] n) := by rfl
@[local simp] private theorem step_2e2f1 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e326,0x1d180] (n+1) ⟨s,f,0x2e2f1⟩ =
      (X86Routine.execute (.control (.jumpZero false 9)) ⟨s,f,0x2e2f3⟩).bind (X86Routine.run listed [0x2e326,0x1d180] n) := by rfl
@[local simp] private theorem step_2e2f3 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e326,0x1d180] (n+1) ⟨s,f,0x2e2f3⟩ =
      (X86Routine.execute (.storeImmediate ⟨some 3,none,0,42⟩ 1) ⟨s,f,0x2e2fa⟩).bind (X86Routine.run listed [0x2e326,0x1d180] n) := by rfl
@[local simp] private theorem step_2e2fa (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e326,0x1d180] (n+1) ⟨s,f,0x2e2fa⟩ =
      (X86Routine.execute (.jump 42) ⟨s,f,0x2e2fc⟩).bind (X86Routine.run listed [0x2e326,0x1d180] n) := by rfl
@[local simp] private theorem step_2e2fc (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e326,0x1d180] (n+1) ⟨s,f,0x2e2fc⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 2 3 12)))) ⟨s,f,0x2e2ff⟩).bind (X86Routine.run listed [0x2e326,0x1d180] n) := by rfl
@[local simp] private theorem step_2e2ff (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e326,0x1d180] (n+1) ⟨s,f,0x2e2ff⟩ =
      (X86Routine.execute (.control (.testWord 2 2)) ⟨s,f,0x2e301⟩).bind (X86Routine.run listed [0x2e326,0x1d180] n) := by rfl
@[local simp] private theorem step_2e301 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e326,0x1d180] (n+1) ⟨s,f,0x2e301⟩ =
      (X86Routine.execute (.control (.jumpZero false 5)) ⟨s,f,0x2e303⟩).bind (X86Routine.run listed [0x2e326,0x1d180] n) := by rfl
@[local simp] private theorem step_2e303 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e326,0x1d180] (n+1) ⟨s,f,0x2e303⟩ =
      (X86Routine.execute (.control (.block (.store ⟨some 3,none,0,42⟩ 2))) ⟨s,f,0x2e306⟩).bind (X86Routine.run listed [0x2e326,0x1d180] n) := by rfl
@[local simp] private theorem step_2e306 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e326,0x1d180] (n+1) ⟨s,f,0x2e306⟩ =
      (X86Routine.execute (.jump 30) ⟨s,f,0x2e308⟩).bind (X86Routine.run listed [0x2e326,0x1d180] n) := by rfl
@[local simp] private theorem step_2e308 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e326,0x1d180] (n+1) ⟨s,f,0x2e308⟩ =
      (X86Routine.execute (.control (.block (.legacy (.mov 2 0)))) ⟨s,f,0x2e30a⟩).bind (X86Routine.run listed [0x2e326,0x1d180] n) := by rfl
@[local simp] private theorem step_2e30a (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e326,0x1d180] (n+1) ⟨s,f,0x2e30a⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 0 3 12)))) ⟨s,f,0x2e30d⟩).bind (X86Routine.run listed [0x2e326,0x1d180] n) := by rfl
@[local simp] private theorem step_2e30d (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e326,0x1d180] (n+1) ⟨s,f,0x2e30d⟩ =
      (X86Routine.execute (.call (-70034)) ⟨s,f,0x2e312⟩).bind (X86Routine.run listed [0x2e326,0x1d180] n) := by
  simp [X86Routine.run,listed]
@[local simp] private theorem stop_select_2e326 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e326,0x1d180] n ⟨s,f,0x2e326⟩=some ⟨s,f,0x2e326⟩ := by cases n <;> rfl
@[local simp] private theorem stop_select_1d180 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e326,0x1d180] n ⟨s,f,0x1d180⟩=some ⟨s,f,0x1d180⟩ := by cases n <;> rfl
theorem selection_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x2e326,0x1d180] 9 ⟨s,f,0x2e2ec⟩=some (selected s) := by
  have run : X86Routine.run listed [0x2e326,0x1d180] 9 ⟨s,f,0x2e2ec⟩=some (selected s) := by
    by_cases x : load32 s.memory (s.regs 3+(8#32))=(0#32) <;>
      by_cases y : load32 s.memory (s.regs 3+(12#32))=(0#32)
    all_goals simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      X86Block.Address.eval,X86.execute,blockPreservesFlags,copyField,metadata,
      OriginalLineLoad.ax,low_ax,selected,classified,dx,dy,
      x,y,logical32,X86Routine.pushWord,put,write,BitVec.add_assoc,-BitVec.toInt_add]
    all_goals
      funext r
      by_cases h0 : r=0 <;> by_cases h2 : r=2 <;> simp [write,h0,h2]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]
@[local simp] private theorem step_2e312 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e326] (n+1) ⟨s,f,0x2e312⟩ =
      (X86Routine.execute (.control (.testWord 0 0)) ⟨s,f,0x2e314⟩).bind (X86Routine.run listed [0x2e326] n) := by rfl
@[local simp] private theorem step_2e314 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e326] (n+1) ⟨s,f,0x2e314⟩ =
      (X86Routine.execute (.jumpSigned 1 9) ⟨s,f,0x2e316⟩).bind (X86Routine.run listed [0x2e326] n) := by rfl
@[local simp] private theorem step_2e316 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e326] (n+1) ⟨s,f,0x2e316⟩ =
      (X86Routine.execute (.storeImmediate ⟨some 3,none,0,42⟩ 2) ⟨s,f,0x2e31d⟩).bind (X86Routine.run listed [0x2e326] n) := by rfl
@[local simp] private theorem step_2e31d (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e326] (n+1) ⟨s,f,0x2e31d⟩ =
      (X86Routine.execute (.jump 7) ⟨s,f,0x2e31f⟩).bind (X86Routine.run listed [0x2e326] n) := by rfl
@[local simp] private theorem step_2e31f (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e326] (n+1) ⟨s,f,0x2e31f⟩ =
      (X86Routine.execute (.storeImmediate ⟨some 3,none,0,42⟩ 3) ⟨s,f,0x2e326⟩).bind (X86Routine.run listed [0x2e326] n) := by rfl
@[local simp] private theorem stop_class_2e326 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e326] n ⟨s,f,0x2e326⟩=some ⟨s,f,0x2e326⟩ := by cases n <;> rfl
theorem classification_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x2e326] 4 ⟨s,f,0x2e312⟩=some (classified s) := by
  have run : X86Routine.run listed [0x2e326] 4 ⟨s,f,0x2e312⟩=some (classified s) := by
    by_cases le : (s.regs 0).toInt≤0
    all_goals simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      X86Block.Address.eval,X86.execute,blockPreservesFlags,copyField,metadata,
      OriginalLineLoad.ax,low_ax,selected,classified,dx,dy,
      le,PlayerHeight.logical_le,put,write,BitVec.add_assoc,-BitVec.toInt_add]
    all_goals
      funext r
      by_cases h0 : r=0 <;> by_cases h2 : r=2 <;> simp [write,h0,h2]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

@[simp] theorem copyField_reg (s : X86Memory.State) (src dst : Word) (r : Reg) (h : r≠0) :
    (copyField s src dst).regs r=s.regs r := by simp [copyField,put,write,h]
@[simp] theorem metadata_reg (s : X86Memory.State) (r : Reg) (h : r≠0) :
    (metadata s).regs r=s.regs r := by simp [metadata,copyField_reg,h]
theorem copyField_frame (s : X86Memory.State) (src dst a : Word)
    (h : HalfMemory.Separate 4 2 a (s.regs 3+dst)) :
    load32 (copyField s src dst).memory a=load32 s.memory a := HalfMemory.word_frame _ _ _ _ h
theorem metadata_frame (s : X86Memory.State) (a : Word)
    (h : ∀ off∈[(16#32),18,20], HalfMemory.Separate 4 2 a (s.regs 3+off)) :
    load32 (metadata s).memory a=load32 s.memory a := by
  unfold metadata
  rw [copyField_frame _ _ _ _ (by simpa using h 20 (by simp)),
      copyField_frame _ _ _ _ (by simpa using h 18 (by simp)),
      copyField_frame _ _ _ _ (h 16 (by simp))]

/-- The three packed fields retain their own exact sequentially read values. -/
theorem metadata_fields (s : X86Memory.State) :
    load16 (metadata s).memory (s.regs 3+16)=load16 s.memory (s.regs 1+4) ∧
    load16 (metadata s).memory (s.regs 3+18)=load16 (copyField s 4 16).memory (s.regs 1+6) ∧
    load16 (metadata s).memory (s.regs 3+20)=load16 (copyField (copyField s 4 16) 6 18).memory (s.regs 1+8) := by
  have a : HalfMemory.Separate 2 2 (s.regs 3+16) (s.regs 3+18) :=
    HalfMemory.translate (s.regs 3) (16#32) (18#32) 2 2 (by unfold HalfMemory.Separate; decide +kernel)
  have b : HalfMemory.Separate 2 2 (s.regs 3+16) (s.regs 3+20) :=
    HalfMemory.translate (s.regs 3) (16#32) (20#32) 2 2 (by unfold HalfMemory.Separate; decide +kernel)
  have c : HalfMemory.Separate 2 2 (s.regs 3+18) (s.regs 3+20) :=
    HalfMemory.translate (s.regs 3) (18#32) (20#32) 2 2 (by unfold HalfMemory.Separate; decide +kernel)
  simp only [metadata,copyField,put,write,show (3:Reg)≠0 from by decide,
    show (1:Reg)≠0 from by decide,if_false]
  rw [HalfMemory.half_frame _ _ _ _ b,HalfMemory.half_frame _ _ _ _ a,
    HalfMemory.half_frame _ _ _ _ c,HalfMemory.readback,HalfMemory.readback,HalfMemory.readback]
  exact ⟨rfl,rfl,rfl⟩

theorem diagonal_call (s : X86Memory.State) (x : dx s≠0) (y : dy s≠0) :
    (selected s).pc=0x1d180 ∧ (selected s).core.regs 0=dy s ∧
    (selected s).core.regs 2=dx s ∧ (selected s).core.regs 4=s.regs 4-4 ∧
    load32 (selected s).core.memory (s.regs 4-4)=0x2e312 := by
  change dx s≠(0#32) at x
  change dy s≠(0#32) at y
  simp [selected,x,y,X86Routine.pushWord,put,write,load_store]
theorem axis_classification (s : X86Memory.State) (h : dx s=0 ∨ dy s=0) :
    (selected s).pc=0x2e326 ∧
    load32 (selected s).core.memory (s.regs 3+42)=(if dx s=0 then 1 else 0) := by
  by_cases x : dx s=(0#32)
  · simp [selected,x,load_store]
  · have y : dy s=(0#32) := h.resolve_left x
    simp [selected,x,y,load_store]
/-- A zero returned quotient takes the historical negative-slope branch too. -/
theorem returned_classification (s : X86Memory.State) :
    load32 (classified s).core.memory (s.regs 3+42)=(if (s.regs 0).toInt≤0 then 3 else 2) := load_store _ _ _

end Doom.Proofs.OriginalLineSetup
