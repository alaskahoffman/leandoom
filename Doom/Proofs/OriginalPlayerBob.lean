import Doom.Proofs.OriginalPlayerHeight
import Doom.Proofs.OriginalThrust

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 200000
namespace Doom.Proofs.PlayerHeight
open Verification X86 X86Memory X86Control BlockSummary

/-- SAR by two rounds down, including negative sums after wrapping. -/
theorem quarter_word (v : Word) :
    v.sshiftRight 2 = BitVec.ofInt 32 (v.toInt / 4) := by
  rw [BitVec.sshiftRight_eq, Int.shiftRight_eq_div_pow]
  rfl

/-- The compiler's sign correction makes SAR implement truncation toward zero. -/
theorem half_word (v : Word) :
    (v - v.sshiftRight 31).sshiftRight 1 = BitVec.ofInt 32 (v.toInt.tdiv 2) := by
  have lo := BitVec.le_toInt v
  have hi := BitVec.toInt_lt (x := v)
  have sign : (v.sshiftRight 31).toInt = if v.toInt < 0 then -1 else 0 := by
    rw [BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow]
    split <;> omega
  have correction : (v-v.sshiftRight 31).toInt = v.toInt - (if v.toInt < 0 then -1 else 0) := by
    rw [BitVec.toInt_sub, sign]
    apply Int.bmod_eq_of_le <;> split <;> omega
  rw [BitVec.sshiftRight_eq, Int.shiftRight_eq_div_pow, correction]
  congr 1
  rw [Int.tdiv_eq_ediv]
  simp only [Int.dvd_iff_emod_eq_zero]
  split <;> split <;> simp only [Int.sign, Nat.reducePow] <;> omega

/-- The wrapped 409*tic product and 13-bit mask select the live table index. -/
theorem bob_index (time : Int32) :
    ((time.toBitVec * 409) &&& (8191#32)).toNat = (ViewState.bobIndex time).val := by
  change (time.toBitVec * 409).toNat &&& (2^13-1) = (time * 409).toUInt32.toNat % 2^13
  rw [Nat.and_two_pow_sub_one_eq_mod]
  rfl

@[simp] theorem bob_step_6 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [64] (n+1) ⟨s,f,6⟩ =
      (X86Routine.execute (.control (.block (.legacy (.mov 1 0)))) ⟨s,f,8⟩).bind (X86Routine.run program [64] n) := by rfl

@[simp] theorem bob_step_8 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [64] (n+1) ⟨s,f,8⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 3 0 0)))) ⟨s,f,10⟩).bind (X86Routine.run program [64] n) := by rfl

@[simp] theorem bob_step_10 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [64] (n+1) ⟨s,f,10⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 3 3 72)))) ⟨s,f,13⟩).bind (X86Routine.run program [64] n) := by rfl

@[simp] theorem bob_step_13 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [64] (n+1) ⟨s,f,13⟩ =
      (X86Routine.execute (.control (.block (.legacy (.mov 0 3)))) ⟨s,f,15⟩).bind (X86Routine.run program [64] n) := by rfl

@[simp] theorem bob_step_15 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [64] (n+2) ⟨s,f,15⟩ =
      X86Routine.run program [64] n ⟨multiply s,none,21⟩ := by
  change X86Routine.run program [64] n
    ⟨X86Block.execute (.arithmetic (.shrd eax edx 16))
      (X86Block.execute (.arithmetic (.imul ebx)) s),none,21⟩ = _
  rw [multiply_correct]

@[simp] theorem bob_step_21 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [64] (n+1) ⟨s,f,21⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 3 1 0)))) ⟨s,f,23⟩).bind (X86Routine.run program [64] n) := by rfl

@[simp] theorem bob_step_23 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [64] (n+1) ⟨s,f,23⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 3 3 76)))) ⟨s,f,26⟩).bind (X86Routine.run program [64] n) := by rfl

@[simp] theorem bob_step_26 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [64] (n+1) ⟨s,f,26⟩ =
      (X86Routine.execute (.control (.block (.legacy (.mov 6 0)))) ⟨s,f,28⟩).bind (X86Routine.run program [64] n) := by rfl

@[simp] theorem bob_step_28 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [64] (n+1) ⟨s,f,28⟩ =
      (X86Routine.execute (.control (.block (.legacy (.mov 0 3)))) ⟨s,f,30⟩).bind (X86Routine.run program [64] n) := by rfl

@[simp] theorem bob_step_30 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [64] (n+2) ⟨s,f,30⟩ =
      X86Routine.run program [64] n ⟨multiply s,none,36⟩ := by
  change X86Routine.run program [64] n
    ⟨X86Block.execute (.arithmetic (.shrd eax edx 16))
      (X86Block.execute (.arithmetic (.imul ebx)) s),none,36⟩ = _
  rw [multiply_correct]

@[simp] theorem bob_step_36 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [64] (n+1) ⟨s,f,36⟩ =
      (X86Routine.execute (.control (.block (.arithmetic (.add 6 0)))) ⟨s,f,38⟩).bind (X86Routine.run program [64] n) := by rfl

@[simp] theorem bob_step_38 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [64] (n+1) ⟨s,f,38⟩ =
      (X86Routine.execute (.control (.block (.legacy (.mov 2 6)))) ⟨s,f,40⟩).bind (X86Routine.run program [64] n) := by rfl

@[simp] theorem bob_step_40 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [64] (n+1) ⟨s,f,40⟩ =
      (X86Routine.execute (.control (.block (.store ⟨some 1,none,0,28⟩ 6))) ⟨s,f,43⟩).bind (X86Routine.run program [64] n) := by rfl

@[simp] theorem bob_step_43 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [64] (n+1) ⟨s,f,43⟩ =
      (X86Routine.execute (.sar 2 2) ⟨s,f,46⟩).bind (X86Routine.run program [64] n) := by rfl

@[simp] theorem bob_step_46 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [64] (n+1) ⟨s,f,46⟩ =
      (X86Routine.execute (.control (.block (.store ⟨some 1,none,0,28⟩ 2))) ⟨s,f,49⟩).bind (X86Routine.run program [64] n) := by rfl

@[simp] theorem bob_step_49 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [64] (n+1) ⟨s,f,49⟩ =
      (X86Routine.execute (.compareRegister 2 1048576) ⟨s,f,55⟩).bind (X86Routine.run program [64] n) := by rfl

@[simp] theorem bob_step_55 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [64] (n+1) ⟨s,f,55⟩ =
      (X86Routine.execute (.jumpSigned 1 7) ⟨s,f,57⟩).bind (X86Routine.run program [64] n) := by rfl

@[simp] theorem bob_step_57 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [64] (n+1) ⟨s,f,57⟩ =
      (X86Routine.execute (.storeImmediate ⟨some 1,none,0,28⟩ 1048576) ⟨s,f,64⟩).bind (X86Routine.run program [64] n) := by rfl

@[simp] theorem bob_stop_64 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [64] n ⟨s,f,64⟩ = some ⟨s,f,64⟩ := by cases n <;> rfl

@[simp] theorem bob_step_130 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [170] (n+1) ⟨s,f,130⟩ =
      (X86Routine.execute (.multiplyMemory 0 ⟨none,none,0,184192⟩ 409) ⟨s,f,140⟩).bind (X86Routine.run program [170] n) := by rfl

@[simp] theorem bob_step_140 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [170] (n+1) ⟨s,f,140⟩ =
      (X86Routine.execute (.control (.andEax 8191)) ⟨s,f,145⟩).bind (X86Routine.run program [170] n) := by rfl

@[simp] theorem bob_step_145 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [170] (n+1) ⟨s,f,145⟩ =
      (X86Routine.execute (.control (.block (.load 3 ⟨none,some 0,2,23172⟩))) ⟨s,f,152⟩).bind (X86Routine.run program [170] n) := by rfl

@[simp] theorem bob_step_152 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [170] (n+1) ⟨s,f,152⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 0 1 28)))) ⟨s,f,155⟩).bind (X86Routine.run program [170] n) := by rfl

@[simp] theorem bob_step_155 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [170] (n+1) ⟨s,f,155⟩ =
      (X86Routine.execute (.control (.block (.legacy (.mov 2 0)))) ⟨s,f,157⟩).bind (X86Routine.run program [170] n) := by rfl

@[simp] theorem bob_step_157 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [170] (n+1) ⟨s,f,157⟩ =
      (X86Routine.execute (.sar 2 31) ⟨s,f,160⟩).bind (X86Routine.run program [170] n) := by rfl

@[simp] theorem bob_step_160 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [170] (n+1) ⟨s,f,160⟩ =
      (X86Routine.execute (.control (.block (.arithmetic (.sub 0 2)))) ⟨s,f,162⟩).bind (X86Routine.run program [170] n) := by rfl

@[simp] theorem bob_step_162 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [170] (n+1) ⟨s,f,162⟩ =
      (X86Routine.execute (.sar 0 1) ⟨s,f,164⟩).bind (X86Routine.run program [170] n) := by rfl

@[simp] theorem bob_step_164 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [170] (n+2) ⟨s,f,164⟩ =
      X86Routine.run program [170] n ⟨multiply s,none,170⟩ := by
  change X86Routine.run program [170] n
    ⟨X86Block.execute (.arithmetic (.shrd eax edx 16))
      (X86Block.execute (.arithmetic (.imul ebx)) s),none,170⟩ = _
  rw [multiply_correct]

@[simp] theorem bob_stop_170 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [170] n ⟨s,f,170⟩ = some ⟨s,f,170⟩ := by cases n <;> rfl

/-- Momentum sum after the two original FixedMul pairs and wrapping ADD. -/
def bobSum (s : X86Memory.State) : Word :=
  let obj := load32 s.memory (s.regs 0)
  let mx := load32 s.memory (obj+(72#32))
  let my := load32 s.memory (obj+(76#32))
  mulWord mx mx + mulWord my my

def amplitudeWord (sum : Word) : Word :=
  let quarter := sum.sshiftRight 2
  if quarter.toInt ≤ 1048576 then quarter else 1048576

theorem amplitude_execution (s : X86Memory.State) (f : Option Flags) :
    (X86Routine.run program [64] 20 ⟨s,f,6⟩).map (fun t =>
      (t.pc,load32 t.core.memory (s.regs 0+(28#32)),t.core.regs 1,t.core.regs 4)) =
      some (64,amplitudeWord (bobSum s),s.regs 0,s.regs 4) := by
  by_cases h : ((bobSum s).sshiftRight 2).toInt ≤ 1048576 <;>
    simp only [bobSum] at h <;>
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      X86.execute,X86Block.Address.eval,put,write,eax,ebx,edx,blockPreservesFlags,
      multiply,load_store,cmp32_signed_le,bobSum,amplitudeWord,h,
      -BitVec.toInt_add,-BitVec.toInt_sub,-BitVec.toInt_sshiftRight]

/-- No range assumptions on momentum: the sum wraps before its signed quarter. -/
theorem amplitude_runtime (mx my : Fixed) :
    amplitudeWord (mulWord mx.raw.toBitVec mx.raw.toBitVec +
      mulWord my.raw.toBitVec my.raw.toBitVec) =
      (ViewState.bobAmplitude mx my).raw.toBitVec := by
  simp only [mulWord,Int32.ofBitVec_toBitVec]
  change amplitudeWord (mx*mx+my*my).raw.toBitVec = _
  rw [amplitudeWord,quarter_word]
  let q := Int32.ofInt ((mx*mx+my*my).raw.toInt / 4)
  change (if q.toBitVec.toInt ≤ 1048576 then q.toBitVec else 1048576) =
    (min (1048576 : Int32) q).toBitVec
  change (if q.toBitVec.toInt ≤ 1048576 then q.toBitVec else 1048576) =
    (if (1048576 : Int32) ≤ q then 1048576 else q).toBitVec
  simp only [Int32.toInt_toBitVec,Int32.le_iff_toInt_le]
  by_cases h : q.toInt ≤ 1048576 <;> by_cases k : 1048576 ≤ q.toInt <;>
    simp [h,k] <;> apply BitVec.eq_of_toInt_eq <;> simp <;> omega

theorem amplitude_observation (s : X86Memory.State) (flags : Option Flags)
    (mx my : Fixed)
    (hx : load32 s.memory (load32 s.memory (s.regs 0)+(72#32)) = mx.raw.toBitVec)
    (hy : load32 s.memory (load32 s.memory (s.regs 0)+(76#32)) = my.raw.toBitVec) :
    (X86Routine.run (X86Routine.decodeAt code) [64] 20 ⟨s,flags,6⟩).map (fun t =>
      (t.pc,load32 t.core.memory (s.regs 0+(28#32)),t.core.regs 1,t.core.regs 4)) =
      some (64,(ViewState.bobAmplitude mx my).raw.toBitVec,s.regs 0,s.regs 4) := by
  have h := amplitude_execution s flags
  have valid : X86Routine.run program [64] 20 ⟨s,flags,6⟩ ≠ none := by
    intro hn; rw [hn] at h; contradiction
  rw [X86Routine.run_sound _ _ decoded _ _ _ valid,h]
  simp only [bobSum,hx,hy,amplitude_runtime]

/-- Grounded bob offset, before the player-state branch. Memory is read-only. -/
def offsetWord (s : X86Memory.State) : Word :=
  let index := (load32 s.memory 184192 * 409) &&& (8191#32)
  let sine := load32 s.memory ((index <<< 2)+(23172#32))
  let bob := load32 s.memory (s.regs 1+(28#32))
  mulWord ((bob-bob.sshiftRight 31).sshiftRight 1) sine

theorem offset_execution (s : X86Memory.State) (f : Option Flags) :
    (X86Routine.run program [170] 10 ⟨s,f,130⟩).map (fun t =>
      (t.pc,t.core.regs 0,t.core.regs 1,t.core.regs 4,t.core.memory)) =
      some (170,offsetWord s,s.regs 1,s.regs 4,s.memory) := by
  simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
    X86.execute,X86Block.Address.eval,put,write,eax,ebx,edx,blockPreservesFlags,
    multiply,offsetWord]

theorem bob_table_address (time : Int32) :
    (((time.toBitVec * 409) &&& (8191#32)) <<< 2) + (23172#32) =
      (23172#32) + BitVec.ofNat 32 ((ViewState.bobIndex time).val * 4) := by
  have index : ((time.toBitVec * 409) &&& (8191#32)) =
      BitVec.ofNat 32 (ViewState.bobIndex time).val := by
    apply BitVec.eq_of_toNat_eq
    rw [bob_index, BitVec.toNat_ofNat]
    have h := (ViewState.bobIndex time).isLt
    omega
  rw [index, BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 32 _ * BitVec.ofNat 32 4 + _ = _
  rw [BitVec.ofNat_mul, BitVec.add_comm]

/-- The shared initialized-table relation supplies the exact selected sample. -/
theorem offset_runtime (s : X86Memory.State) (bob : Fixed) (time : Int32)
    (ht : load32 s.memory 184192 = time.toBitVec)
    (hb : load32 s.memory (s.regs 1+(28#32)) = bob.raw.toBitVec)
    (tables : ThrustTables s.memory) :
    offsetWord s = (ViewState.bobOffset bob time).raw.toBitVec := by
  unfold offsetWord
  simp only [ht,hb]
  rw [bob_table_address,half_word,Int32.toInt_toBitVec]
  have sample := tables.entries ⟨(ViewState.bobIndex time).val,
    by have h := (ViewState.bobIndex time).isLt; omega⟩
  change load32 s.memory ((23172#32) + BitVec.ofNat 32 ((ViewState.bobIndex time).val * 4)) = _ at sample
  rw [sample]
  change mulWord (Int32.ofInt (bob.raw.toInt.tdiv 2)).toBitVec
    (Tables.fineSine.get _).toBitVec = _
  rw [mulWord_fixed]
  rfl

/-- Exact original-byte offset execution for every bob word and tic word,
conditional on the time/bob fields and the shared initialized sine table. -/
theorem offset_observation (s : X86Memory.State) (flags : Option Flags)
    (bob : Fixed) (time : Int32)
    (ht : load32 s.memory 184192 = time.toBitVec)
    (hb : load32 s.memory (s.regs 1+(28#32)) = bob.raw.toBitVec)
    (tables : ThrustTables s.memory) :
    (X86Routine.run (X86Routine.decodeAt code) [170] 10 ⟨s,flags,130⟩).map (fun t =>
      (t.pc,t.core.regs 0,t.core.regs 1,t.core.regs 4,t.core.memory)) =
      some (170,(ViewState.bobOffset bob time).raw.toBitVec,s.regs 1,s.regs 4,s.memory) := by
  have h := offset_execution s flags
  have valid : X86Routine.run program [170] 10 ⟨s,flags,130⟩ ≠ none := by
    intro hn; rw [hn] at h; contradiction
  rw [X86Routine.run_sound _ _ decoded _ _ _ valid,h,offset_runtime s bob time ht hb tables]

end Doom.Proofs.PlayerHeight
