import Doom.Proofs.OriginalPlayerHeightCode

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 100000
namespace Doom.Proofs.PlayerHeight
open Verification X86 X86Memory X86Control BlockSummary

theorem slots_apart (p : Word) (a b : Fin 8) (h : a ≠ b) : Apart (p + BitVec.ofNat 32 (4*a.val)) (p + BitVec.ofNat 32 (4*b.val)) := by
  intro i j
  rw [BitVec.add_assoc,BitVec.add_assoc]
  intro he
  have he := (BitVec.add_right_inj p).mp he
  have ha := a.isLt; have hb := b.isLt; have hi := i.isLt; have hj := j.isLt
  have hv := congrArg BitVec.toNat he
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at hv
  have : a.val = b.val := by omega
  exact h (Fin.ext this)

@[simp] theorem load_height_after_delta (m : Memory) (p v : Word) :
    load32 (store32 m (p+(24#32)) v) (p+(20#32)) = load32 m (p+(20#32)) :=
  load_store_apart _ _ _ _ (slots_apart p 5 6 (by decide))
@[simp] theorem load_delta_after_height (m : Memory) (p v : Word) :
    load32 (store32 m (p+(20#32)) v) (p+(24#32)) = load32 m (p+(24#32)) :=
  load_store_apart _ _ _ _ (slots_apart p 6 5 (by decide))

theorem cmp_ge (a b : BitVec 32) : ((compare32 a b).sign == (compare32 a b).overflow) = decide (b.toInt ≤ a.toInt) := by
  have boundsA := a.isLt
  have boundsB := b.isLt
  cases ha : a.msb <;> cases hb : b.msb <;> cases hr : (a-b).msb <;>
    simp [compare32,ha,hb,hr,BitVec.toInt_eq_msb_cond] <;>
    simp only [BitVec.msb_eq_decide,BitVec.toNat_sub,decide_eq_true_eq,decide_eq_false_iff_not] at ha hb hr <;>
    omega

theorem cmp_ge_prop (a b : BitVec 32) : (compare32 a b).sign = (compare32 a b).overflow ↔ b.toInt ≤ a.toInt := by
  calc
    _ ↔ ((compare32 a b).sign == (compare32 a b).overflow) = true := by simp
    _ ↔ decide (b.toInt ≤ a.toInt) = true := by rw [cmp_ge]
    _ ↔ _ := by simp

theorem logical_le (v : BitVec 32) : (logical32 v).lessEqual = decide (v.toInt ≤ 0) := by
  have h : logical32 v = compare32 v 0 := by simp [logical32,compare32,BitVec.ult_eq_decide]
  rw [h,cmp32_signed_le]
  rfl

theorem logical_gt (v : BitVec 32) : !(logical32 v).lessEqual = decide (0 < v.toInt) := by
  have h : logical32 v = compare32 v 0 := by simp [logical32,compare32,BitVec.ult_eq_decide]
  rw [h,cmp32_signed_le]
  simp
  omega

@[simp] theorem logical_zero (v : Word) : (logical32 v).zero = (v == 0) := rfl

/-- Word-level recovery summary. Signed tests and all additions retain the
original 32-bit wrapping behavior. -/
def recover (height delta : Word) : Word × Word := Id.run do
  let sum := height + delta
  let h := if sum.toInt ≤ 2686976 then sum else 2686976
  let d := if sum.toInt ≤ 2686976 then delta else 0
  let d := if h.toInt < 1343488 then (if 0 < d.toInt then d else 1) else d
  let h := if h.toInt < 1343488 then 1343488 else h
  let d := if d = 0 then d else if d + 16384 = 0 then 1 else d + 16384
  return (h,d)

@[simp] theorem recovery_step_177 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [263] (n+1) ⟨s,f,177⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 3 1 24)))) ⟨s,f,180⟩).bind (X86Routine.run program [263] n) := by rfl
@[simp] theorem recovery_step_180 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [263] (n+1) ⟨s,f,180⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 2 1 20)))) ⟨s,f,183⟩).bind (X86Routine.run program [263] n) := by rfl
@[simp] theorem recovery_step_183 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [263] (n+1) ⟨s,f,183⟩ =
      (X86Routine.execute (.control (.block (.arithmetic (.add 2 3)))) ⟨s,f,185⟩).bind (X86Routine.run program [263] n) := by rfl
@[simp] theorem recovery_step_185 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [263] (n+1) ⟨s,f,185⟩ =
      (X86Routine.execute (.control (.block (.store ⟨some 1,none,0,20⟩ 2))) ⟨s,f,188⟩).bind (X86Routine.run program [263] n) := by rfl
@[simp] theorem recovery_step_188 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [263] (n+1) ⟨s,f,188⟩ =
      (X86Routine.execute (.compareRegister 2 2686976) ⟨s,f,194⟩).bind (X86Routine.run program [263] n) := by rfl
@[simp] theorem recovery_step_194 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [263] (n+1) ⟨s,f,194⟩ =
      (X86Routine.execute (.jumpSigned 1 10) ⟨s,f,196⟩).bind (X86Routine.run program [263] n) := by rfl
@[simp] theorem recovery_step_196 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [263] (n+1) ⟨s,f,196⟩ =
      (X86Routine.execute (.storeImmediate ⟨some 1,none,0,20⟩ 2686976) ⟨s,f,203⟩).bind (X86Routine.run program [263] n) := by rfl
@[simp] theorem recovery_step_203 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [263] (n+1) ⟨s,f,203⟩ =
      (X86Routine.execute (.control (.block (.store ⟨some 1,none,0,24⟩ 5))) ⟨s,f,206⟩).bind (X86Routine.run program [263] n) := by rfl
@[simp] theorem recovery_step_206 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [263] (n+1) ⟨s,f,206⟩ =
      (X86Routine.execute (.control (.cmpImmediate ⟨some 1,none,0,20⟩ 1343488)) ⟨s,f,213⟩).bind (X86Routine.run program [263] n) := by rfl
@[simp] theorem recovery_step_213 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [263] (n+1) ⟨s,f,213⟩ =
      (X86Routine.execute (.jumpSigned 0 21) ⟨s,f,215⟩).bind (X86Routine.run program [263] n) := by rfl
@[simp] theorem recovery_step_215 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [263] (n+1) ⟨s,f,215⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 7 1 24)))) ⟨s,f,218⟩).bind (X86Routine.run program [263] n) := by rfl
@[simp] theorem recovery_step_218 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [263] (n+1) ⟨s,f,218⟩ =
      (X86Routine.execute (.storeImmediate ⟨some 1,none,0,20⟩ 1343488) ⟨s,f,225⟩).bind (X86Routine.run program [263] n) := by rfl
@[simp] theorem recovery_step_225 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [263] (n+1) ⟨s,f,225⟩ =
      (X86Routine.execute (.control (.testWord 7 7)) ⟨s,f,227⟩).bind (X86Routine.run program [263] n) := by rfl
@[simp] theorem recovery_step_227 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [263] (n+1) ⟨s,f,227⟩ =
      (X86Routine.execute (.jumpSigned 2 7) ⟨s,f,229⟩).bind (X86Routine.run program [263] n) := by rfl
@[simp] theorem recovery_step_229 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [263] (n+1) ⟨s,f,229⟩ =
      (X86Routine.execute (.storeImmediate ⟨some 1,none,0,24⟩ 1) ⟨s,f,236⟩).bind (X86Routine.run program [263] n) := by rfl
@[simp] theorem recovery_step_236 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [263] (n+1) ⟨s,f,236⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 5 1 24)))) ⟨s,f,239⟩).bind (X86Routine.run program [263] n) := by rfl
@[simp] theorem recovery_step_239 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [263] (n+1) ⟨s,f,239⟩ =
      (X86Routine.execute (.control (.testWord 5 5)) ⟨s,f,241⟩).bind (X86Routine.run program [263] n) := by rfl
@[simp] theorem recovery_step_241 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [263] (n+1) ⟨s,f,241⟩ =
      (X86Routine.execute (.control (.jumpZero true 20)) ⟨s,f,243⟩).bind (X86Routine.run program [263] n) := by rfl
@[simp] theorem recovery_step_243 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [263] (n+1) ⟨s,f,243⟩ =
      (X86Routine.execute (.control (.block (.lea 2 ⟨some 5,none,0,16384⟩))) ⟨s,f,249⟩).bind (X86Routine.run program [263] n) := by rfl
@[simp] theorem recovery_step_249 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [263] (n+1) ⟨s,f,249⟩ =
      (X86Routine.execute (.control (.block (.store ⟨some 1,none,0,24⟩ 2))) ⟨s,f,252⟩).bind (X86Routine.run program [263] n) := by rfl
@[simp] theorem recovery_step_252 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [263] (n+1) ⟨s,f,252⟩ =
      (X86Routine.execute (.control (.testWord 2 2)) ⟨s,f,254⟩).bind (X86Routine.run program [263] n) := by rfl
@[simp] theorem recovery_step_254 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [263] (n+1) ⟨s,f,254⟩ =
      (X86Routine.execute (.control (.jumpZero false 7)) ⟨s,f,256⟩).bind (X86Routine.run program [263] n) := by rfl
@[simp] theorem recovery_step_256 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [263] (n+1) ⟨s,f,256⟩ =
      (X86Routine.execute (.storeImmediate ⟨some 1,none,0,24⟩ 1) ⟨s,f,263⟩).bind (X86Routine.run program [263] n) := by rfl
@[simp] theorem recovery_stop (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [263] n ⟨s,f,263⟩ = some ⟨s,f,263⟩ := by cases n <;> rfl

/-- The actual recovery region, entered only after playerstate == PST_LIVE.
ECX holds player_t; EBP is the zero just tested. The bob offset in EAX and the
caller stack are preserved. -/
theorem recovery_execution (s : X86Memory.State) (flags : Option Flags)
    (live : s.regs 5 = 0) :
    (X86Routine.run program [263] 30 ⟨s,flags,177⟩).map (fun t =>
      (t.pc,load32 t.core.memory (s.regs 1+(20#32)),load32 t.core.memory (s.regs 1+(24#32)),t.core.regs 0,t.core.regs 1,t.core.regs 4)) =
      some (263,(recover (load32 s.memory (s.regs 1+(20#32))) (load32 s.memory (s.regs 1+(24#32)))).1,
        (recover (load32 s.memory (s.regs 1+(20#32))) (load32 s.memory (s.regs 1+(24#32)))).2,s.regs 0,s.regs 1,s.regs 4) := by
  by_cases high : (load32 s.memory (s.regs 1+(20#32)) + load32 s.memory (s.regs 1+(24#32))).toInt ≤ 2686976 <;>
    by_cases low : (load32 s.memory (s.regs 1+(20#32)) + load32 s.memory (s.regs 1+(24#32))).toInt < 1343488 <;>
    by_cases positive : 0 < (load32 s.memory (s.regs 1+(24#32))).toInt <;>
    have lower : (1343488 ≤ (load32 s.memory (s.regs 1+(20#32)) + load32 s.memory (s.regs 1+(24#32))).toInt) ↔
      ¬ (load32 s.memory (s.regs 1+(20#32)) + load32 s.memory (s.regs 1+(24#32))).toInt < 1343488 := by omega
  all_goals have nonpos : (load32 s.memory (s.regs 1+(24#32))).toInt ≤ 0 ↔
      ¬ 0 < (load32 s.memory (s.regs 1+(24#32))).toInt := by omega
  all_goals simp [X86Routine.execute,X86Control.execute,X86Block.execute,
    X86Memory.execute,X86.execute,X86Block.Address.eval,put,write,blockPreservesFlags,
    live,load_store,cmp32_signed_le,cmp_ge,cmp_ge_prop,logical_le,logical_gt,recover,high,low,positive,lower,nonpos,-BitVec.toInt_add]
  all_goals by_cases zero : load32 s.memory (s.regs 1+(24#32)) = (0#32) <;>
    by_cases cancel : load32 s.memory (s.regs 1+(24#32)) + (16384#32) = (0#32) <;>
    simp [zero,cancel,X86Routine.execute,X86Control.execute,X86Block.execute,
      X86Memory.execute,X86.execute,X86Block.Address.eval,put,write,blockPreservesFlags,
      load_store,-BitVec.toInt_add]

@[simp] theorem fixed_add_raw (a b : Fixed) : (a+b).raw = a.raw+b.raw := rfl

theorem bits_zero (v : Int32) : v.toBitVec = (0#32) ↔ v = 0 := by
  change v.toBitVec = (0 : Int32).toBitVec ↔ v = 0
  exact Int32.toBitVec_inj

theorem raw_ite (p : Prop) [Decidable p] (a b : Fixed) : (if p then a else b).raw = if p then a.raw else b.raw := by split <;> rfl
theorem int_ite (p : Prop) [Decidable p] (a b : Int32) : (if p then a else b).toInt = if p then a.toInt else b.toInt := by split <;> rfl
theorem bits_ite (p : Prop) [Decidable p] (a b : Int32) : (if p then a else b).toBitVec = if p then a.toBitVec else b.toBitVec := by split <;> rfl
theorem word_int_ite (p : Prop) [Decidable p] (a b : BitVec 32) : (if p then a else b).toInt = if p then a.toInt else b.toInt := by split <;> rfl

theorem recover_runtime (v : ViewState) :
    recover v.height.raw.toBitVec v.delta.raw.toBitVec =
      ((v.recoverHeight).height.raw.toBitVec,(v.recoverHeight).delta.raw.toBitVec) := by
  unfold recover ViewState.recoverHeight
  simp only [Id.run,Pure.pure,Fixed.ofInt,raw_ite,int_ite,bits_ite,word_int_ite,fixed_add_raw,
    Int32.le_iff_toInt_le,Int32.lt_iff_toInt_lt,←Int32.toBitVec_add,Int32.toInt_toBitVec]
  by_cases high : (v.height.raw+v.delta.raw).toInt ≤ 2686976 <;>
    by_cases low : (v.height.raw+v.delta.raw).toInt < 1343488 <;>
    by_cases positive : 0 < v.delta.raw.toInt <;>
    simp [high,low,positive,bits_zero,←Int32.toBitVec_add,-Int32.toInt_add,-BitVec.toInt_add]
  all_goals rw [show v.delta.raw.toBitVec + (16384#32) = (v.delta.raw + (16384 : Int32)).toBitVec by rfl]
  all_goals simp only [bits_zero]

/-- Bind the proved recovery block to the actual decoded original bytes and
live runtime helper. No range restrictions on height or delta. -/
theorem recovery_observation (s : X86Memory.State) (flags : Option Flags) (v : ViewState)
    (live : s.regs 5 = 0)
    (height : load32 s.memory (s.regs 1+(20#32)) = v.height.raw.toBitVec)
    (delta : load32 s.memory (s.regs 1+(24#32)) = v.delta.raw.toBitVec) :
    (X86Routine.run (X86Routine.decodeAt code) [263] 30 ⟨s,flags,177⟩).map (fun t =>
      (t.pc,load32 t.core.memory (s.regs 1+(20#32)),load32 t.core.memory (s.regs 1+(24#32)),t.core.regs 0,t.core.regs 1,t.core.regs 4)) =
      some (263,(v.recoverHeight).height.raw.toBitVec,(v.recoverHeight).delta.raw.toBitVec,s.regs 0,s.regs 1,s.regs 4) := by
  have h := recovery_execution s flags live
  have valid : X86Routine.run program [263] 30 ⟨s,flags,177⟩ ≠ none := by
    intro hn
    rw [hn] at h
    contradiction
  rw [X86Routine.run_sound _ _ decoded _ _ _ valid]
  rw [height,delta,recover_runtime] at h
  exact h

@[simp] theorem clamp_step_263 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [295] (n+1) ⟨s,f,263⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 3 1 0)))) ⟨s,f,265⟩).bind (X86Routine.run program [295] n) := by rfl
@[simp] theorem clamp_step_265 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [295] (n+1) ⟨s,f,265⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 6 1 20)))) ⟨s,f,268⟩).bind (X86Routine.run program [295] n) := by rfl
@[simp] theorem clamp_step_268 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [295] (n+1) ⟨s,f,268⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 3 3 20)))) ⟨s,f,271⟩).bind (X86Routine.run program [295] n) := by rfl
@[simp] theorem clamp_step_271 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [295] (n+1) ⟨s,f,271⟩ =
      (X86Routine.execute (.control (.block (.arithmetic (.add 3 6)))) ⟨s,f,273⟩).bind (X86Routine.run program [295] n) := by rfl
@[simp] theorem clamp_step_273 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [295] (n+1) ⟨s,f,273⟩ =
      (X86Routine.execute (.control (.block (.arithmetic (.add 3 0)))) ⟨s,f,275⟩).bind (X86Routine.run program [295] n) := by rfl
@[simp] theorem clamp_step_275 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [295] (n+1) ⟨s,f,275⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 0 1 0)))) ⟨s,f,277⟩).bind (X86Routine.run program [295] n) := by rfl
@[simp] theorem clamp_step_277 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [295] (n+1) ⟨s,f,277⟩ =
      (X86Routine.execute (.control (.block (.store ⟨some 1,none,0,16⟩ 3))) ⟨s,f,280⟩).bind (X86Routine.run program [295] n) := by rfl
@[simp] theorem clamp_step_280 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [295] (n+1) ⟨s,f,280⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 0 0 60)))) ⟨s,f,283⟩).bind (X86Routine.run program [295] n) := by rfl
@[simp] theorem clamp_step_283 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [295] (n+1) ⟨s,f,283⟩ =
      (X86Routine.execute (.control (.block (.subEax 262144))) ⟨s,f,288⟩).bind (X86Routine.run program [295] n) := by rfl
@[simp] theorem clamp_step_288 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [295] (n+1) ⟨s,f,288⟩ =
      (X86Routine.execute (.compareRegisters 0 3) ⟨s,f,290⟩).bind (X86Routine.run program [295] n) := by rfl
@[simp] theorem clamp_step_290 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [295] (n+1) ⟨s,f,290⟩ =
      (X86Routine.execute (.jumpSigned 0 3) ⟨s,f,292⟩).bind (X86Routine.run program [295] n) := by rfl
@[simp] theorem clamp_step_292 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [295] (n+1) ⟨s,f,292⟩ =
      (X86Routine.execute (.control (.block (.store ⟨some 1,none,0,16⟩ 0))) ⟨s,f,295⟩).bind (X86Routine.run program [295] n) := by rfl
@[simp] theorem clamp_stop (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [295] n ⟨s,f,295⟩ = some ⟨s,f,295⟩ := by cases n <;> rfl

def viewObject (s : X86Memory.State) := load32 s.memory (s.regs 1)
def viewCandidate (s : X86Memory.State) :=
  load32 s.memory (viewObject s+(20#32)) + load32 s.memory (s.regs 1+(20#32)) + s.regs 0
def viewCeiling (s : X86Memory.State) := load32 s.memory (viewObject s+(60#32)) - (262144#32)
def clampWord (candidate ceiling : Word) :=
  if candidate.toInt ≤ ceiling.toInt then candidate else ceiling

theorem ceiling_execution (s : X86Memory.State) (flags : Option Flags)
    (safe : Apart (viewObject s+(60#32)) (s.regs 1+(16#32))) :
    (X86Routine.run program [295] 12 ⟨s,flags,263⟩).map (fun t =>
      (t.pc,load32 t.core.memory (s.regs 1+(16#32)),t.core.regs 1,t.core.regs 4)) =
      some (295,clampWord (viewCandidate s) (viewCeiling s),s.regs 1,s.regs 4) := by
  have keep (v : Word) : load32 (store32 s.memory (s.regs 1+(16#32)) v) (viewObject s+(60#32)) =
      load32 s.memory (viewObject s+(60#32)) := load_store_apart _ _ _ _ safe
  simp only [viewObject] at keep
  by_cases h : (viewCandidate s).toInt ≤ (viewCeiling s).toInt <;>
    simp only [viewCandidate,viewCeiling,viewObject] at h <;>
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      X86.execute,X86Block.Address.eval,put,write,eax,ebx,edx,blockPreservesFlags,load_store,
      cmp_ge_prop,viewCandidate,viewCeiling,viewObject,clampWord,keep,h,
      -BitVec.toInt_add,-BitVec.toInt_sub]

theorem clamp_runtime (a b : Fixed) : clampWord a.raw.toBitVec b.raw.toBitVec = (min a.raw b.raw).toBitVec := by
  change clampWord a.raw.toBitVec b.raw.toBitVec = (if a.raw ≤ b.raw then a.raw else b.raw).toBitVec
  simp only [clampWord,Int32.toInt_toBitVec,Int32.le_iff_toInt_le]
  split <;> rfl

theorem ceiling_observation (s : X86Memory.State) (flags : Option Flags)
    (body : Motion) (height offset : Fixed)
    (safe : Apart (viewObject s+(60#32)) (s.regs 1+(16#32)))
    (hz : load32 s.memory (viewObject s+(20#32)) = body.z.raw.toBitVec)
    (hh : load32 s.memory (s.regs 1+(20#32)) = height.raw.toBitVec)
    (hc : load32 s.memory (viewObject s+(60#32)) = body.ceilingz.raw.toBitVec)
    (ho : s.regs 0 = offset.raw.toBitVec) :
    (X86Routine.run (X86Routine.decodeAt code) [295] 12 ⟨s,flags,263⟩).map (fun t =>
      (t.pc,load32 t.core.memory (s.regs 1+(16#32)),t.core.regs 1,t.core.regs 4)) =
      some (295,(ViewState.clampZ body height offset).raw.toBitVec,s.regs 1,s.regs 4) := by
  have h := ceiling_execution s flags safe
  have valid : X86Routine.run program [295] 12 ⟨s,flags,263⟩ ≠ none := by
    intro hn; rw [hn] at h; contradiction
  rw [X86Routine.run_sound _ _ decoded _ _ _ valid,h]
  unfold viewCandidate viewCeiling
  rw [hz,hh,hc,ho]
  change some (295,clampWord (body.z+height+offset).raw.toBitVec
    (body.ceilingz-Fixed.ofInt 4).raw.toBitVec,s.regs 1,s.regs 4) = _
  rw [clamp_runtime]
  rfl

@[simp] theorem airborne_step_115 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [295] (n+1) ⟨s,f,115⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 0 1 0)))) ⟨s,f,117⟩).bind (X86Routine.run program [295] n) := by rfl
@[simp] theorem airborne_step_117 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [295] (n+1) ⟨s,f,117⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 2 1 20)))) ⟨s,f,120⟩).bind (X86Routine.run program [295] n) := by rfl
@[simp] theorem airborne_step_120 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [295] (n+1) ⟨s,f,120⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 0 0 20)))) ⟨s,f,123⟩).bind (X86Routine.run program [295] n) := by rfl
@[simp] theorem airborne_step_123 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [295] (n+1) ⟨s,f,123⟩ =
      (X86Routine.execute (.control (.block (.arithmetic (.add 0 2)))) ⟨s,f,125⟩).bind (X86Routine.run program [295] n) := by rfl
@[simp] theorem airborne_step_125 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [295] (n+1) ⟨s,f,125⟩ =
      (X86Routine.execute (.jump 162) ⟨s,f,130⟩).bind (X86Routine.run program [295] n) := by rfl

@[simp] theorem load_pointer_after_z (m : Memory) (p v : Word) :
    load32 (store32 m (p+(16#32)) v) p = load32 m p := by
  apply load_store_apart
  have h := slots_apart p 0 4 (by decide)
  change Apart (p+(0#32)) (p+(16#32)) at h
  simpa only [BitVec.add_zero] using h
@[simp] theorem load_height_after_z (m : Memory) (p v : Word) :
    load32 (store32 m (p+(16#32)) v) (p+(20#32)) = load32 m (p+(20#32)) :=
  load_store_apart _ _ _ _ (slots_apart p 5 4 (by decide))


theorem airborne_tail (s : X86Memory.State) (f : Option Flags) (extra : Nat) :
    (X86Routine.run program [295] (extra+6) ⟨s,f,115⟩).map (fun t =>
      (t.pc,load32 t.core.memory (s.regs 1+(16#32)),t.core.regs 1,t.core.regs 4)) =
      some (295,load32 s.memory (load32 s.memory (s.regs 1)+(20#32)) + load32 s.memory (s.regs 1+(20#32)),s.regs 1,s.regs 4) := by
  simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
    X86.execute,X86Block.Address.eval,put,write,eax,blockPreservesFlags,load_store]

/-- The final airborne overwrite. Incoming view Z is unconstrained: neither
its original value nor an earlier ceiling clamp can affect this result. -/
theorem airborne_observation (s : X86Memory.State) (flags : Option Flags)
    (body : Motion) (height : Fixed)
    (hz : load32 s.memory (viewObject s+(20#32)) = body.z.raw.toBitVec)
    (hh : load32 s.memory (s.regs 1+(20#32)) = height.raw.toBitVec) :
    (X86Routine.run (X86Routine.decodeAt code) [295] 6 ⟨s,flags,115⟩).map (fun t =>
      (t.pc,load32 t.core.memory (s.regs 1+(16#32)),t.core.regs 1,t.core.regs 4)) =
      some (295,(body.z+height).raw.toBitVec,s.regs 1,s.regs 4) := by
  have h := airborne_tail s flags 0
  have valid : X86Routine.run program [295] 6 ⟨s,flags,115⟩ ≠ none := by
    intro hn; rw [hn] at h; contradiction
  rw [X86Routine.run_sound _ _ decoded _ _ _ valid,h]
  change some (295,load32 s.memory (viewObject s+(20#32)) + load32 s.memory (s.regs 1+(20#32)),s.regs 1,s.regs 4) = _
  rw [hz,hh]
  rfl

/-- Any earlier view-Z store is irrelevant to the final overwrite, provided
it leaves the object's Z intact. Includes any result of the early clamp. -/
theorem airborne_previous_store (s : X86Memory.State) (flags : Option Flags)
    (body : Motion) (height : Fixed) (previousZ : Word)
    (safe : Apart (viewObject s+(20#32)) (s.regs 1+(16#32)))
    (hz : load32 s.memory (viewObject s+(20#32)) = body.z.raw.toBitVec)
    (hh : load32 s.memory (s.regs 1+(20#32)) = height.raw.toBitVec) :
    (X86Routine.run (X86Routine.decodeAt code) [295] 6
      ⟨{s with memory := store32 s.memory (s.regs 1+(16#32)) previousZ},flags,115⟩).map (fun t =>
      (t.pc,load32 t.core.memory (s.regs 1+(16#32)),t.core.regs 1,t.core.regs 4)) =
      some (295,(body.z+height).raw.toBitVec,s.regs 1,s.regs 4) := by
  apply airborne_observation {s with memory := store32 s.memory (s.regs 1+(16#32)) previousZ} flags body height
  · simp only [viewObject,load_pointer_after_z]
    exact (load_store_apart _ _ _ _ safe).trans hz
  · simpa only [load_height_after_z] using hh

end Doom.Proofs.PlayerHeight
