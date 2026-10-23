import Doom.Proofs.OriginalPlayerBob
import Doom.PlayerDamage

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.PlayerArmor
open Verification X86 X86Memory X86Control BlockSummary

def code : List UInt8 := [0x8b,0x55,0x28,0x85,0xd2,0x74,0x3a,0x83,0xfa,0x1,0x75,0x10,0xbb,0x3,0x0,0x0,0x0,0x89,0xfa,0x89,0xf8,0xc1,0xfa,0x1f,0xf7,0xfb,0xeb,0xb,0x89,0xfa,0x89,0xf8,0xc1,0xfa,0x1f,0x2b,0xc2,0xd1,0xf8,0x8b,0x4d,0x24,0x39,0xc8,0x7c,0x9,0x89,0xc8,0xc7,0x45,0x28,0x0,0x0,0x0,0x0,0x8b,0x55,0x24,0x29,0xc2,0x29,0xc7,0x89,0x55,0x24]
def program (pc : Nat) := if 0x2a5d5 ≤ pc ∧ pc < 0x2a616 then X86Routine.decodeAt code (pc-0x2a5d5) else none

def listed : X86Routine.Program
  | 0x2a5d5 => some (.control (.block (.legacy (.load 2 5 40))),3)
  | 0x2a5d8 => some (.control (.testWord 2 2),2)
  | 0x2a5da => some (.control (.jumpZero true 58),2)
  | 0x2a5dc => some (.compareRegister 2 1,3)
  | 0x2a5df => some (.control (.jumpZero false 16),2)
  | 0x2a5e1 => some (.immediate 3 3,5)
  | 0x2a5e6 => some (.control (.block (.legacy (.mov 2 7))),2)
  | 0x2a5e8 => some (.control (.block (.legacy (.mov 0 7))),2)
  | 0x2a5ea => some (.sar 2 31,3)
  | 0x2a5ed => some (.signedDivide 3,2)
  | 0x2a5ef => some (.jump 11,2)
  | 0x2a5f1 => some (.control (.block (.legacy (.mov 2 7))),2)
  | 0x2a5f3 => some (.control (.block (.legacy (.mov 0 7))),2)
  | 0x2a5f5 => some (.sar 2 31,3)
  | 0x2a5f8 => some (.control (.block (.arithmetic (.sub 0 2))),2)
  | 0x2a5fa => some (.sar 0 1,2)
  | 0x2a5fc => some (.control (.block (.legacy (.load 1 5 36))),3)
  | 0x2a5ff => some (.compareRegisters 0 1,2)
  | 0x2a601 => some (.jumpSigned 3 9,2)
  | 0x2a603 => some (.control (.block (.legacy (.mov 0 1))),2)
  | 0x2a605 => some (.storeImmediate ⟨some 5,none,0,40⟩ 0,7)
  | 0x2a60c => some (.control (.block (.legacy (.load 2 5 36))),3)
  | 0x2a60f => some (.control (.block (.arithmetic (.sub 2 0))),2)
  | 0x2a611 => some (.control (.block (.arithmetic (.sub 7 0))),2)
  | 0x2a613 => some (.control (.block (.store ⟨some 5,none,0,36⟩ 2)),3)
  | _ => none

theorem decoded (pc : Nat) (h : listed pc ≠ none) : program pc = listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

theorem dividend (v : Word) : ((v.sshiftRight 31) ++ v).toInt = v.toInt := by
  have h : (v.sshiftRight 31 ++ v) = v.signExtend 64 := by
    ext i hi
    simp only [BitVec.getElem_append,BitVec.getElem_signExtend,BitVec.getElem_sshiftRight]
    split
    · simp_all
    · split
      · have he : i = 32 := by omega
        subst i
        simp [BitVec.msb_eq_getLsbD_last]
      · rfl
  rw [h,BitVec.toInt_signExtend_of_le (by decide)]

theorem third_safe (v : Word) :
    ¬(v.toInt.tdiv 3 < -2147483648 ∨ 2147483647 < v.toInt.tdiv 3) := by
  have lo := BitVec.le_toInt v
  have hi := BitVec.toInt_lt (x := v)
  have a := Int.tdiv_le_tdiv (by decide : (0:Int)<3) lo
  have b := Int.tdiv_le_tdiv (by decide : (0:Int)<3) (show v.toInt ≤ 2147483647 by omega)
  change (-715827882 : Int) ≤ v.toInt.tdiv 3 at a
  change v.toInt.tdiv 3 ≤ (715827882 : Int) at b
  omega

theorem cmp_lt (a b : Word) : ((compare32 a b).sign != (compare32 a b).overflow) = decide (a.toInt < b.toInt) := by
  have := PlayerHeight.cmp_ge a b
  cases h : ((compare32 a b).sign == (compare32 a b).overflow) <;> simp_all <;> omega

theorem third (v : Word) : BitVec.ofInt 32 (v.toInt.tdiv 3) = v.sdiv 3 := by
  apply BitVec.eq_of_toInt_eq
  simp [BitVec.toInt_sdiv]

def pointer (s : X86Memory.State) := s.regs 5
def armor (s : X86Memory.State) := load32 s.memory (pointer s+(36#32))
def kind (s : X86Memory.State) := load32 s.memory (pointer s+(40#32))
def quota (s : X86Memory.State) := (s.regs 7).sdiv (if kind s = (1#32) then (3#32) else (2#32))
def saved (s : X86Memory.State) := if (quota s).toInt < (armor s).toInt then quota s else armor s

def resultMemory (s : X86Memory.State) : Memory :=
  if kind s = (0#32) then s.memory else
    let m := if (quota s).toInt < (armor s).toInt then s.memory else store32 s.memory (pointer s+(40#32)) 0
    store32 m (pointer s+(36#32)) (armor s-saved s)
def remaining (s : X86Memory.State) := if kind s = (0#32) then s.regs 7 else s.regs 7-saved s

theorem armor_type_apart (p : Word) : Apart (p+36) (p+40) := by
  intro i j
  have hi := i.isLt
  have hj := j.isLt
  intro h
  have cancel : BitVec.ofNat 32 (36+i.val) = BitVec.ofNat 32 (40+j.val) := by
    simpa [BitVec.ofNat_add,BitVec.add_assoc] using congrArg (fun x => x-p) h
  have := congrArg BitVec.toNat cancel
  simp only [BitVec.toNat_ofNat] at this
  omega

theorem armor_read (s : X86Memory.State) :
    load32 (store32 s.memory (pointer s+(40#32)) 0) (pointer s+(36#32)) = armor s :=
  load_store_apart _ _ _ _ (armor_type_apart _)

@[simp] theorem step_0x2a5d5 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2a616] (n+1) ⟨s,f,0x2a5d5⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 2 5 40)))) ⟨s,f,0x2a5d8⟩).bind (X86Routine.run listed [0x2a616] n) := by rfl

@[simp] theorem step_0x2a5d8 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2a616] (n+1) ⟨s,f,0x2a5d8⟩ =
      (X86Routine.execute (.control (.testWord 2 2)) ⟨s,f,0x2a5da⟩).bind (X86Routine.run listed [0x2a616] n) := by rfl

@[simp] theorem step_0x2a5da (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2a616] (n+1) ⟨s,f,0x2a5da⟩ =
      (X86Routine.execute (.control (.jumpZero true 58)) ⟨s,f,0x2a5dc⟩).bind (X86Routine.run listed [0x2a616] n) := by rfl

@[simp] theorem step_0x2a5dc (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2a616] (n+1) ⟨s,f,0x2a5dc⟩ =
      (X86Routine.execute (.compareRegister 2 1) ⟨s,f,0x2a5df⟩).bind (X86Routine.run listed [0x2a616] n) := by rfl

@[simp] theorem step_0x2a5df (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2a616] (n+1) ⟨s,f,0x2a5df⟩ =
      (X86Routine.execute (.control (.jumpZero false 16)) ⟨s,f,0x2a5e1⟩).bind (X86Routine.run listed [0x2a616] n) := by rfl

@[simp] theorem step_0x2a5e1 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2a616] (n+1) ⟨s,f,0x2a5e1⟩ =
      (X86Routine.execute (.immediate 3 3) ⟨s,f,0x2a5e6⟩).bind (X86Routine.run listed [0x2a616] n) := by rfl

@[simp] theorem step_0x2a5e6 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2a616] (n+1) ⟨s,f,0x2a5e6⟩ =
      (X86Routine.execute (.control (.block (.legacy (.mov 2 7)))) ⟨s,f,0x2a5e8⟩).bind (X86Routine.run listed [0x2a616] n) := by rfl

@[simp] theorem step_0x2a5e8 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2a616] (n+1) ⟨s,f,0x2a5e8⟩ =
      (X86Routine.execute (.control (.block (.legacy (.mov 0 7)))) ⟨s,f,0x2a5ea⟩).bind (X86Routine.run listed [0x2a616] n) := by rfl

@[simp] theorem step_0x2a5ea (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2a616] (n+1) ⟨s,f,0x2a5ea⟩ =
      (X86Routine.execute (.sar 2 31) ⟨s,f,0x2a5ed⟩).bind (X86Routine.run listed [0x2a616] n) := by rfl

@[simp] theorem step_0x2a5ed (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2a616] (n+1) ⟨s,f,0x2a5ed⟩ =
      (X86Routine.execute (.signedDivide 3) ⟨s,f,0x2a5ef⟩).bind (X86Routine.run listed [0x2a616] n) := by rfl

@[simp] theorem step_0x2a5ef (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2a616] (n+1) ⟨s,f,0x2a5ef⟩ =
      (X86Routine.execute (.jump 11) ⟨s,f,0x2a5f1⟩).bind (X86Routine.run listed [0x2a616] n) := by rfl

@[simp] theorem step_0x2a5f1 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2a616] (n+1) ⟨s,f,0x2a5f1⟩ =
      (X86Routine.execute (.control (.block (.legacy (.mov 2 7)))) ⟨s,f,0x2a5f3⟩).bind (X86Routine.run listed [0x2a616] n) := by rfl

@[simp] theorem step_0x2a5f3 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2a616] (n+1) ⟨s,f,0x2a5f3⟩ =
      (X86Routine.execute (.control (.block (.legacy (.mov 0 7)))) ⟨s,f,0x2a5f5⟩).bind (X86Routine.run listed [0x2a616] n) := by rfl

@[simp] theorem step_0x2a5f5 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2a616] (n+1) ⟨s,f,0x2a5f5⟩ =
      (X86Routine.execute (.sar 2 31) ⟨s,f,0x2a5f8⟩).bind (X86Routine.run listed [0x2a616] n) := by rfl

@[simp] theorem step_0x2a5f8 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2a616] (n+1) ⟨s,f,0x2a5f8⟩ =
      (X86Routine.execute (.control (.block (.arithmetic (.sub 0 2)))) ⟨s,f,0x2a5fa⟩).bind (X86Routine.run listed [0x2a616] n) := by rfl

@[simp] theorem step_0x2a5fa (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2a616] (n+1) ⟨s,f,0x2a5fa⟩ =
      (X86Routine.execute (.sar 0 1) ⟨s,f,0x2a5fc⟩).bind (X86Routine.run listed [0x2a616] n) := by rfl

@[simp] theorem step_0x2a5fc (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2a616] (n+1) ⟨s,f,0x2a5fc⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 1 5 36)))) ⟨s,f,0x2a5ff⟩).bind (X86Routine.run listed [0x2a616] n) := by rfl

@[simp] theorem step_0x2a5ff (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2a616] (n+1) ⟨s,f,0x2a5ff⟩ =
      (X86Routine.execute (.compareRegisters 0 1) ⟨s,f,0x2a601⟩).bind (X86Routine.run listed [0x2a616] n) := by rfl

@[simp] theorem step_0x2a601 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2a616] (n+1) ⟨s,f,0x2a601⟩ =
      (X86Routine.execute (.jumpSigned 3 9) ⟨s,f,0x2a603⟩).bind (X86Routine.run listed [0x2a616] n) := by rfl

@[simp] theorem step_0x2a603 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2a616] (n+1) ⟨s,f,0x2a603⟩ =
      (X86Routine.execute (.control (.block (.legacy (.mov 0 1)))) ⟨s,f,0x2a605⟩).bind (X86Routine.run listed [0x2a616] n) := by rfl

@[simp] theorem step_0x2a605 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2a616] (n+1) ⟨s,f,0x2a605⟩ =
      (X86Routine.execute (.storeImmediate ⟨some 5,none,0,40⟩ 0) ⟨s,f,0x2a60c⟩).bind (X86Routine.run listed [0x2a616] n) := by rfl

@[simp] theorem step_0x2a60c (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2a616] (n+1) ⟨s,f,0x2a60c⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 2 5 36)))) ⟨s,f,0x2a60f⟩).bind (X86Routine.run listed [0x2a616] n) := by rfl

@[simp] theorem step_0x2a60f (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2a616] (n+1) ⟨s,f,0x2a60f⟩ =
      (X86Routine.execute (.control (.block (.arithmetic (.sub 2 0)))) ⟨s,f,0x2a611⟩).bind (X86Routine.run listed [0x2a616] n) := by rfl

@[simp] theorem step_0x2a611 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2a616] (n+1) ⟨s,f,0x2a611⟩ =
      (X86Routine.execute (.control (.block (.arithmetic (.sub 7 0)))) ⟨s,f,0x2a613⟩).bind (X86Routine.run listed [0x2a616] n) := by rfl

@[simp] theorem step_0x2a613 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2a616] (n+1) ⟨s,f,0x2a613⟩ =
      (X86Routine.execute (.control (.block (.store ⟨some 5,none,0,36⟩ 2))) ⟨s,f,0x2a616⟩).bind (X86Routine.run listed [0x2a616] n) := by rfl

@[simp] theorem finished (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2a616] n ⟨s,f,0x2a616⟩ = some ⟨s,f,0x2a616⟩ := by cases n <;> rfl

/-- The entire original armor block, with no restrictions on damage, armor,
armor type, player address, initial flags or other memory. All writes remain
in the shared byte memory, including unaligned and wrapping addresses. -/
theorem execution (s : X86Memory.State) (f : Option Flags) :
    (X86Routine.run listed [0x2a616] 24 ⟨s,f,0x2a5d5⟩).map
      (fun t => (t.core.regs 7,t.core.memory,t.core.regs 5,t.core.regs 4,t.core.regs 6,t.pc)) =
      some (remaining s,resultMemory s,s.regs 5,s.regs 4,s.regs 6,0x2a616) := by
  have half := PlayerHeight.half_word (s.regs 7)
  have div2 : BitVec.ofInt 32 ((s.regs 7).toInt.tdiv 2) = (s.regs 7).sdiv 2 := by
    apply BitVec.eq_of_toInt_eq
    simp [BitVec.toInt_sdiv]
  rw [div2] at half
  have ar := armor_read s
  dsimp [pointer,armor] at ar
  by_cases h0 : kind s = (0#32)
  · have h := h0
    dsimp [kind,pointer] at h
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,
      X86Memory.execute,put,write,logical32,blockPreservesFlags,h,remaining,resultMemory,h0]
  · by_cases h1 : kind s = (1#32) <;>
      by_cases hc : (quota s).toInt < (armor s).toInt
    all_goals
      have hz := h0
      have ho := h1
      have cap := hc
      simp [quota,h1,armor,pointer] at cap

      dsimp [kind,pointer] at hz ho
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,
        X86Memory.execute,X86.execute,put,write,blockPreservesFlags,X86Block.Address.eval,
        logical32,cmp32_zero,cmp_lt,PlayerHeight.cmp_ge_prop,← Int.not_lt,dividend,third_safe,third,half,hz,ho,cap,ar,
        remaining,resultMemory,saved,quota,armor,kind,pointer,h0,h1,hc]
      all_goals
        have notcap := Int.not_lt.mpr cap
        simp [notcap]

/-- The live helper is exactly the armor code previously inline in apply. -/
theorem live_inline (s : PlayerDamage.State) (d : Int32) :
    PlayerDamage.absorbArmor s d = (Id.run do
      let mut state := s
      let mut damage := d
      if state.armorType != 0 then
        let saved := damage / (if state.armorType == 1 then 3 else 2)
        let saved := min saved state.armor
        state := {state with armor := state.armor-saved, armorType := if state.armor ≤ saved then 0 else state.armorType}
        damage := damage-saved
      return (state,damage)) := by
  rfl

theorem memory_frame (s : X86Memory.State) (a : Word)
    (safeArmor : Apart a (pointer s+(36#32))) (safeType : Apart a (pointer s+(40#32))) :
    load32 (resultMemory s) a = load32 s.memory a := by
  unfold resultMemory
  split
  · rfl
  · rw [load_store_apart _ _ _ _ safeArmor]
    split
    · rfl
    · exact load_store_apart _ _ _ _ safeType

theorem live_values (s : X86Memory.State) (v : PlayerDamage.State) (d : Int32)
    (damage : s.regs 7 = d.toBitVec) (points : armor s = v.armor.toBitVec)
    (armorType : kind s = v.armorType.toBitVec) :
    (remaining s,load32 (resultMemory s) (pointer s+(36#32)),load32 (resultMemory s) (pointer s+(40#32))) =
      let out := PlayerDamage.absorbArmor v d
      (out.2.toBitVec,out.1.armor.toBitVec,out.1.armorType.toBitVec) := by
  have reverseApart : Apart (pointer s+(40#32)) (pointer s+(36#32)) := by
    intro i j h
    exact armor_type_apart (pointer s) j i h.symm
  have typeRead (m : Memory) (w : Word) := load_store_apart m (pointer s+(36#32)) (pointer s+(40#32)) w reverseApart
  have zero : kind s = (0#32) ↔ v.armorType = 0 := by
    rw [armorType]; exact Int32.toBitVec_inj (b := 0)
  have one : kind s = (1#32) ↔ v.armorType = 1 := by
    rw [armorType]; exact Int32.toBitVec_inj (b := 1)
  let q := d / (if v.armorType == 1 then 3 else 2)
  have quota_eq : quota s = q.toBitVec := by
    by_cases h : v.armorType = 1 <;> simp [quota,damage,one,q,h]
  have pointRead : load32 s.memory (pointer s+(36#32)) = v.armor.toBitVec := points
  have kindRead : load32 s.memory (pointer s+(40#32)) = v.armorType.toBitVec := armorType
  have qe : d / (if v.armorType == 1 then 3 else 2) = q := rfl
  simp only [beq_iff_eq] at qe
  simp only [remaining,resultMemory]
  by_cases hz : v.armorType = 0
  · simp [zero,hz,PlayerDamage.absorbArmor,damage,pointRead,kindRead]
  · have hn : ¬kind s = (0#32) := fun h => hz (zero.mp h)
    have min_eq (a b : Int32) : min a b = if a ≤ b then a else b := rfl
    by_cases hc : q.toInt < v.armor.toInt
    · have le : q ≤ v.armor := Int32.le_iff_toInt_le.mpr (by omega)
      have nle : ¬v.armor ≤ q := by rw [Int32.le_iff_toInt_le]; omega
      simp [hn,saved,quota_eq,points,hc,load_store,typeRead,pointRead,kindRead,damage,
        PlayerDamage.absorbArmor,hz,qe,min_eq,le,nle]
    · have le : v.armor ≤ q := Int32.le_iff_toInt_le.mpr (by omega)
      have minimum : min q v.armor = v.armor := by
        rw [min_eq]; split
        · apply Int32.le_antisymm <;> assumption
        · rfl
      simp [hn,saved,quota_eq,points,hc,load_store,typeRead,pointRead,kindRead,damage,
        PlayerDamage.absorbArmor,hz,qe,minimum]

/-- Replace the proposed instruction listing with decoded executable bytes. -/
theorem original_execution (s : X86Memory.State) (f : Option Flags) :
    (X86Routine.run program [0x2a616] 24 ⟨s,f,0x2a5d5⟩).map
      (fun t => (t.core.regs 7,t.core.memory,t.core.regs 5,t.core.regs 4,t.core.regs 6,t.pc)) =
      some (remaining s,resultMemory s,s.regs 5,s.regs 4,s.regs 6,0x2a616) := by
  have h := execution s f
  have valid : X86Routine.run listed [0x2a616] 24 ⟨s,f,0x2a5d5⟩ ≠ none := by
    intro hn
    rw [hn] at h
    contradiction
  rw [X86Routine.run_sound program listed decoded _ _ _ valid]
  exact h

/-- DOS armor absorption agrees with the helper called by PlayerDamage.apply,
for every signed 32-bit damage/armor/type and every matching byte memory. -/
theorem correspondence (s : X86Memory.State) (f : Option Flags) (v : PlayerDamage.State) (d : Int32)
    (damage : s.regs 7 = d.toBitVec) (points : armor s = v.armor.toBitVec)
    (armorType : kind s = v.armorType.toBitVec) :
    (X86Routine.run program [0x2a616] 24 ⟨s,f,0x2a5d5⟩).map
      (fun t => (t.core.regs 7,load32 t.core.memory (pointer s+(36#32)),
        load32 t.core.memory (pointer s+(40#32)))) =
      let out := PlayerDamage.absorbArmor v d
      some (out.2.toBitVec,out.1.armor.toBitVec,out.1.armorType.toBitVec) := by
  have h := original_execution s f
  cases hr : X86Routine.run program [0x2a616] 24 ⟨s,f,0x2a5d5⟩ with
  | none => simp [hr] at h
  | some t =>
    simp only [hr,Option.map_some,Option.some.injEq,Prod.mk.injEq] at h
    simp only [Option.map_some,h.1,h.2.1]
    exact congrArg some (live_values s v d damage points armorType)

end Doom.Proofs.PlayerArmor
