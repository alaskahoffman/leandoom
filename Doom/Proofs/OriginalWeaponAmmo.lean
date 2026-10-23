import Doom.Proofs.E1M1WeaponReadyReset
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.WeaponAmmo
open Verification X86 X86Memory X86Control BlockSummary
def entryBytes : List UInt8 := [0x53,0x51,0x52,0x56,0x8b,0x58,0x70,0x8d,0x14,0x9d,0x0,0x0,0x0,0x0,0x29,0xda,0x8b,0x1c,0xd5,0x90,0x2d,0x1,0x0,0x8b,0x50,0x70,0x83,0xfa,0x6,0xf,0x85,0xf3,0xfc,0xff,0xff,0xba,0x28,0x0,0x0,0x0,0xe9,0xfa,0xfc,0xff,0xff]
def decisionBytes : List UInt8 := [0x83,0xfa,0x8,0x75,0x7,0xba,0x2,0x0,0x0,0x0,0xeb,0x5,0xba,0x1,0x0,0x0,0x0,0x83,0xfb,0x5,0x74,0x9,0x3b,0x94,0x98,0x9c,0x0,0x0,0x0,0x7f,0xa,0xb8,0x1,0x0,0x0,0x0,0x5e,0x5a,0x59,0x5b,0xc3]
def bytesProgram (entry decision : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2d460 ≤ pc ∧ pc < 0x2d48d then X86Routine.decodeAt entry (pc-0x2d460)
  else if 0x2d176 ≤ pc ∧ pc < 0x2d19f then X86Routine.decodeAt decision (pc-0x2d176) else none
def program := bytesProgram entryBytes decisionBytes
def listed : X86Routine.Program
  | 0x2d460 => some (.push 3,1)
  | 0x2d461 => some (.push 1,1)
  | 0x2d462 => some (.push 2,1)
  | 0x2d463 => some (.push 6,1)
  | 0x2d464 => some (.control (.block (.legacy (.load 3 0 112))),3)
  | 0x2d467 => some (.control (.block (.lea 2 ⟨none,some 3,2,0⟩)),7)
  | 0x2d46e => some (.control (.block (.arithmetic (.sub 2 3))),2)
  | 0x2d470 => some (.control (.block (.load 3 ⟨none,some 2,3,0x12d90⟩)),7)
  | 0x2d477 => some (.control (.block (.legacy (.load 2 0 112))),3)
  | 0x2d47a => some (.compareRegister 2 6,3)
  | 0x2d47d => some (.control (.jumpZero false (-781)),6)
  | 0x2d483 => some (.immediate 2 40,5)
  | 0x2d488 => some (.jump (-774),5)
  | 0x2d176 => some (.compareRegister 2 8,3)
  | 0x2d179 => some (.control (.jumpZero false 7),2)
  | 0x2d17b => some (.immediate 2 2,5)
  | 0x2d180 => some (.jump 5,2)
  | 0x2d182 => some (.immediate 2 1,5)
  | 0x2d187 => some (.compareRegister 3 5,3)
  | 0x2d18a => some (.control (.jumpZero true 9),2)
  | 0x2d18c => some (.control (.cmpMemory 2 ⟨some 0,some 3,2,156⟩),7)
  | 0x2d193 => some (.jumpSigned 2 10,2)
  | 0x2d195 => some (.immediate 0 1,5)
  | 0x2d19a => some (.pop 6,1)
  | 0x2d19b => some (.pop 2,1)
  | 0x2d19c => some (.pop 1,1)
  | 0x2d19d => some (.pop 3,1)
  | 0x2d19e => some (.ret,1)
  | _ => none
theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide
@[local simp] theorem step_2d47a (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d187] (n+1) ⟨s,f,0x2d47a⟩ =
      (X86Routine.execute (.compareRegister 2 6) ⟨s,f,0x2d47d⟩).bind (X86Routine.run listed [0x2d187] n) := by rfl
@[local simp] theorem step_2d47d (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d187] (n+1) ⟨s,f,0x2d47d⟩ =
      (X86Routine.execute (.control (.jumpZero false (-781))) ⟨s,f,0x2d483⟩).bind (X86Routine.run listed [0x2d187] n) := by rfl
@[local simp] theorem step_2d483 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d187] (n+1) ⟨s,f,0x2d483⟩ =
      (X86Routine.execute (.immediate 2 40) ⟨s,f,0x2d488⟩).bind (X86Routine.run listed [0x2d187] n) := by rfl
@[local simp] theorem step_2d488 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d187] (n+1) ⟨s,f,0x2d488⟩ =
      (X86Routine.execute (.jump (-774)) ⟨s,f,0x2d48d⟩).bind (X86Routine.run listed [0x2d187] n) := by rfl
@[local simp] theorem step_2d176 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d187] (n+1) ⟨s,f,0x2d176⟩ =
      (X86Routine.execute (.compareRegister 2 8) ⟨s,f,0x2d179⟩).bind (X86Routine.run listed [0x2d187] n) := by rfl
@[local simp] theorem step_2d179 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d187] (n+1) ⟨s,f,0x2d179⟩ =
      (X86Routine.execute (.control (.jumpZero false 7)) ⟨s,f,0x2d17b⟩).bind (X86Routine.run listed [0x2d187] n) := by rfl
@[local simp] theorem step_2d17b (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d187] (n+1) ⟨s,f,0x2d17b⟩ =
      (X86Routine.execute (.immediate 2 2) ⟨s,f,0x2d180⟩).bind (X86Routine.run listed [0x2d187] n) := by rfl
@[local simp] theorem step_2d180 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d187] (n+1) ⟨s,f,0x2d180⟩ =
      (X86Routine.execute (.jump 5) ⟨s,f,0x2d182⟩).bind (X86Routine.run listed [0x2d187] n) := by rfl
@[local simp] theorem step_2d182 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d187] (n+1) ⟨s,f,0x2d182⟩ =
      (X86Routine.execute (.immediate 2 1) ⟨s,f,0x2d187⟩).bind (X86Routine.run listed [0x2d187] n) := by rfl
@[local simp] theorem stop_2d47a_2d187 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d187] n ⟨s,f,0x2d187⟩=some ⟨s,f,0x2d187⟩ := by cases n <;> rfl
@[local simp] theorem step_2d187 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d195,0x2d19f] (n+1) ⟨s,f,0x2d187⟩ =
      (X86Routine.execute (.compareRegister 3 5) ⟨s,f,0x2d18a⟩).bind (X86Routine.run listed [0x2d195,0x2d19f] n) := by rfl
@[local simp] theorem step_2d18a (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d195,0x2d19f] (n+1) ⟨s,f,0x2d18a⟩ =
      (X86Routine.execute (.control (.jumpZero true 9)) ⟨s,f,0x2d18c⟩).bind (X86Routine.run listed [0x2d195,0x2d19f] n) := by rfl
@[local simp] theorem step_2d18c (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d195,0x2d19f] (n+1) ⟨s,f,0x2d18c⟩ =
      (X86Routine.execute (.control (.cmpMemory 2 ⟨some 0,some 3,2,156⟩)) ⟨s,f,0x2d193⟩).bind (X86Routine.run listed [0x2d195,0x2d19f] n) := by rfl
@[local simp] theorem step_2d193 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d195,0x2d19f] (n+1) ⟨s,f,0x2d193⟩ =
      (X86Routine.execute (.jumpSigned 2 10) ⟨s,f,0x2d195⟩).bind (X86Routine.run listed [0x2d195,0x2d19f] n) := by rfl
@[local simp] theorem stop_2d187_2d195 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d195,0x2d19f] n ⟨s,f,0x2d195⟩=some ⟨s,f,0x2d195⟩ := by cases n <;> rfl
@[local simp] theorem stop_2d187_2d19f (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d195,0x2d19f] n ⟨s,f,0x2d19f⟩=some ⟨s,f,0x2d19f⟩ := by cases n <;> rfl

def saved (s : X86Memory.State) := X86Routine.pushWord (X86Routine.pushWord
  (X86Routine.pushWord (X86Routine.pushWord s (s.regs 3)) (s.regs 1)) (s.regs 2)) (s.regs 6)
def weapon (s : X86Memory.State) := load32 (saved s).memory (s.regs 0+(112#32))
def ammoType (s : X86Memory.State) := load32 (saved s).memory ((((weapon s <<< 2)-weapon s) <<< 3)+(0x12d90#32))
def prepared (s : X86Memory.State) := put (put (saved s) 3 (ammoType s)) 2 (weapon s)
theorem prepare_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x2d47a] 9 ⟨s,f,0x2d460⟩=some ⟨prepared s,none,0x2d47a⟩ := by
  let a := X86Routine.pushWord s (s.regs 3)
  let b := X86Routine.pushWord a (s.regs 1)
  let c := X86Routine.pushWord b (s.regs 2)
  let d := saved s
  let e := put d 3 (weapon s)
  let g := put e 2 (weapon s <<< 2)
  let k := put g 2 ((weapon s <<< 2)-weapon s)
  let l := put k 3 (ammoType s)
  have path : X86Routine.Prefix listed [0x2d47a] 9 ⟨s,f,0x2d460⟩ ⟨prepared s,none,0x2d47a⟩ := by
    apply X86Routine.Prefix.step (middle := ⟨a,f,0x2d461⟩) (by simp) (by rfl) rfl
    apply X86Routine.Prefix.step (middle := ⟨b,f,0x2d462⟩) (by simp) (by rfl) rfl
    apply X86Routine.Prefix.step (middle := ⟨c,f,0x2d463⟩) (by simp) (by rfl) rfl
    apply X86Routine.Prefix.step (middle := ⟨d,f,0x2d464⟩) (by simp) (by rfl) rfl
    apply X86Routine.Prefix.step (middle := ⟨e,f,0x2d467⟩) (by simp) (by rfl) (by rfl)
    apply X86Routine.Prefix.step (middle := ⟨g,f,0x2d46e⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,g,e,put,write])
    apply X86Routine.Prefix.step (middle := ⟨k,none,0x2d470⟩) (by simp) (by rfl) (by rfl)
    apply X86Routine.Prefix.step (middle := ⟨l,none,0x2d477⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,l,k,g,e,d,ammoType,put,write])
    apply X86Routine.Prefix.step (middle := ⟨prepared s,none,0x2d47a⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,blockPreservesFlags,
        prepared,l,k,g,e,d,put,write]
      funext r
      by_cases h2 : r=2 <;> by_cases h3 : r=3 <;> simp_all [write]
      rfl)
    exact X86Routine.Prefix.nil _
  have run := path.run 0
  have run : X86Routine.run listed [0x2d47a] 9 ⟨s,f,0x2d460⟩=some ⟨prepared s,none,0x2d47a⟩ := by
    simpa [X86Routine.run] using run
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

def cost (w : Word) : Word := if w=(6#32) then 40 else if w=(8#32) then 2 else 1
def charged (s : X86Memory.State) : X86Control.State :=
  ⟨put s 2 (cost (s.regs 2)),some (compare32 (s.regs 2) (if s.regs 2=(6#32) then 6 else 8)),0x2d187⟩
theorem cost_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x2d187] 6 ⟨s,f,0x2d47a⟩=some (charged s) := by
  have run : X86Routine.run listed [0x2d187] 6 ⟨s,f,0x2d47a⟩=some (charged s) := by
    by_cases h6 : s.regs 2=(6#32) <;> by_cases h8 : s.regs 2=(8#32) <;>
      simp [X86Routine.execute,X86Control.execute,charged,cost,put,write,cmp32_zero,h6,h8]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

def available (s : X86Memory.State) := load32 s.memory (s.regs 0+(s.regs 3 <<< 2)+(156#32))
abbrev allowed (s : X86Memory.State) : Prop := s.regs 3=(5#32) ∨ (s.regs 2).toInt ≤ (available s).toInt
def decision (s : X86Memory.State) : X86Control.State :=
  ⟨s,some (if s.regs 3=(5#32) then compare32 (s.regs 3) 5 else compare32 (s.regs 2) (available s)),
    if allowed s then 0x2d195 else 0x2d19f⟩
theorem decision_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x2d195,0x2d19f] 4 ⟨s,f,0x2d187⟩=some (decision s) := by
  have run : X86Routine.run listed [0x2d195,0x2d19f] 4 ⟨s,f,0x2d187⟩=some (decision s) := by
    by_cases noammo : s.regs 3=(5#32) <;> by_cases enough : (s.regs 2).toInt ≤ (available s).toInt <;>
      simp only [available] at enough <;>
      simp [X86Routine.execute,X86Control.execute,X86Block.Address.eval,decision,allowed,available,
        cmp32_zero,cmp32_signed_le,noammo,enough]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

def returned (s : X86Memory.State) (f : Option Flags) : X86Control.State :=
  let t := PspriteLoop.popped (PspriteLoop.popped (PspriteLoop.popped (PspriteLoop.popped (put s 0 1) 6) 2) 1) 3
  ⟨put t 4 (t.regs 4+4),f,(load32 t.memory (t.regs 4)).toNat⟩
theorem return_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 6 ⟨s,f,0x2d195⟩ (returned s f) := by
  let a := put s 0 1
  let b := PspriteLoop.popped a 6
  let c := PspriteLoop.popped b 2
  let d := PspriteLoop.popped c 1
  let e := PspriteLoop.popped d 3
  have p : X86Routine.Prefix listed [] 6 ⟨s,f,0x2d195⟩ (returned s f) := by
    apply X86Routine.Prefix.step (middle := ⟨a,f,0x2d19a⟩) (by simp) (by rfl) rfl
    apply X86Routine.Prefix.step (middle := ⟨b,f,0x2d19b⟩) (by simp) (by rfl) rfl
    apply X86Routine.Prefix.step (middle := ⟨c,f,0x2d19c⟩) (by simp) (by rfl) rfl
    apply X86Routine.Prefix.step (middle := ⟨d,f,0x2d19d⟩) (by simp) (by rfl) rfl
    apply X86Routine.Prefix.step (middle := ⟨e,f,0x2d19e⟩) (by simp) (by rfl) rfl
    apply X86Routine.Prefix.step (middle := returned s f) (by simp) (by rfl) rfl
    exact X86Routine.Prefix.nil _
  exact p.transfer program [] decoded (by simp)

private theorem prefix_trans {p stops n m s t u}
    (a : X86Routine.Prefix p stops n s t) (b : X86Routine.Prefix p stops m t u) :
    X86Routine.Prefix p stops (n+m) s u := by
  induction a with
  | nil => simpa using b
  | @step n s middle last op len active decoded executed rest ih =>
    simpa only [Nat.succ_add] using X86Routine.Prefix.step active decoded executed (ih b)
def checked (s : X86Memory.State) := decision (charged (prepared s)).core
/-- Failure stops at the actual fallback-selection entry, not a fabricated return. -/
def result (s : X86Memory.State) :=
  if allowed (charged (prepared s)).core then returned (checked s).core (checked s).flags else checked s

theorem check_execution (s : X86Memory.State) (f : Option Flags) :
    ∃ n, n≤19 ∧ X86Routine.Prefix program [] n ⟨s,f,0x2d460⟩ (checked s) := by
  obtain ⟨n,hn,a,_⟩ := X86Routine.run_path (prepare_execution s f)
  obtain ⟨m,hm,b,_⟩ := X86Routine.run_path (cost_execution (prepared s) none)
  obtain ⟨k,hk,c,_⟩ := X86Routine.run_path (decision_execution (charged (prepared s)).core (charged (prepared s)).flags)
  have eq : charged (prepared s)=⟨(charged (prepared s)).core,(charged (prepared s)).flags,0x2d187⟩ := rfl
  rw [←eq] at c
  exact ⟨n+m+k,by omega,prefix_trans (prefix_trans
    (a.transfer program [] (by intros; rfl) (by simp))
    (b.transfer program [] (by intros; rfl) (by simp)))
    (c.transfer program [] (by intros; rfl) (by simp))⟩
theorem execution (s : X86Memory.State) (f : Option Flags) :
    ∃ n, n≤25 ∧ X86Routine.Prefix program [] n ⟨s,f,0x2d460⟩ (result s) := by
  obtain ⟨n,hn,a⟩ := check_execution s f
  by_cases h : allowed (charged (prepared s)).core
  · have eq : checked s=⟨(checked s).core,(checked s).flags,0x2d195⟩ := by simp [checked,decision,h]
    have b := return_execution (checked s).core (checked s).flags
    rw [←eq] at b
    exact ⟨n+6,by omega,by simpa only [result,if_pos h] using prefix_trans a b⟩
  · exact ⟨n,by omega,by simpa only [result,if_neg h] using a⟩


/-- The memory relation is evaluated after the real pushes, so even stack/data
aliasing is not silently erased. A caller transports its layout invariant here. -/
structure Inputs (s : X86Memory.State) (w : Fin 3) (ammo : Int32) : Prop where
  weaponValue : weapon s=BitVec.ofNat 32 w.val
  typeValue : ammoType s=(if w.val=0 then 5 else if w.val=2 then 1 else 0)
  ammoValue : available (charged (prepared s)).core=ammo.toBitVec

theorem live_decision (s : X86Memory.State) (w : Fin 3) (ammo : Int32) (h : Inputs s w ammo) :
    (checked s).pc=(if Weapon.ammoAvailable w.val ammo then 0x2d195 else 0x2d19f) := by
  have kinds : w.val=0 ∨ w.val=1 ∨ w.val=2 := by omega
  have av := h.ammoValue
  rcases kinds with hw | hw | hw <;>
    simp [checked,decision,allowed,charged,prepared,cost,put,write,h.weaponValue,h.typeValue,hw,
      Weapon.ammoAvailable,Int32.lt_iff_toInt_lt] at *
  all_goals rw [←Int32.toInt_toBitVec ammo] at *
  all_goals simp_all [available,charged,prepared,cost,put,write,weapon,ammoType]
  all_goals congr 1 <;> omega

private theorem apart_offsets (base a b : Word) (h : ∀ i j : Fin 4,
    a + BitVec.ofNat 32 i.val ≠ b + BitVec.ofNat 32 j.val) : Apart (base+a) (base+b) := by
  intro i j eq
  apply h i j
  apply (BitVec.add_right_inj base).mp
  simpa only [BitVec.add_assoc] using eq

/-- The acceptance path actually restores its saved registers and returns to
its caller. No separation assumptions are required for the stack's own words. -/
theorem success_return (s : X86Memory.State) (h : allowed (charged (prepared s)).core) :
    (result s).pc=(load32 s.memory (s.regs 4)).toNat ∧
    (result s).core.regs 0=1 ∧ (result s).core.regs 1=s.regs 1 ∧
    (result s).core.regs 2=s.regs 2 ∧ (result s).core.regs 3=s.regs 3 ∧
    (result s).core.regs 4=s.regs 4+4 ∧ (result s).core.regs 6=s.regs 6 := by
  have h01 := apart_offsets (s.regs 4) (0#32) (4294967292#32) (by decide)
  have h02 := apart_offsets (s.regs 4) (0#32) (4294967288#32) (by decide)
  have h03 := apart_offsets (s.regs 4) (0#32) (4294967284#32) (by decide)
  have h04 := apart_offsets (s.regs 4) (0#32) (4294967280#32) (by decide)
  have h12 := apart_offsets (s.regs 4) (4294967292#32) (4294967288#32) (by decide)
  have h13 := apart_offsets (s.regs 4) (4294967292#32) (4294967284#32) (by decide)
  have h14 := apart_offsets (s.regs 4) (4294967292#32) (4294967280#32) (by decide)
  have h23 := apart_offsets (s.regs 4) (4294967288#32) (4294967284#32) (by decide)
  have h24 := apart_offsets (s.regs 4) (4294967288#32) (4294967280#32) (by decide)
  have h34 := apart_offsets (s.regs 4) (4294967284#32) (4294967280#32) (by decide)
  simp only [result,if_pos h]
  simp only [BitVec.add_zero] at h01 h02 h03 h04
  simp [returned,checked,decision,charged,prepared,PspriteLoop.popped,put,write,saved,
    X86Routine.pushWord,BitVec.sub_eq_add_neg,BitVec.add_assoc,load_store,
    load_store_apart _ _ _ _ h01,
    load_store_apart _ _ _ _ h02,
    load_store_apart _ _ _ _ h03,
    load_store_apart _ _ _ _ h04,
    load_store_apart _ _ _ _ h12,
    load_store_apart _ _ _ _ h13,
    load_store_apart _ _ _ _ h14,
    load_store_apart _ _ _ _ h23,
    load_store_apart _ _ _ _ h24,
    load_store_apart _ _ _ _ h34]
end Doom.Proofs.WeaponAmmo
