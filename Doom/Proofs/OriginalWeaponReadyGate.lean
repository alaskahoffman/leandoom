import Doom.Proofs.E1M1WeaponReady
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.WeaponReadyGate
open Verification X86 X86Memory X86Control BlockSummary

def code : List UInt8 := [0x83,0x79,0x74,0xa,0x75,0x6,0x83,0x79,0x20,0x0,0x75,0x21,0x8b,0x59,0x70,0x8d,0x4,0x9d,0x0,0x0,0x0,0x0,0x29,0xd8,0x31,0xd2,0x8b,0x1c,0xc5,0x98,0x2d,0x1,0x0,0x89,0xc8,0xe8,0xe5,0xfc,0xff,0xff,0x5f,0x5e,0x59,0x5b,0xc3,0xf6,0x41,0xf,0x1,0x74,0x2c,0x83,0xb9,0xbc,0x0,0x0,0x0,0x0,0x74,0xd,0x8b,0x71,0x70,0x83,0xfe,0x4,0x74,0x25,0x83,0xfe,0x6,0x74,0x20,0x89,0xc8,0xc7,0x81,0xbc,0x0,0x0,0x0,0x1,0x0,0x0,0x0,0xe8,0x83,0x0,0x0,0x0,0x5f,0x5e,0x59,0x5b,0xc3]
def bytesProgram (bs : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2d333 ≤ pc ∧ pc < 0x2d392 then X86Routine.decodeAt bs (pc-0x2d333) else none
def program := bytesProgram code

def listed : X86Routine.Program
  | 0x2d333 => some (.control (.cmpImmediate ⟨some 1,none,0,116⟩ 10),4)
  | 0x2d337 => some (.control (.jumpZero false 6),2)
  | 0x2d339 => some (.control (.cmpImmediate ⟨some 1,none,0,32⟩ 0),4)
  | 0x2d33d => some (.control (.jumpZero false 33),2)
  | 0x2d33f => some (.control (.block (.legacy (.load 3 1 112))),3)
  | 0x2d342 => some (.control (.block (.lea 0 ⟨none,some 3,2,0⟩)),7)
  | 0x2d349 => some (.control (.block (.arithmetic (.sub 0 3))),2)
  | 0x2d34b => some (.xorRegister 2 2,2)
  | 0x2d34d => some (.control (.block (.load 3 ⟨none,some 0,3,0x12d98⟩)),7)
  | 0x2d354 => some (.control (.block (.legacy (.mov 0 1))),2)
  | 0x2d356 => some (.call (-795),5)
  | 0x2d35b => some (.pop 7,1)
  | 0x2d35c => some (.pop 6,1)
  | 0x2d35d => some (.pop 1,1)
  | 0x2d35e => some (.pop 3,1)
  | 0x2d35f => some (.ret,1)
  | 0x2d360 => some (.testMemoryByte ⟨some 1,none,0,15⟩ 1,4)
  | 0x2d364 => some (.control (.jumpZero true 44),2)
  | 0x2d366 => some (.control (.cmpImmediate ⟨some 1,none,0,188⟩ 0),7)
  | 0x2d36d => some (.control (.jumpZero true 13),2)
  | 0x2d36f => some (.control (.block (.legacy (.load 6 1 112))),3)
  | 0x2d372 => some (.compareRegister 6 4,3)
  | 0x2d375 => some (.control (.jumpZero true 37),2)
  | 0x2d377 => some (.compareRegister 6 6,3)
  | 0x2d37a => some (.control (.jumpZero true 32),2)
  | 0x2d37c => some (.control (.block (.legacy (.mov 0 1))),2)
  | 0x2d37e => some (.storeImmediate ⟨some 1,none,0,188⟩ 1,10)
  | 0x2d388 => some (.call 131,5)
  | 0x2d38d => some (.pop 7,1)
  | 0x2d38e => some (.pop 6,1)
  | 0x2d38f => some (.pop 1,1)
  | 0x2d390 => some (.pop 3,1)
  | 0x2d391 => some (.ret,1)
  | _ => none

theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

@[local simp] theorem step_2d333 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d33f,0x2d360] (n+1) ⟨s,f,0x2d333⟩ =
      (X86Routine.execute (.control (.cmpImmediate ⟨some 1,none,0,116⟩ 10)) ⟨s,f,0x2d337⟩).bind (X86Routine.run listed [0x2d33f,0x2d360] n) := by rfl

@[local simp] theorem step_2d337 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d33f,0x2d360] (n+1) ⟨s,f,0x2d337⟩ =
      (X86Routine.execute (.control (.jumpZero false 6)) ⟨s,f,0x2d339⟩).bind (X86Routine.run listed [0x2d33f,0x2d360] n) := by rfl

@[local simp] theorem step_2d339 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d33f,0x2d360] (n+1) ⟨s,f,0x2d339⟩ =
      (X86Routine.execute (.control (.cmpImmediate ⟨some 1,none,0,32⟩ 0)) ⟨s,f,0x2d33d⟩).bind (X86Routine.run listed [0x2d33f,0x2d360] n) := by rfl

@[local simp] theorem step_2d33d (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d33f,0x2d360] (n+1) ⟨s,f,0x2d33d⟩ =
      (X86Routine.execute (.control (.jumpZero false 33)) ⟨s,f,0x2d33f⟩).bind (X86Routine.run listed [0x2d33f,0x2d360] n) := by rfl

@[local simp] theorem stop_2d333_2d33f (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d33f,0x2d360] n ⟨s,f,0x2d33f⟩=some ⟨s,f,0x2d33f⟩ := by cases n <;> rfl

@[local simp] theorem stop_2d333_2d360 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d33f,0x2d360] n ⟨s,f,0x2d360⟩=some ⟨s,f,0x2d360⟩ := by cases n <;> rfl

@[local simp] theorem step_2d360 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d392,0x2d37c,0x2d39c] (n+1) ⟨s,f,0x2d360⟩ =
      (X86Routine.execute (.testMemoryByte ⟨some 1,none,0,15⟩ 1) ⟨s,f,0x2d364⟩).bind (X86Routine.run listed [0x2d392,0x2d37c,0x2d39c] n) := by rfl

@[local simp] theorem step_2d364 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d392,0x2d37c,0x2d39c] (n+1) ⟨s,f,0x2d364⟩ =
      (X86Routine.execute (.control (.jumpZero true 44)) ⟨s,f,0x2d366⟩).bind (X86Routine.run listed [0x2d392,0x2d37c,0x2d39c] n) := by rfl

@[local simp] theorem step_2d366 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d392,0x2d37c,0x2d39c] (n+1) ⟨s,f,0x2d366⟩ =
      (X86Routine.execute (.control (.cmpImmediate ⟨some 1,none,0,188⟩ 0)) ⟨s,f,0x2d36d⟩).bind (X86Routine.run listed [0x2d392,0x2d37c,0x2d39c] n) := by rfl

@[local simp] theorem step_2d36d (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d392,0x2d37c,0x2d39c] (n+1) ⟨s,f,0x2d36d⟩ =
      (X86Routine.execute (.control (.jumpZero true 13)) ⟨s,f,0x2d36f⟩).bind (X86Routine.run listed [0x2d392,0x2d37c,0x2d39c] n) := by rfl

@[local simp] theorem step_2d36f (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d392,0x2d37c,0x2d39c] (n+1) ⟨s,f,0x2d36f⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 6 1 112)))) ⟨s,f,0x2d372⟩).bind (X86Routine.run listed [0x2d392,0x2d37c,0x2d39c] n) := by rfl

@[local simp] theorem step_2d372 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d392,0x2d37c,0x2d39c] (n+1) ⟨s,f,0x2d372⟩ =
      (X86Routine.execute (.compareRegister 6 4) ⟨s,f,0x2d375⟩).bind (X86Routine.run listed [0x2d392,0x2d37c,0x2d39c] n) := by rfl

@[local simp] theorem step_2d375 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d392,0x2d37c,0x2d39c] (n+1) ⟨s,f,0x2d375⟩ =
      (X86Routine.execute (.control (.jumpZero true 37)) ⟨s,f,0x2d377⟩).bind (X86Routine.run listed [0x2d392,0x2d37c,0x2d39c] n) := by rfl

@[local simp] theorem step_2d377 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d392,0x2d37c,0x2d39c] (n+1) ⟨s,f,0x2d377⟩ =
      (X86Routine.execute (.compareRegister 6 6) ⟨s,f,0x2d37a⟩).bind (X86Routine.run listed [0x2d392,0x2d37c,0x2d39c] n) := by rfl

@[local simp] theorem step_2d37a (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d392,0x2d37c,0x2d39c] (n+1) ⟨s,f,0x2d37a⟩ =
      (X86Routine.execute (.control (.jumpZero true 32)) ⟨s,f,0x2d37c⟩).bind (X86Routine.run listed [0x2d392,0x2d37c,0x2d39c] n) := by rfl

@[local simp] theorem stop_2d360_2d392 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d392,0x2d37c,0x2d39c] n ⟨s,f,0x2d392⟩=some ⟨s,f,0x2d392⟩ := by cases n <;> rfl

@[local simp] theorem stop_2d360_2d37c (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d392,0x2d37c,0x2d39c] n ⟨s,f,0x2d37c⟩=some ⟨s,f,0x2d37c⟩ := by cases n <;> rfl

@[local simp] theorem stop_2d360_2d39c (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d392,0x2d37c,0x2d39c] n ⟨s,f,0x2d39c⟩=some ⟨s,f,0x2d39c⟩ := by cases n <;> rfl

def pending (s : X86Memory.State) := load32 s.memory (s.regs 1+(116#32))
def health (s : X86Memory.State) := load32 s.memory (s.regs 1+(32#32))
def weapon (s : X86Memory.State) := load32 s.memory (s.regs 1+(112#32))
def latch (s : X86Memory.State) := load32 s.memory (s.regs 1+(188#32))
def attack (s : X86Memory.State) := s.memory (s.regs 1+(15#32)) &&& (1#8)
abbrev lowering (s : X86Memory.State) : Prop := pending s≠(10#32) ∨ health s=(0#32)
def choice (s : X86Memory.State) : X86Control.State :=
  ⟨s,some (if pending s≠(10#32) then compare32 (pending s) 10 else compare32 (health s) 0),
    if lowering s then 0x2d33f else 0x2d360⟩

theorem choice_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x2d33f,0x2d360] 4 ⟨s,f,0x2d333⟩=some (choice s) := by
  have run : X86Routine.run listed [0x2d33f,0x2d360] 4 ⟨s,f,0x2d333⟩=some (choice s) := by
    by_cases p : pending s=(10#32) <;> by_cases h : health s=(0#32) <;>
      simp only [pending,health] at p h <;>
      simp [X86Routine.execute,X86Control.execute,X86Block.Address.eval,
        choice,lowering,pending,health,cmp32_zero,p,h]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

def trigger (s : X86Memory.State) : X86Control.State :=
  if attack s=(0#8) then ⟨s,some (logical8 (attack s)),0x2d392⟩
  else if latch s=(0#32) then ⟨s,some (compare32 (latch s) 0),0x2d37c⟩
  else ⟨put s 6 (weapon s),some (compare32 (weapon s) (if weapon s=(4#32) then 4 else 6)),
    if weapon s=(4#32) ∨ weapon s=(6#32) then 0x2d39c else 0x2d37c⟩

theorem trigger_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x2d392,0x2d37c,0x2d39c] 9 ⟨s,f,0x2d360⟩=some (trigger s) := by
  have run : X86Routine.run listed [0x2d392,0x2d37c,0x2d39c] 9 ⟨s,f,0x2d360⟩=some (trigger s) := by
    by_cases a : attack s=(0#8) <;> by_cases l : latch s=(0#32) <;>
      by_cases w4 : weapon s=(4#32) <;> by_cases w6 : weapon s=(6#32) <;>
      simp only [attack,latch,weapon] at a l w4 w6 <;>
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
        X86Block.Address.eval,trigger,attack,latch,weapon,put,write,blockPreservesFlags,logical8,cmp32_zero,a,l,w4,w6]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

def downState (s : X86Memory.State) := load32 s.memory ((((weapon s <<< 2)-weapon s) <<< 3)+0x12d98)
def lowered (s : X86Memory.State) : X86Control.State :=
  ⟨X86Routine.pushWord (put (put (put s 0 (s.regs 1)) 2 0) 3 (downState s)) 0x2d35b,
    some (logical32 0),0x2d040⟩

theorem lower_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x2d040] 7 ⟨s,f,0x2d33f⟩=some (lowered s) := by
  have run : X86Routine.run listed [0x2d040] 7 ⟨s,f,0x2d33f⟩=some (lowered s) := by
    simp [X86Routine.run,listed,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      X86.execute,X86Block.Address.eval,put,write,lowered,downState,weapon,
      X86Routine.pushWord,blockPreservesFlags,logical32,BitVec.sub_eq_add_neg]
    funext r
    by_cases h0 : r=0 <;> by_cases h2 : r=2 <;> by_cases h3 : r=3 <;> by_cases h4 : r=4 <;> simp_all [write]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

def firing (s : X86Memory.State) (f : Option Flags) : X86Control.State :=
  ⟨X86Routine.pushWord {put s 0 (s.regs 1) with memory := store32 s.memory (s.regs 1+(188#32)) 1} 0x2d38d,f,0x2d410⟩

theorem fire_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x2d410] 3 ⟨s,f,0x2d37c⟩=some (firing s f) := by
  have run : X86Routine.run listed [0x2d410] 3 ⟨s,f,0x2d37c⟩=some (firing s f) := by
    simp [X86Routine.run,listed,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      X86Block.Address.eval,put,write,firing,X86Routine.pushWord,blockPreservesFlags]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

private theorem prefix_trans {p stops n m s t u}
    (a : X86Routine.Prefix p stops n s t) (b : X86Routine.Prefix p stops m t u) :
    X86Routine.Prefix p stops (n+m) s u := by
  induction a with
  | nil => simpa using b
  | @step n s middle last op len active decoded executed rest ih =>
    simpa only [Nat.succ_add] using X86Routine.Prefix.step active decoded executed (ih b)

/-- Exact decision suffix, stopping at real callees or the two bob entries.
No callee is replaced by a summary or assumed to return. -/
def result (s : X86Memory.State) : X86Control.State :=
  if lowering s then lowered s
  else let t := trigger s
       if t.pc=0x2d37c then firing t.core t.flags else t

theorem execution (s : X86Memory.State) (f : Option Flags) :
    ∃ n, n ≤ 16 ∧ X86Routine.Prefix program [] n ⟨s,f,0x2d333⟩ (result s) := by
  obtain ⟨n,hn,a,_⟩ := X86Routine.run_path (choice_execution s f)
  have a := a.transfer program [] (by intros; rfl) (by simp)
  by_cases low : lowering s
  · have e : choice s=⟨s,(choice s).flags,0x2d33f⟩ := by simp [choice,low]
    rw [e] at a
    obtain ⟨m,hm,b,_⟩ := X86Routine.run_path (lower_execution s (choice s).flags)
    have b := b.transfer program [] (by intros; rfl) (by simp)
    exact ⟨n+m,by omega,by simpa only [result,if_pos low] using prefix_trans a b⟩
  · have e : choice s=⟨s,(choice s).flags,0x2d360⟩ := by simp [choice,low]
    rw [e] at a
    obtain ⟨m,hm,b,_⟩ := X86Routine.run_path (trigger_execution s (choice s).flags)
    have b := b.transfer program [] (by intros; rfl) (by simp)
    have ab := prefix_trans a b
    by_cases fire : (trigger s).pc=0x2d37c
    · have e : trigger s=⟨(trigger s).core,(trigger s).flags,0x2d37c⟩ := by rw [←fire]
      rw [e] at ab
      obtain ⟨k,hk,c,_⟩ := X86Routine.run_path (fire_execution (trigger s).core (trigger s).flags)
      have c := c.transfer program [] (by intros; rfl) (by simp)
      exact ⟨n+m+k,by omega,by simpa only [result,if_neg low,if_pos fire] using prefix_trans ab c⟩
    · exact ⟨n+m,by omega,by simpa only [result,if_neg low,if_neg fire] using ab⟩

/-- The supported live pending sentinel is 9; DOS wp_nochange is 10. -/
def pendingWord (p : Nat) : Word := if p=9 then 10 else BitVec.ofNat 32 p
structure Inputs (s : X86Memory.State) (w : Fin 3) (p : Nat) (hp : Int32) (a : Bool) : Prop where
  pendingSupported : p≤2 ∨ p=9
  pendingValue : pending s=pendingWord p
  healthValue : health s=hp.toBitVec
  weaponValue : weapon s=BitVec.ofNat 32 w.val
  attackValue : (attack s≠(0#8)) ↔ a=true

theorem live_lowering (s : X86Memory.State) (w : Fin 3) (p : Nat) (hp : Int32) (a : Bool)
    (h : Inputs s w p hp a) : lowering s ↔ (Weapon.supported p || hp==0)=true := by
  have zero : hp.toBitVec=(0#32) ↔ hp=0 := by
    constructor
    · intro e; exact Int32.toBitVec_inj.mp e
    · intro e; subst hp; rfl
  rcases h.pendingSupported with small | sentinel
  · have cases : p=0 ∨ p=1 ∨ p=2 := by omega
    rcases cases with rfl | rfl | rfl <;>
      simp [lowering,h.pendingValue,pendingWord,Weapon.supported]
  · subst p
    simp [lowering,h.pendingValue,pendingWord,h.healthValue,zero,Weapon.supported]

theorem supported_not_held (s : X86Memory.State) (w : Fin 3) (p : Nat) (hp : Int32) (a : Bool)
    (h : Inputs s w p hp a) : weapon s≠(4#32) ∧ weapon s≠(6#32) := by
  rw [h.weaponValue]
  have cases : w.val=0 ∨ w.val=1 ∨ w.val=2 := by omega
  rcases cases with e | e | e <;> rw [e] <;> decide

/-- Branch correspondence to the helper actually used by the live ready action.
This describes the requested operation, not execution of lower/fire callees. -/
theorem live_decision (s : X86Memory.State) (w : Fin 3) (p : Nat) (hp : Int32) (a : Bool)
    (h : Inputs s w p hp a) :
    (result s).pc = match Weapon.readyDecision p hp a with
      | .lower => 0x2d040 | .fire => 0x2d410 | .idle => 0x2d392 := by
  have low := live_lowering s w p hp a h
  obtain ⟨w4,w6⟩ := supported_not_held s w p hp a h
  by_cases l : lowering s
  · have yes := low.mp l
    simp [result,l,lowered,Weapon.readyDecision,yes]
  · have no : (Weapon.supported p || hp==0)≠true := fun e => l (low.mpr e)
    by_cases atk : attack s=(0#8)
    · have off : a=false := by
        have absent : a≠true := fun eq => (h.attackValue.mpr eq) atk
        cases a <;> simp_all
      simp [result,l,trigger,atk,Weapon.readyDecision,no,off]
    · have on : a=true := h.attackValue.mp atk
      by_cases lat : latch s=(0#32) <;>
        simp [result,l,trigger,atk,lat,w4,w6,firing,Weapon.readyDecision,no,on]

/-- On the idle path these gates are read-only: the bobbing proof can reuse
its initial-memory and separation premises without transporting them. -/
theorem idle_result (s : X86Memory.State) (h : ¬lowering s) (a : attack s=(0#8)) :
    result s=⟨s,some (logical8 (attack s)),0x2d392⟩ := by
  simp [result,h,trigger,a]

/-- The lowering CALL carries the live down-state ID, slot zero and player
pointer, and pushes the actual continuation. Table initialization is explicit. -/
theorem lower_live (s : X86Memory.State) (w : Fin 3) (p : Nat) (hp : Int32) (a : Bool)
    (h : Inputs s w p hp a) (low : lowering s)
    (table : load32 s.memory (BitVec.ofNat 32 (0x12d98+24*w.val))=BitVec.ofNat 32 (Weapon.down w.val)) :
    (result s).core.regs 0=s.regs 1 ∧ (result s).core.regs 2=0 ∧
    (result s).core.regs 3=BitVec.ofNat 32 (Weapon.down w.val) ∧
    (result s).core.regs 4=s.regs 4-4 ∧
    load32 (result s).core.memory (s.regs 4-4)=0x2d35b := by
  have down : downState s=BitVec.ofNat 32 (Weapon.down w.val) := by
    unfold downState
    rw [h.weaponValue]
    have cases : w.val=0 ∨ w.val=1 ∨ w.val=2 := by omega
    rcases cases with e | e | e <;> simp only [e] at table ⊢ <;> exact table
  simp [result,low,lowered,X86Routine.pushWord,put,write,load_store,down]

/-- CALL's stack write may alias player memory in the raw machine model.
The live latch claim therefore states the necessary byte separation. -/
theorem fire_live (s : X86Memory.State) (w : Fin 3) (p : Nat) (hp : Int32) (a : Bool)
    (h : Inputs s w p hp a) (low : ¬lowering s) (pressed : attack s≠(0#8))
    (apart : Apart (s.regs 1+(188#32)) (s.regs 4-(4#32))) :
    (result s).core.regs 0=s.regs 1 ∧ (result s).core.regs 4=s.regs 4-4 ∧
    load32 (result s).core.memory (s.regs 4-4)=0x2d38d ∧
    load32 (result s).core.memory (s.regs 1+188)=1 := by
  obtain ⟨w4,w6⟩ := supported_not_held s w p hp a h
  by_cases lat : latch s=(0#32) <;>
    simp [result,low,trigger,pressed,lat,w4,w6,firing,X86Routine.pushWord,put,write,
      load_store,load_store_apart _ _ _ _ apart]

end Doom.Proofs.WeaponReadyGate
