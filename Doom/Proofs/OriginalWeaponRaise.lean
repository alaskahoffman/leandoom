import Doom.Proofs.E1M1WeaponFlash
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.WeaponRaise
open Verification X86 X86Memory X86Control BlockSummary
def code : List UInt8 := [0x53,0x51,0x89,0xc3,0x8b,0x4a,0xc,0x81,0xe9,0x0,0x0,0x6,0x0,0x89,0x4a,0xc,0x81,0xf9,0x0,0x0,0x20,0x0,0x7f,0x25,0xc7,0x42,0xc,0x0,0x0,0x20,0x0,0x8b,0x50,0x70,0x8d,0x4,0x95,0x0,0x0,0x0,0x0,0x29,0xd0,0x8b,0xc,0xc5,0x9c,0x2d,0x1,0x0,0x31,0xd2,0x89,0xd8,0x89,0xcb,0xe8,0x33,0xfb,0xff,0xff,0x59,0x5b,0xc3]

def bytesProgram (bs : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2d4d0 ≤ pc ∧ pc < 0x2d510 then X86Routine.decodeAt bs (pc-0x2d4d0) else none
def program := bytesProgram code
def listed : X86Routine.Program
  | 0x2d4d0 => some (.push 3,1)
  | 0x2d4d1 => some (.push 1,1)
  | 0x2d4d2 => some (.control (.block (.legacy (.mov 3 0))),2)
  | 0x2d4d4 => some (.control (.block (.legacy (.load 1 2 12))),3)
  | 0x2d4d7 => some (.addImmediate 1 (-0x60000),6)
  | 0x2d4dd => some (.control (.block (.store ⟨some 2,none,0,12⟩ 1)),3)
  | 0x2d4e0 => some (.compareRegister 1 0x200000,6)
  | 0x2d4e6 => some (.jumpSigned 2 37,2)
  | 0x2d4e8 => some (.storeImmediate ⟨some 2,none,0,12⟩ 0x200000,7)
  | 0x2d4ef => some (.control (.block (.legacy (.load 2 0 112))),3)
  | 0x2d4f2 => some (.control (.block (.lea 0 ⟨none,some 2,2,0⟩)),7)
  | 0x2d4f9 => some (.control (.block (.arithmetic (.sub 0 2))),2)
  | 0x2d4fb => some (.control (.block (.load 1 ⟨none,some 0,3,0x12d9c⟩)),7)
  | 0x2d502 => some (.xorRegister 2 2,2)
  | 0x2d504 => some (.control (.block (.legacy (.mov 0 3))),2)
  | 0x2d506 => some (.control (.block (.legacy (.mov 3 1))),2)
  | 0x2d508 => some (.call (-1229),5)
  | 0x2d50d => some (.pop 1,1)
  | 0x2d50e => some (.pop 3,1)
  | 0x2d50f => some (.ret,1)
  | _ => none

theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def yAddress (s : X86Memory.State) := s.regs 2+(12#32)
def saved (s : X86Memory.State) := X86Routine.pushWord (X86Routine.pushWord s (s.regs 3)) (s.regs 1)
def advanced (s : X86Memory.State) : Word := load32 (saved s).memory (yAddress s)-(0x60000#32)
def raised (s : X86Memory.State) : X86Memory.State :=
  {put (put (saved s) 3 (s.regs 0)) 1 (advanced s) with memory := store32 (saved s).memory (yAddress s) (advanced s)}
def branch (s : X86Memory.State) : X86Control.State :=
  ⟨raised s,some (compare32 (advanced s) 0x200000),if (advanced s).toInt > 0x200000 then 0x2d50d else 0x2d4e8⟩

theorem branch_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x2d50d,0x2d4e8] 8 ⟨s,f,0x2d4d0⟩=some (branch s) := by
  have p : X86Routine.Prefix listed [0x2d50d,0x2d4e8] 6 ⟨s,f,0x2d4d0⟩ ⟨raised s,none,0x2d4e0⟩ := by
    apply X86Routine.Prefix.step (middle := ⟨X86Routine.pushWord s (s.regs 3),f,0x2d4d1⟩) (by simp) (by rfl) rfl
    apply X86Routine.Prefix.step (middle := ⟨saved s,f,0x2d4d2⟩) (by simp) (by rfl) (by rfl)
    apply X86Routine.Prefix.step (middle := ⟨put (saved s) 3 (s.regs 0),f,0x2d4d4⟩) (by simp) (by rfl) (by rfl)
    apply X86Routine.Prefix.step (middle := ⟨put (put (saved s) 3 (s.regs 0)) 1 (load32 (saved s).memory (yAddress s)),f,0x2d4d7⟩) (by simp) (by rfl) (by rfl)
    apply X86Routine.Prefix.step (middle := ⟨put (put (saved s) 3 (s.regs 0)) 1 (advanced s),none,0x2d4dd⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,put,write,advanced,BitVec.sub_eq_add_neg]
      funext r
      by_cases eq : r=1 <;> simp [write,eq])
    apply X86Routine.Prefix.step (middle := ⟨raised s,none,0x2d4e0⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,raised,put,write,saved,X86Routine.pushWord,yAddress])
    exact X86Routine.Prefix.nil _
  have run : X86Routine.run listed [0x2d50d,0x2d4e8] 8 ⟨s,f,0x2d4d0⟩=some (branch s) := by
    apply p.finish (fuel := 2) ?_ 8 (by decide)
    by_cases high : (advanced s).toInt > 0x200000
    · have low : ¬ (advanced s).toInt ≤ 0x200000 := by omega
      simp [X86Routine.run,listed,X86Routine.execute,branch,raised,put,write,cmp32_signed_le,high,low]
    · have low : (advanced s).toInt ≤ 0x200000 := by omega
      simp [X86Routine.run,listed,X86Routine.execute,branch,raised,put,write,cmp32_signed_le,high,low]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

def returned (s : X86Memory.State) (f : Option Flags) : X86Control.State :=
  let t := PspriteLoop.popped (PspriteLoop.popped s 1) 3
  ⟨put t 4 (t.regs 4+4),f,(load32 t.memory (t.regs 4)).toNat⟩

theorem return_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 3 ⟨s,f,0x2d50d⟩ (returned s f) := by
  have p : X86Routine.Prefix listed [] 3 ⟨s,f,0x2d50d⟩ (returned s f) := by
    apply X86Routine.Prefix.step (middle := ⟨PspriteLoop.popped s 1,f,0x2d50e⟩) (by simp) (by rfl) rfl
    apply X86Routine.Prefix.step (middle := ⟨PspriteLoop.popped (PspriteLoop.popped s 1) 3,f,0x2d50f⟩) (by simp) (by rfl) rfl
    apply X86Routine.Prefix.step (middle := returned s f) (by simp) (by rfl) rfl
    exact X86Routine.Prefix.nil _
  exact p.transfer program [] decoded (by simp)


def clamped (s : X86Memory.State) : X86Memory.State :=
  {s with memory := store32 s.memory (yAddress s) (0x200000#32)}
def weaponIndex (s : X86Memory.State) := load32 (clamped s).memory (s.regs 0+(112#32))
def readyState (s : X86Memory.State) :=
  load32 (clamped s).memory ((((weaponIndex s <<< 2)-weaponIndex s) <<< 3)+(0x12d9c#32))
def dispatched (s : X86Memory.State) : X86Control.State :=
  ⟨X86Routine.pushWord (put (put (put (put (clamped s) 2 0) 1 (readyState s)) 0 (s.regs 3)) 3 (readyState s))
    0x2d50d,some (logical32 0),0x2d040⟩

theorem dispatch_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x2d040] 9 ⟨s,f,0x2d4e8⟩=some (dispatched s) := by
  have run : X86Routine.run listed [0x2d040] 9 ⟨s,f,0x2d4e8⟩=some (dispatched s) := by
    simp (config := { maxSteps := 200000 }) [X86Routine.run,listed,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      X86.execute,X86Block.Address.eval,put,write,clamped,dispatched,readyState,weaponIndex,yAddress,
      X86Routine.pushWord,blockPreservesFlags,logical32,BitVec.sub_eq_add_neg]
    funext r
    by_cases h0 : r=0 <;> by_cases h1 : r=1 <;> by_cases h2 : r=2 <;> by_cases h3 : r=3 <;> by_cases h4 : r=4 <;> simp_all [write]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

def result (s : X86Memory.State) : X86Control.State :=
  if (advanced s).toInt > 0x200000 then returned (raised s) (branch s).flags else dispatched (raised s)

private theorem prefix_trans {p stops n m s t u}
    (a : X86Routine.Prefix p stops n s t) (b : X86Routine.Prefix p stops m t u) :
    X86Routine.Prefix p stops (n+m) s u := by
  induction a with
  | nil => simpa using b
  | @step n s middle last op len active decoded executed rest ih =>
    simpa only [Nat.succ_add] using X86Routine.Prefix.step active decoded executed (ih b)

/-- Complete A_Raise through its in-progress RET or actual ready-state CALL.
The latter endpoint is the setter entry, not a stubbed ready action. -/
theorem execution (s : X86Memory.State) (f : Option Flags) :
    ∃ n, n ≤ 17 ∧ X86Routine.Prefix program [] n ⟨s,f,0x2d4d0⟩ (result s) := by
  obtain ⟨n,hn,a,_⟩ := X86Routine.run_path (branch_execution s f)
  have a := a.transfer program [] (by intros; rfl) (by simp)
  by_cases high : (advanced s).toInt > 0x200000
  · have eq : branch s=⟨raised s,(branch s).flags,0x2d50d⟩ := by simp [branch,high]
    rw [eq] at a
    have b := return_execution (raised s) (branch s).flags
    refine ⟨n+3,by omega,?_⟩
    simpa [result,high] using prefix_trans a b
  · have eq : branch s=⟨raised s,(branch s).flags,0x2d4e8⟩ := by simp [branch,high]
    rw [eq] at a
    obtain ⟨m,hm,b,_⟩ := X86Routine.run_path (dispatch_execution (raised s) (branch s).flags)
    have b := b.transfer program [] (by intros; rfl) (by simp)
    refine ⟨n+m,by omega,?_⟩
    simpa [result,high] using prefix_trans a b


def location (s : X86Memory.State) (w : Fin 3) (i : Fin 7) : Word := match i.val with
  | 0 => yAddress s
  | 1 => s.regs 4+(0xfffffffc#32)
  | 2 => s.regs 4+(0xfffffff8#32)
  | 3 => s.regs 4+(0xfffffff4#32)
  | 4 => s.regs 4
  | 5 => s.regs 0+(112#32)
  | _ => BitVec.ofNat 32 (0x12d9c+24*w.val)
structure Inputs (s : X86Memory.State) (w : Fin 3) (y : Fixed) : Prop where
  height : load32 s.memory (location s w 0)=y.raw.toBitVec
  weapon : load32 s.memory (location s w 5)=BitVec.ofNat 32 w.val
  ready : load32 s.memory (location s w 6)=BitVec.ofNat 32 (Weapon.ready w.val)
  ret : load32 s.memory (s.regs 4)=(0x2d095#32)
  separate : ∀ i j : Fin 7, i≠j → Apart (location s w i) (location s w j)

theorem read_store (s : X86Memory.State) (w : Fin 3) (y : Fixed) (h : Inputs s w y)
    (m : Memory) (i j : Fin 7) (v : Word) :
    load32 (store32 m (location s w i) v) (location s w j)=
      if j=i then v else load32 m (location s w j) := by
  by_cases eq : j=i
  · subst j; simp [load_store]
  · rw [if_neg eq]; exact load_store_apart _ _ _ _ (h.separate j i eq)

theorem read_return (s : X86Memory.State) (w : Fin 3) (y : Fixed) (h : Inputs s w y)
    (m : Memory) (i : Fin 7) (v : Word) :
    load32 (store32 m (location s w i) v) (s.regs 4)=
      if i=4 then v else load32 m (s.regs 4) := by
  change load32 (store32 m (location s w i) v) (location s w 4)=_
  rw [read_store s w y h]
  change (if (4 : Fin 7)=i then v else load32 m (s.regs 4))=_
  simp [eq_comm]
theorem location_0 (s : X86Memory.State) (w : Fin 3) : location s w 0=yAddress s := rfl
theorem location_1 (s : X86Memory.State) (w : Fin 3) : location s w 1=s.regs 4+(0xfffffffc#32) := rfl
theorem location_2 (s : X86Memory.State) (w : Fin 3) : location s w 2=s.regs 4+(0xfffffff8#32) := rfl
theorem location_3 (s : X86Memory.State) (w : Fin 3) : location s w 3=s.regs 4+(0xfffffff4#32) := rfl
theorem location_4 (s : X86Memory.State) (w : Fin 3) : location s w 4=s.regs 4 := rfl
theorem location_5 (s : X86Memory.State) (w : Fin 3) : location s w 5=s.regs 0+(112#32) := rfl
theorem location_6 (s : X86Memory.State) (w : Fin 3) : location s w 6=BitVec.ofNat 32 (0x12d9c+24*w.val) := rfl
@[local simp] theorem location_add_1_2 (s : X86Memory.State) (w : Fin 3) : location s w 1+(4294967292#32)=location s w 2 := by change (s.regs 4+(4294967292#32))+(4294967292#32)=s.regs 4+(4294967288#32); simp only [BitVec.add_assoc]; rfl
@[local simp] theorem location_add_1_3 (s : X86Memory.State) (w : Fin 3) : location s w 1+(4294967288#32)=location s w 3 := by change (s.regs 4+(4294967292#32))+(4294967288#32)=s.regs 4+(4294967284#32); simp only [BitVec.add_assoc]; rfl
@[local simp] theorem location_stack_1 (s : X86Memory.State) (w : Fin 3) : location s w 1+(4#32)=s.regs 4 := by change (s.regs 4+(4294967292#32))+(4#32)=s.regs 4; simp [BitVec.add_assoc]
@[local simp] theorem location_add_2_1 (s : X86Memory.State) (w : Fin 3) : location s w 2+(4#32)=location s w 1 := by change (s.regs 4+(4294967288#32))+(4#32)=s.regs 4+(4294967292#32); simp only [BitVec.add_assoc]; rfl
@[local simp] theorem location_add_2_3 (s : X86Memory.State) (w : Fin 3) : location s w 2+(4294967292#32)=location s w 3 := by change (s.regs 4+(4294967288#32))+(4294967292#32)=s.regs 4+(4294967284#32); simp only [BitVec.add_assoc]; rfl
@[local simp] theorem location_stack_2 (s : X86Memory.State) (w : Fin 3) : location s w 2+(8#32)=s.regs 4 := by change (s.regs 4+(4294967288#32))+(8#32)=s.regs 4; simp [BitVec.add_assoc]
@[local simp] theorem location_add_3_1 (s : X86Memory.State) (w : Fin 3) : location s w 3+(8#32)=location s w 1 := by change (s.regs 4+(4294967284#32))+(8#32)=s.regs 4+(4294967292#32); simp only [BitVec.add_assoc]; rfl
@[local simp] theorem location_add_3_2 (s : X86Memory.State) (w : Fin 3) : location s w 3+(4#32)=location s w 2 := by change (s.regs 4+(4294967284#32))+(4#32)=s.regs 4+(4294967288#32); simp only [BitVec.add_assoc]; rfl
@[local simp] theorem location_stack_3 (s : X86Memory.State) (w : Fin 3) : location s w 3+(12#32)=s.regs 4 := by change (s.regs 4+(4294967284#32))+(12#32)=s.regs 4; simp [BitVec.add_assoc]

theorem live_step (y : Fixed) :
    (Weapon.raiseStep y).1.raw.toBitVec =
      (if (y.raw.toBitVec-(0x60000#32)).toInt > 0x200000 then y.raw.toBitVec-(0x60000#32) else (0x200000#32)) ∧
    (Weapon.raiseStep y).2=decide ((y.raw.toBitVec-(0x60000#32)).toInt ≤ 0x200000) := by
  have word : y.raw.toBitVec-(0x60000#32)=(y.raw-393216).toBitVec := rfl
  have raw : (y-Fixed.ofInt 6).raw=y.raw-393216 := rfl
  rw [word,Int32.toInt_toBitVec]
  by_cases high : (y.raw-393216).toInt > 2097152 <;>
    simp [Weapon.raiseStep,raw,Int32.lt_iff_toInt_lt,high,-Int32.toInt_sub,←Int.not_lt]
  rfl

/-- Initial field/table separation suffices to recover live height and branch
behavior, the caller's restored registers, or the actual ready setter arguments. -/
theorem live_result (s : X86Memory.State) (w : Fin 3) (y : Fixed) (h : Inputs s w y) :
    load32 (result s).core.memory (yAddress s)=(Weapon.raiseStep y).1.raw.toBitVec ∧
    (if (Weapon.raiseStep y).2 then
      (result s).pc=0x2d040 ∧ (result s).core.regs 0=s.regs 0 ∧ (result s).core.regs 2=(0#32) ∧
      (result s).core.regs 3=BitVec.ofNat 32 (Weapon.ready w.val) ∧
      (result s).core.regs 4=s.regs 4-(12#32) ∧
      load32 (result s).core.memory ((result s).core.regs 4)=(0x2d50d#32)
    else (result s).pc=0x2d095 ∧ (result s).core.regs 1=s.regs 1 ∧
      (result s).core.regs 3=s.regs 3 ∧ (result s).core.regs 4=s.regs 4+(4#32)) := by
  rw [(live_step y).1,(live_step y).2]
  have hy := h.height
  have hw := h.weapon
  have hr := h.ready
  have cases : w=0 ∨ w=1 ∨ w=2 := by omega
  rcases cases with rfl|rfl|rfl
  · have l0 : location s 0 0=s.regs 2+(12#32) := rfl
    have l6 : location s 0 6=(0x12d9c#32) := rfl
    by_cases high : (y.raw.toBitVec-(0x60000#32)).toInt > 0x200000
    all_goals
      first
      | have opposite : ¬ (y.raw.toBitVec-(0x60000#32)).toInt ≤ 0x200000 := by omega
      | have opposite : ¬ 0x200000 < (y.raw.toBitVec-(0x60000#32)).toInt := by omega
      simp [BitVec.sub_eq_add_neg,-BitVec.toInt_add,-BitVec.toInt_sub,-Int.not_lt,-Int.not_le] at high opposite
      simp [result,branch,advanced,raised,saved,returned,dispatched,clamped,readyState,weaponIndex,
        PspriteLoop.popped,X86Routine.pushWord,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,yAddress,
        BitVec.ofNat_eq_ofNat,Weapon.ready,WeaponData.PUNCH,WeaponData.PISTOL,WeaponData.SGUN,
        ←l0,←l6,←location_1 s 0,←location_2 s 0,←location_3 s 0,←location_5 s 0,read_store s 0 y h,read_return s 0 y h,hy,hw,hr,h.ret,high,opposite,
        -BitVec.toInt_add,-BitVec.toInt_sub] <;> omega
  · have l0 : location s 1 0=s.regs 2+(12#32) := rfl
    have l6 : location s 1 6=(0x12db4#32) := rfl
    by_cases high : (y.raw.toBitVec-(0x60000#32)).toInt > 0x200000
    all_goals
      first
      | have opposite : ¬ (y.raw.toBitVec-(0x60000#32)).toInt ≤ 0x200000 := by omega
      | have opposite : ¬ 0x200000 < (y.raw.toBitVec-(0x60000#32)).toInt := by omega
      simp [BitVec.sub_eq_add_neg,-BitVec.toInt_add,-BitVec.toInt_sub,-Int.not_lt,-Int.not_le] at high opposite
      simp [result,branch,advanced,raised,saved,returned,dispatched,clamped,readyState,weaponIndex,
        PspriteLoop.popped,X86Routine.pushWord,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,yAddress,
        BitVec.ofNat_eq_ofNat,Weapon.ready,WeaponData.PUNCH,WeaponData.PISTOL,WeaponData.SGUN,
        ←l0,←l6,←location_1 s 1,←location_2 s 1,←location_3 s 1,←location_5 s 1,read_store s 1 y h,read_return s 1 y h,hy,hw,hr,h.ret,high,opposite,
        -BitVec.toInt_add,-BitVec.toInt_sub] <;> omega
  · have l0 : location s 2 0=s.regs 2+(12#32) := rfl
    have l6 : location s 2 6=(0x12dcc#32) := rfl
    by_cases high : (y.raw.toBitVec-(0x60000#32)).toInt > 0x200000
    all_goals
      first
      | have opposite : ¬ (y.raw.toBitVec-(0x60000#32)).toInt ≤ 0x200000 := by omega
      | have opposite : ¬ 0x200000 < (y.raw.toBitVec-(0x60000#32)).toInt := by omega
      simp [BitVec.sub_eq_add_neg,-BitVec.toInt_add,-BitVec.toInt_sub,-Int.not_lt,-Int.not_le] at high opposite
      simp [result,branch,advanced,raised,saved,returned,dispatched,clamped,readyState,weaponIndex,
        PspriteLoop.popped,X86Routine.pushWord,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,yAddress,
        BitVec.ofNat_eq_ofNat,Weapon.ready,WeaponData.PUNCH,WeaponData.PISTOL,WeaponData.SGUN,
        ←l0,←l6,←location_1 s 2,←location_2 s 2,←location_3 s 2,←location_5 s 2,read_store s 2 y h,read_return s 2 y h,hy,hw,hr,h.ret,high,opposite,
        -BitVec.toInt_add,-BitVec.toInt_sub] <;> omega

def writes (s : X86Memory.State) : List Word :=
  [s.regs 4+(0xfffffffc#32),s.regs 4+(0xfffffff8#32),s.regs 4+(0xfffffff4#32),yAddress s]

/-- Both branches preserve every disjoint word outside their explicit writes. -/
theorem frame (s : X86Memory.State) : PlayerHeight.Frame s.memory (result s).core.memory (writes s) := by
  intro a safe
  have keep1 (m : Memory) (v : Word) : load32 (store32 m (s.regs 4+(0xfffffffc#32)) v) a=load32 m a :=
    load_store_apart _ _ _ _ (safe _ (by simp [writes]))
  have keep2 (m : Memory) (v : Word) : load32 (store32 m (s.regs 4+(0xfffffff8#32)) v) a=load32 m a :=
    load_store_apart _ _ _ _ (safe _ (by simp [writes]))
  have keep3 (m : Memory) (v : Word) : load32 (store32 m (s.regs 4+(0xfffffff4#32)) v) a=load32 m a :=
    load_store_apart _ _ _ _ (safe _ (by simp [writes]))
  have keepY (m : Memory) (v : Word) : load32 (store32 m (yAddress s) v) a=load32 m a :=
    load_store_apart _ _ _ _ (safe _ (by simp [writes]))
  simp only [yAddress] at keepY
  by_cases high : (advanced s).toInt > 0x200000 <;>
    simp [result,high,returned,dispatched,raised,clamped,saved,PspriteLoop.popped,X86Routine.pushWord,
      put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,keep1,keep2,keep3,keepY,yAddress]

end Doom.Proofs.WeaponRaise
