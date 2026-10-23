import Doom.Proofs.OriginalWeaponRaise
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.WeaponReady
open Verification X86 X86Memory X86Control BlockSummary
def code : List UInt8 := [0xc7,0x81,0xbc,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x8b,0x35,0x80,0xcf,0x2,0x0,0xc1,0xe6,0x7,0xa1,0x84,0x35,0x1,0x0,0x81,0xe6,0xff,0x1f,0x0,0x0,0x8b,0x1c,0xb0,0x8b,0x41,0x1c,0xf7,0xeb,0xf,0xac,0xd0,0x10,0x5,0x0,0x0,0x1,0x0,0x81,0xe6,0xff,0xf,0x0,0x0,0x89,0x47,0x8,0x8b,0x1c,0xb5,0x84,0x5a,0x0,0x0,0x8b,0x41,0x1c,0xf7,0xeb,0xf,0xac,0xd0,0x10,0x5,0x0,0x0,0x20,0x0,0x89,0x47,0xc,0x5f,0x5e,0x59,0x5b,0xc3]
def bytesProgram (bs : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2d392 ≤ pc ∧ pc < 0x2d3e7 then X86Routine.decodeAt bs (pc-0x2d392) else none
def program := bytesProgram code
def listed : X86Routine.Program
  | 0x2d392 => some (.storeImmediate ⟨some 1,none,0,188⟩ 0,10)
  | 0x2d39c => some (.control (.block (.load 6 ⟨none,none,0,0x2cf80⟩)),6)
  | 0x2d3a2 => some (.control (.block (.legacy (.shl 6 7))),3)
  | 0x2d3a5 => some (.control (.block (.load 0 ⟨none,none,0,0x13584⟩)),5)
  | 0x2d3aa => some (.andRegister 6 8191,6)
  | 0x2d3b0 => some (.control (.block (.load 3 ⟨some 0,some 6,2,0⟩)),3)
  | 0x2d3b3 => some (.control (.block (.legacy (.load 0 1 28))),3)
  | 0x2d3b6 => some (.control (.block (.arithmetic (.imul 3))),2)
  | 0x2d3b8 => some (.control (.block (.arithmetic (.shrd 0 2 16))),4)
  | 0x2d3bc => some (.addImmediate 0 65536,5)
  | 0x2d3c1 => some (.andRegister 6 4095,6)
  | 0x2d3c7 => some (.control (.block (.store ⟨some 7,none,0,8⟩ 0)),3)
  | 0x2d3ca => some (.control (.block (.load 3 ⟨none,some 6,2,0x5a84⟩)),7)
  | 0x2d3d1 => some (.control (.block (.legacy (.load 0 1 28))),3)
  | 0x2d3d4 => some (.control (.block (.arithmetic (.imul 3))),2)
  | 0x2d3d6 => some (.control (.block (.arithmetic (.shrd 0 2 16))),4)
  | 0x2d3da => some (.addImmediate 0 2097152,5)
  | 0x2d3df => some (.control (.block (.store ⟨some 7,none,0,12⟩ 0)),3)
  | 0x2d3e2 => some (.pop 7,1)
  | 0x2d3e3 => some (.pop 6,1)
  | 0x2d3e4 => some (.pop 1,1)
  | 0x2d3e5 => some (.pop 3,1)
  | 0x2d3e6 => some (.ret,1)
  | _ => none
theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide
@[local simp] theorem step_2d392 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d3e2] (n+1) ⟨s,f,0x2d392⟩ =
      (X86Routine.execute (.storeImmediate ⟨some 1,none,0,188⟩ 0) ⟨s,f,0x2d39c⟩).bind (X86Routine.run listed [0x2d3e2] n) := by rfl
@[local simp] theorem step_2d39c (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d3e2] (n+1) ⟨s,f,0x2d39c⟩ =
      (X86Routine.execute (.control (.block (.load 6 ⟨none,none,0,0x2cf80⟩))) ⟨s,f,0x2d3a2⟩).bind (X86Routine.run listed [0x2d3e2] n) := by rfl
@[local simp] theorem step_2d3a2 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d3e2] (n+1) ⟨s,f,0x2d3a2⟩ =
      (X86Routine.execute (.control (.block (.legacy (.shl 6 7)))) ⟨s,f,0x2d3a5⟩).bind (X86Routine.run listed [0x2d3e2] n) := by rfl
@[local simp] theorem step_2d3a5 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d3e2] (n+1) ⟨s,f,0x2d3a5⟩ =
      (X86Routine.execute (.control (.block (.load 0 ⟨none,none,0,0x13584⟩))) ⟨s,f,0x2d3aa⟩).bind (X86Routine.run listed [0x2d3e2] n) := by rfl
@[local simp] theorem step_2d3aa (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d3e2] (n+1) ⟨s,f,0x2d3aa⟩ =
      (X86Routine.execute (.andRegister 6 8191) ⟨s,f,0x2d3b0⟩).bind (X86Routine.run listed [0x2d3e2] n) := by rfl
@[local simp] theorem step_2d3b0 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d3e2] (n+1) ⟨s,f,0x2d3b0⟩ =
      (X86Routine.execute (.control (.block (.load 3 ⟨some 0,some 6,2,0⟩))) ⟨s,f,0x2d3b3⟩).bind (X86Routine.run listed [0x2d3e2] n) := by rfl
@[local simp] theorem step_2d3b3 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d3e2] (n+1) ⟨s,f,0x2d3b3⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 0 1 28)))) ⟨s,f,0x2d3b6⟩).bind (X86Routine.run listed [0x2d3e2] n) := by rfl
@[local simp] theorem step_2d3b6 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d3e2] (n+2) ⟨s,f,0x2d3b6⟩ =
      X86Routine.run listed [0x2d3e2] n ⟨multiply s,none,0x2d3bc⟩ := by
  change X86Routine.run listed [0x2d3e2] n
    ⟨X86Block.execute (.arithmetic (.shrd eax edx 16))
      (X86Block.execute (.arithmetic (.imul ebx)) s),none,0x2d3bc⟩ = _
  rw [multiply_correct]
@[local simp] theorem step_2d3bc (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d3e2] (n+1) ⟨s,f,0x2d3bc⟩ =
      (X86Routine.execute (.addImmediate 0 65536) ⟨s,f,0x2d3c1⟩).bind (X86Routine.run listed [0x2d3e2] n) := by rfl
@[local simp] theorem step_2d3c1 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d3e2] (n+1) ⟨s,f,0x2d3c1⟩ =
      (X86Routine.execute (.andRegister 6 4095) ⟨s,f,0x2d3c7⟩).bind (X86Routine.run listed [0x2d3e2] n) := by rfl
@[local simp] theorem step_2d3c7 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d3e2] (n+1) ⟨s,f,0x2d3c7⟩ =
      (X86Routine.execute (.control (.block (.store ⟨some 7,none,0,8⟩ 0))) ⟨s,f,0x2d3ca⟩).bind (X86Routine.run listed [0x2d3e2] n) := by rfl
@[local simp] theorem step_2d3ca (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d3e2] (n+1) ⟨s,f,0x2d3ca⟩ =
      (X86Routine.execute (.control (.block (.load 3 ⟨none,some 6,2,0x5a84⟩))) ⟨s,f,0x2d3d1⟩).bind (X86Routine.run listed [0x2d3e2] n) := by rfl
@[local simp] theorem step_2d3d1 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d3e2] (n+1) ⟨s,f,0x2d3d1⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 0 1 28)))) ⟨s,f,0x2d3d4⟩).bind (X86Routine.run listed [0x2d3e2] n) := by rfl
@[local simp] theorem step_2d3d4 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d3e2] (n+2) ⟨s,f,0x2d3d4⟩ =
      X86Routine.run listed [0x2d3e2] n ⟨multiply s,none,0x2d3da⟩ := by
  change X86Routine.run listed [0x2d3e2] n
    ⟨X86Block.execute (.arithmetic (.shrd eax edx 16))
      (X86Block.execute (.arithmetic (.imul ebx)) s),none,0x2d3da⟩ = _
  rw [multiply_correct]
@[local simp] theorem step_2d3da (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d3e2] (n+1) ⟨s,f,0x2d3da⟩ =
      (X86Routine.execute (.addImmediate 0 2097152) ⟨s,f,0x2d3df⟩).bind (X86Routine.run listed [0x2d3e2] n) := by rfl
@[local simp] theorem step_2d3df (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d3e2] (n+1) ⟨s,f,0x2d3df⟩ =
      (X86Routine.execute (.control (.block (.store ⟨some 7,none,0,12⟩ 0))) ⟨s,f,0x2d3e2⟩).bind (X86Routine.run listed [0x2d3e2] n) := by rfl
@[local simp] theorem stop (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d3e2] n ⟨s,f,0x2d3e2⟩=some ⟨s,f,0x2d3e2⟩ := by cases n <;> rfl

def cleared (s : X86Memory.State) := store32 s.memory (s.regs 1+188) 0
def index (s : X86Memory.State) := (load32 (cleared s) 0x2cf80 <<< 7) &&& (8191#32)
def half (s : X86Memory.State) := index s &&& (4095#32)
def cosine (s : X86Memory.State) := load32 (cleared s) (load32 (cleared s) 0x13584+(index s <<< 2))
def x (s : X86Memory.State) := mulWord (load32 (cleared s) (s.regs 1+28)) (cosine s)+(65536#32)
def horizontal (s : X86Memory.State) := store32 (cleared s) (s.regs 7+8) (x s)
def sine (s : X86Memory.State) := load32 (horizontal s) ((half s <<< 2)+0x5a84)
def bob (s : X86Memory.State) := load32 (horizontal s) (s.regs 1+28)
def y (s : X86Memory.State) := mulWord (bob s) (sine s)+(2097152#32)
def bobbed (s : X86Memory.State) : X86Memory.State :=
  ⟨write (write (write (write s.regs 6 (half s)) 3 (sine s)) 0 (y s)) 2
    ((BitVec.ofInt 64 ((bob s).toInt * (sine s).toInt)).extractLsb' 32 32),
    store32 (horizontal s) (s.regs 7+12) (y s)⟩

theorem bob_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x2d3e2] 18 ⟨s,f,0x2d392⟩=some ⟨bobbed s,none,0x2d3e2⟩ := by
  have run : X86Routine.run listed [0x2d3e2] 18 ⟨s,f,0x2d392⟩=some ⟨bobbed s,none,0x2d3e2⟩ := by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,
      blockPreservesFlags,put,write,multiply,eax,edx,ebx,bobbed,cleared,index,half,cosine,x,horizontal,sine,bob,y,
      BitVec.add_assoc]
    funext r
    by_cases h0 : r=0 <;> by_cases h2 : r=2 <;> by_cases h3 : r=3 <;> by_cases h6 : r=6 <;> simp_all [write]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

def returned (s : X86Memory.State) (f : Option Flags) : X86Control.State :=
  let t := PspriteLoop.popped (PspriteLoop.popped (PspriteLoop.popped (PspriteLoop.popped s 7) 6) 1) 3
  ⟨put t 4 (t.regs 4+4),f,(load32 t.memory (t.regs 4)).toNat⟩

theorem return_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 5 ⟨s,f,0x2d3e2⟩ (returned s f) := by
  have p : X86Routine.Prefix listed [] 5 ⟨s,f,0x2d3e2⟩ (returned s f) := by
    apply X86Routine.Prefix.step (middle := ⟨PspriteLoop.popped s 7,f,0x2d3e3⟩) (by simp) (by rfl) rfl
    apply X86Routine.Prefix.step (middle := ⟨PspriteLoop.popped (PspriteLoop.popped s 7) 6,f,0x2d3e4⟩) (by simp) (by rfl) rfl
    apply X86Routine.Prefix.step (middle := ⟨PspriteLoop.popped (PspriteLoop.popped (PspriteLoop.popped s 7) 6) 1,f,0x2d3e5⟩) (by simp) (by rfl) rfl
    apply X86Routine.Prefix.step (middle := ⟨PspriteLoop.popped (PspriteLoop.popped (PspriteLoop.popped (PspriteLoop.popped s 7) 6) 1) 3,f,0x2d3e6⟩) (by simp) (by rfl) rfl
    apply X86Routine.Prefix.step (middle := returned s f) (by simp) (by rfl) rfl
    exact X86Routine.Prefix.nil _
  exact p.transfer program [] decoded (by simp)

def result (s : X86Memory.State) := returned (bobbed s) none

private theorem prefix_trans {p stops n m s t u}
    (a : X86Routine.Prefix p stops n s t) (b : X86Routine.Prefix p stops m t u) :
    X86Routine.Prefix p stops (n+m) s u := by
  induction a with
  | nil => simpa using b
  | @step n s middle last op len active decoded executed rest ih =>
    simpa only [Nat.succ_add] using X86Routine.Prefix.step active decoded executed (ih b)


theorem execution (s : X86Memory.State) (f : Option Flags) :
    ∃ n, n ≤ 23 ∧ X86Routine.Prefix program [] n ⟨s,f,0x2d392⟩ (result s) := by
  obtain ⟨n,hn,p,_⟩ := X86Routine.run_path (bob_execution s f)
  have p := p.transfer program [] (by intros; rfl) (by simp)
  exact ⟨n+5,by omega, prefix_trans p (return_execution _ _)⟩
def aim (time : Int32) : Angle := ⟨((time*128).toUInt32 &&& 8191) <<< 19⟩
def halfAim (time : Int32) : Angle := ⟨((time*128).toUInt32 &&& 4095) <<< 19⟩
def initialIndex (s : X86Memory.State) := (load32 s.memory 0x2cf80 <<< 7) &&& (8191#32)
def location (s : X86Memory.State) (i : Fin 9) : Word := match i.val with
  | 0 => s.regs 1+188
  | 1 => s.regs 7+8
  | 2 => s.regs 7+12
  | 3 => 0x2cf80
  | 4 => 0x13584
  | 5 => load32 s.memory 0x13584+(initialIndex s <<< 2)
  | 6 => ((initialIndex s &&& (4095#32)) <<< 2)+0x5a84
  | 7 => s.regs 1+28
  | _ => s.regs 4+16
structure Inputs (s : X86Memory.State) (amplitude : Fixed) (time : Int32) : Prop where
  clock : load32 s.memory (location s 3)=time.toBitVec
  amplitude : load32 s.memory (location s 7)=amplitude.raw.toBitVec
  cosine : load32 s.memory (location s 5)=(aim time).fineCosine.raw.toBitVec
  sine : load32 s.memory (location s 6)=(halfAim time).fineSine.raw.toBitVec
  ret : load32 s.memory (location s 8)=(0x2d095#32)
  separate : ∀ i j : Fin 9, i≠j → Apart (location s i) (location s j)

theorem cleared_read (s : X86Memory.State) (amplitude : Fixed) (time : Int32) (h : Inputs s amplitude time)
    (i : Fin 9) (ne : i≠0) : load32 (cleared s) (location s i)=load32 s.memory (location s i) :=
  load_store_apart _ _ _ _ (h.separate i 0 ne)

theorem index_initial (s : X86Memory.State) (amplitude : Fixed) (time : Int32) (h : Inputs s amplitude time) :
    index s=initialIndex s := by
  have keep := cleared_read s amplitude time h 3 (by decide)
  change load32 (cleared s) 0x2cf80=load32 s.memory 0x2cf80 at keep
  simp only [index,initialIndex,keep]

theorem cosine_value (s : X86Memory.State) (amplitude : Fixed) (time : Int32) (h : Inputs s amplitude time) :
    cosine s=(aim time).fineCosine.raw.toBitVec := by
  have keep := cleared_read s amplitude time h 4 (by decide)
  change load32 (cleared s) 0x13584=load32 s.memory 0x13584 at keep
  unfold cosine
  rw [keep,index_initial s amplitude time h]
  exact (cleared_read s amplitude time h 5 (by decide)).trans h.cosine

theorem horizontal_read (s : X86Memory.State) (amplitude : Fixed) (time : Int32) (h : Inputs s amplitude time)
    (i : Fin 9) (ne0 : i≠0) (ne1 : i≠1) : load32 (horizontal s) (location s i)=load32 s.memory (location s i) := by
  change load32 (store32 (cleared s) (location s 1) (x s)) (location s i)=_
  rw [load_store_apart _ _ _ _ (h.separate i 1 ne1)]
  exact cleared_read s amplitude time h i ne0

theorem coordinates (s : X86Memory.State) (v : Weapon.State) (amplitude : Fixed) (time : Int32)
    (h : Inputs s amplitude time) :
    x s=(Weapon.readyIdle v amplitude time).weapon.x.raw.toBitVec ∧
    y s=(Weapon.readyIdle v amplitude time).weapon.y.raw.toBitVec := by
  have bx := (cleared_read s amplitude time h 7 (by decide)).trans h.amplitude
  have by' := (horizontal_read s amplitude time h 7 (by decide) (by decide)).trans h.amplitude
  have sy : sine s=(halfAim time).fineSine.raw.toBitVec := by
    unfold sine half
    rw [index_initial s amplitude time h]
    exact (horizontal_read s amplitude time h 6 (by decide) (by decide)).trans h.sine
  constructor
  · unfold x
    change load32 (cleared s) (s.regs 1+28)=amplitude.raw.toBitVec at bx
    rw [bx,cosine_value s amplitude time h,mulWord_fixed]
    simp only [Weapon.readyIdle,aim,Fixed.add,Int32.toBitVec_add,Fixed.ofInt]
    exact BitVec.add_comm _ _
  · unfold y bob
    change load32 (horizontal s) (s.regs 1+28)=amplitude.raw.toBitVec at by'
    rw [by',sy,mulWord_fixed]
    simp only [Weapon.readyIdle,halfAim,Fixed.add,Int32.toBitVec_add,Fixed.ofInt]
    exact BitVec.add_comm _ _

def writes (s : X86Memory.State) : List Word := [location s 0,location s 1,location s 2]

theorem frame (s : X86Memory.State) : PlayerHeight.Frame s.memory (result s).core.memory (writes s) := by
  intro a safe
  have k0 := safe (location s 0) (by simp [writes])
  have k1 := safe (location s 1) (by simp [writes])
  have k2 := safe (location s 2) (by simp [writes])
  change load32 (store32 (store32 (store32 s.memory (location s 0) 0) (location s 1) (x s)) (location s 2) (y s)) a=_
  rw [load_store_apart _ _ _ _ k2,load_store_apart _ _ _ _ k1,load_store_apart _ _ _ _ k0]

theorem live_result (s : X86Memory.State) (v : Weapon.State) (amplitude : Fixed) (time : Int32)
    (h : Inputs s amplitude time) :
    load32 (result s).core.memory (location s 0)=0 ∧
    load32 (result s).core.memory (location s 1)=(Weapon.readyIdle v amplitude time).weapon.x.raw.toBitVec ∧
    load32 (result s).core.memory (location s 2)=(Weapon.readyIdle v amplitude time).weapon.y.raw.toBitVec ∧
    (result s).pc=0x2d095 ∧ (result s).core.regs 4=s.regs 4+20 := by
  have mem : (result s).core.memory=store32 (store32 (store32 s.memory (location s 0) 0) (location s 1) (x s)) (location s 2) (y s) := rfl
  have latch : load32 (result s).core.memory (location s 0)=0 := by
    rw [mem,load_store_apart _ _ _ _ (h.separate 0 2 (by decide)),load_store_apart _ _ _ _ (h.separate 0 1 (by decide)),load_store]
  have hx : load32 (result s).core.memory (location s 1)=x s := by
    rw [mem,load_store_apart _ _ _ _ (h.separate 1 2 (by decide)),load_store]
  have hy : load32 (result s).core.memory (location s 2)=y s := by rw [mem,load_store]
  have ret : load32 (result s).core.memory (location s 8)=(0x2d095#32) := by
    rw [mem,load_store_apart _ _ _ _ (h.separate 8 2 (by decide)),load_store_apart _ _ _ _ (h.separate 8 1 (by decide)),load_store_apart _ _ _ _ (h.separate 8 0 (by decide)),h.ret]
  refine ⟨latch,hx.trans (coordinates s v amplitude time h).1,hy.trans (coordinates s v amplitude time h).2,?_,?_⟩
  · simpa [result,returned,PspriteLoop.popped,bobbed,put,write,BitVec.add_assoc,location] using congrArg BitVec.toNat ret
  · simp [result,returned,PspriteLoop.popped,bobbed,put,write,BitVec.add_assoc]
end Doom.Proofs.WeaponReady

