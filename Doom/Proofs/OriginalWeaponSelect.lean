import Doom.Proofs.E1M1FloorCycle
import Doom.Weapon
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.WeaponSelect
open Verification X86 X86Memory X86Control BlockSummary

/-- Check each of the at most 32 bits by kernel reduction and bit-vector
lemmas. No compiled SAT-certificate checker is added to the trust boundary. -/
macro "selection_bits" : tactic => `(tactic| (
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 ∨ i=15 ∨ i=16 ∨ i=17 ∨ i=18 ∨ i=19 ∨ i=20 ∨ i=21 ∨ i=22 ∨ i=23 ∨ i=24 ∨ i=25 ∨ i=26 ∨ i=27 ∨ i=28 ∨ i=29 ∨ i=30 ∨ i=31 := by omega
  rcases cases with case|case|case|case|case|case|case|case|case|case|case|case|case|case|case|case|case|case|case|case|case|case|case|case|case|case|case|case|case|case|case|case
  all_goals subst i
  all_goals simp [-BitVec.getLsbD_eq_getElem,BitVec.getLsbD_shiftLeft,BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_sshiftRight,BitVec.msb_eq_getLsbD_last,BitVec.getLsbD_extractLsb',BitVec.getLsbD_setWidth]
))

def code : List UInt8 := [0xf6,0x43,0x7,0x80,0x74,0x4,0xc6,0x43,0x7,0x0,0x8a,0x63,0x7,0xf6,0xc4,0x4,0xf,0x84,0x7b,0x0,0x0,0x0,0x88,0xe0,0x24,0x38,0x25,0xff,0x0,0x0,0x0,0xc1,0xf8,0x3,0x85,0xc0,0x75,0x27,0x83,0xba,0x94,0x0,0x0,0x0,0x0,0x74,0x1e,0x83,0x7a,0x70,0x7,0x75,0x6,0x83,0x7a,0x30,0x0,0x75,0x7,0xb9,0x1,0x0,0x0,0x0,0xeb,0x2,0x31,0xc9,0x85,0xc9,0x74,0x5,0xb8,0x7,0x0,0x0,0x0,0x83,0x3d,0xbc,0xa3,0x2,0x0,0x0,0x74,0x19,0x83,0xf8,0x2,0x75,0x14,0x83,0xba,0x98,0x0,0x0,0x0,0x0,0x74,0xb,0x83,0x7a,0x70,0x8,0x74,0x5,0xb8,0x8,0x0,0x0,0x0,0x83,0x7c,0x82,0x78,0x0,0x74,0x1b,0x3b,0x42,0x70,0x74,0x16,0x83,0xf8,0x5,0x74,0x5,0x83,0xf8,0x6,0x75,0x9,0x83,0x3d,0xac,0xa3,0x2,0x0,0x0,0x75,0x3,0x89,0x42,0x74]
def bytesProgram (bytes : List UInt8) : X86Routine.Program := fun pc =>
  if 0x333e5 ≤ pc ∧ pc < 0x33476 then X86Routine.decodeAt bytes (pc-0x333e5) else none
def program := bytesProgram code

/-- The shareware E1M1 profile admits fist, pistol and shotgun selections.
Chainsaw ownership is an explicit memory premise, not inferred from the map. -/
structure Inputs (s : X86Memory.State) (buttons : BitVec 8) (w : Fin 3) : Prop where
  encoded : s.memory (s.regs 3+7)=buttons
  ordinary : buttons &&& (128#8) = (0#8)
  selection : buttons &&& 4≠0 → (buttons &&& (56#8)).zeroExtend 32 >>> 3=BitVec.ofNat 32 w.val
  noChainsaw : load32 s.memory (s.regs 2+148)=0
  shareware : load32 s.memory (0x2a3bc#32)=0

def loaded (s : X86Memory.State) (buttons : BitVec 8) := putByte s 4 buttons
def owns (s : X86Memory.State) (w : Fin 3) : Word := load32 s.memory (s.regs 2+BitVec.ofNat 32 w.val*4+120)
def current (s : X86Memory.State) : Word := load32 s.memory (s.regs 2+112)
def selected (s : X86Memory.State) (w : Fin 3) := put s 0 (BitVec.ofNat 32 w.val)
def changes (s : X86Memory.State) (buttons : BitVec 8) (w : Fin 3) : Bool :=
  buttons &&& (4#8) != (0#8) && owns s w != 0 && current s != BitVec.ofNat 32 w.val

def selectionResult (s : X86Memory.State) (w : Fin 3) : X86Control.State :=
  let chosen := selected s w
  if owns s w=0 then ⟨chosen,some (compare32 0 0),0x33476⟩
  else if BitVec.ofNat 32 w.val=current s then
    ⟨chosen,some (compare32 (BitVec.ofNat 32 w.val) (current s)),0x33476⟩
  else ⟨{chosen with memory := store32 s.memory (s.regs 2+116) (BitVec.ofNat 32 w.val)},
    some (compare32 (BitVec.ofNat 32 w.val) 6),0x33476⟩

def result (s : X86Memory.State) (buttons : BitVec 8) (w : Fin 3) : X86Control.State :=
  if buttons &&& (4#8) = (0#8) then ⟨loaded s buttons,some (logical8 0),0x33476⟩
  else selectionResult s w

def listed : X86Routine.Program
  | 0x333e5 => some (.testMemoryByte ⟨some 3,none,0,7⟩ 128,4)
  | 0x333e9 => some (.control (.jumpZero true 4),2)
  | 0x333ef => some (.control (.loadByte 4 ⟨some 3,none,0,7⟩),3)
  | 0x333f2 => some (.testByteImmediate 4 4,3)
  | 0x333f5 => some (.control (.jumpZero true 123),6)
  | 0x333fb => some (.moveByte 0 4,2)
  | 0x333fd => some (.andByteImmediate 0 56,2)
  | 0x333ff => some (.control (.andEax 255),5)
  | 0x33404 => some (.sar 0 3,3)
  | 0x33407 => some (.control (.testWord 0 0),2)
  | 0x33409 => some (.control (.jumpZero false 39),2)
  | 0x3340b => some (.control (.cmpImmediate ⟨some 2,none,0,148⟩ 0),7)
  | 0x33412 => some (.control (.jumpZero true 30),2)
  | 0x33432 => some (.control (.cmpImmediate ⟨none,none,0,0x2a3bc⟩ 0),7)
  | 0x33439 => some (.control (.jumpZero true 25),2)
  | 0x33454 => some (.control (.cmpImmediate ⟨some 2,some 0,2,120⟩ 0),5)
  | 0x33459 => some (.control (.jumpZero true 27),2)
  | 0x3345b => some (.control (.cmpMemory 0 ⟨some 2,none,0,112⟩),3)
  | 0x3345e => some (.control (.jumpZero true 22),2)
  | 0x33460 => some (.compareRegister 0 5,3)
  | 0x33463 => some (.control (.jumpZero true 5),2)
  | 0x33465 => some (.compareRegister 0 6,3)
  | 0x33468 => some (.control (.jumpZero false 9),2)
  | 0x33473 => some (.control (.block (.store ⟨some 2,none,0,116⟩ 0)),3)
  | _ => none

theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

theorem read_loaded (s : X86Memory.State) (b : BitVec 8) : readByte (loaded s b).regs 4=b := by
  change (((s.regs 0 &&& 0xffff00ff) ||| (b.zeroExtend 32 <<< 8)).extractLsb' 8 8)=b
  selection_bits

/-- Exact high-byte to low-byte transfer followed by the two masks. -/
theorem masked (s : X86Memory.State) (b : BitVec 8) :
    ((readByte (putByte (loaded s b) 0 (readByte (loaded s b).regs 4)).regs 0 &&& 56).zeroExtend 32)=
      (b &&& (56#8)).zeroExtend 32 := by
  rw [read_loaded]
  simp [readByte,putByte,byteReg,put,write]
  selection_bits

theorem put_low (s : X86Memory.State) (b : BitVec 8) :
    putByte s 0 b=put s 0 ((s.regs 0 &&& 0xffffff00) ||| b.zeroExtend 32) := rfl
theorem put_high (s : X86Memory.State) (b : BitVec 8) :
    putByte s 4 b=put s 0 ((s.regs 0 &&& 0xffff00ff) ||| (b.zeroExtend 32 <<< 8)) := rfl
theorem read_low (rs : Registers) : readByte rs 0=(rs 0).extractLsb' 0 8 := rfl
theorem read_high (rs : Registers) : readByte rs 4=(rs 0).extractLsb' 8 8 := rfl

theorem input_prefix (s : X86Memory.State) (f : Option Flags) (b : BitVec 8) (w : Fin 3)
    (h : Inputs s b w) :
    X86Routine.run listed [0x333fb,0x33476] 5 ⟨s,f,0x333e5⟩=
      some ⟨loaded s b,some (logical8 (b &&& (4#8))),if b &&& (4#8) = (0#8) then 0x33476 else 0x333fb⟩ := by
  have buttons : s.memory (s.regs 3+(7#32))=b := h.encoded
  have ordinary : b &&& (128#8)=(0#8) := h.ordinary
  have high : readByte (putByte s 4 b).regs 4=b := read_loaded s b
  simp [X86Routine.run,listed,X86Routine.execute,X86Control.execute,X86Block.Address.eval,
    logical8,buttons,ordinary,high,loaded]
  split <;> simp_all

theorem mask_sequence (s : X86Memory.State) (f : Option Flags) (b : BitVec 8) (w : Fin 3)
    (h : Inputs s b w) (active : b &&& 4≠0) :
    X86Routine.run listed [0x33409] 5 ⟨loaded s b,f,0x333fb⟩=
      some ⟨selected s w,some (logical32 (BitVec.ofNat 32 w.val)),0x33409⟩ := by
  have choice := h.selection active
  rw [←choice]
  simp [X86Routine.run,listed,X86Routine.execute,X86Control.execute,X86Block.Address.eval,
    loaded,selected,put_low,put_high,read_low,read_high,put,write,eax,logical32]
  repeat' apply And.intro
  · funext r
    by_cases hr : r=0
    · subst r; simp [write]; rw [←choice]; selection_bits
    · simp [write,hr]
  all_goals first | (congr 1 <;> selection_bits) | (simp [BitVec.msb_eq_getLsbD_last])


theorem compare_zero (a b : Word) : (compare32 a b).zero=decide (a=b) := by
  change (a-b == 0)=decide (a=b)
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq,decide_eq_true_eq]
  simp [BitVec.sub_eq_iff_eq_add]

theorem to_ownership (s : X86Memory.State) (b : BitVec 8) (w : Fin 3) (h : Inputs s b w) :
    X86Routine.run listed [0x33454] 5 ⟨selected s w,some (logical32 (BitVec.ofNat 32 w.val)),0x33409⟩=
      some ⟨selected s w,some (compare32 0 0),0x33454⟩ := by
  have noChainsaw : load32 s.memory (s.regs 2+(148#32))=(0#32) := h.noChainsaw
  have shareware : load32 s.memory (172988#32)=(0#32) := h.shareware
  have cases : w=0 ∨ w=1 ∨ w=2 := by have bound := w.isLt; simp only [Fin.ext_iff]; omega
  rcases cases with rfl|rfl|rfl <;>
    simp [X86Routine.run,listed,X86Routine.execute,X86Control.execute,X86Block.Address.eval,
      selected,put,write,logical32,compare_zero,noChainsaw,shareware]

set_option maxHeartbeats 2400000 in
theorem ownership_tail (s : X86Memory.State) (f : Option Flags) (b : BitVec 8) (w : Fin 3)
    (h : Inputs s b w) :
    X86Routine.run listed [0x33476] 9 ⟨selected s w,f,0x33454⟩=
      some (selectionResult s w) := by
  have noChainsaw : load32 s.memory (s.regs 2+(148#32))=(0#32) := h.noChainsaw
  have shareware : load32 s.memory (172988#32)=(0#32) := h.shareware
  have cases : w=0 ∨ w=1 ∨ w=2 := by have bound := w.isLt; simp only [Fin.ext_iff]; omega
  rcases cases with rfl|rfl|rfl
  · have gate : ((0#32)=load32 s.memory (s.regs 2+(112#32))) ↔ load32 s.memory (s.regs 2+(112#32))=(0#32) := eq_comm
    by_cases owned : owns s 0=0 <;> by_cases ready : current s=(0#32) <;>
      simp [owns,current,BitVec.add_assoc] at owned ready <;>
      simp (maxSteps := 1000000) [X86Routine.run,listed,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
        X86.execute,X86Block.Address.eval,selected,selectionResult,logical32,compare_zero,put,write,
        owns,current,BitVec.add_assoc,noChainsaw,shareware,blockPreservesFlags,owned,ready,gate]
  · have gate : ((1#32)=load32 s.memory (s.regs 2+(112#32))) ↔ load32 s.memory (s.regs 2+(112#32))=(1#32) := eq_comm
    by_cases owned : owns s 1=0 <;> by_cases ready : current s=(1#32) <;>
      simp [owns,current,BitVec.add_assoc] at owned ready <;>
      simp (maxSteps := 1000000) [X86Routine.run,listed,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
        X86.execute,X86Block.Address.eval,selected,selectionResult,logical32,compare_zero,put,write,
        owns,current,BitVec.add_assoc,noChainsaw,shareware,blockPreservesFlags,owned,ready,gate]
  · have gate : ((2#32)=load32 s.memory (s.regs 2+(112#32))) ↔ load32 s.memory (s.regs 2+(112#32))=(2#32) := eq_comm
    by_cases owned : owns s 2=0 <;> by_cases ready : current s=(2#32) <;>
      simp [owns,current,BitVec.add_assoc] at owned ready <;>
      simp (maxSteps := 1000000) [X86Routine.run,listed,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
        X86.execute,X86Block.Address.eval,selected,selectionResult,logical32,compare_zero,put,write,
        owns,current,BitVec.add_assoc,noChainsaw,shareware,blockPreservesFlags,owned,ready,gate]


/-- All selected paths retain the same machine state at every seam. -/
theorem execution (s : X86Memory.State) (f : Option Flags) (b : BitVec 8) (w : Fin 3)
    (h : Inputs s b w) :
    X86Routine.run program [0x33476] 24 ⟨s,f,0x333e5⟩=some (result s b w) := by
  have transfer {exits n a z} (path : X86Routine.Prefix listed exits n a z) :=
    path.transfer listed [0x33476] (by intros; rfl) (by
      intro pc hp; simp only [List.mem_singleton]; intro e; subst pc; exact hp rfl)
  have first := input_prefix s f b w h
  obtain ⟨n,hn,path,_⟩ := X86Routine.run_path first
  have path := transfer path
  have run : X86Routine.run listed [0x33476] 24 ⟨s,f,0x333e5⟩=some (result s b w) := by
    by_cases active : b &&& (4#8)=(0#8)
    · simp only [active,if_pos,BitVec.and_zero] at path
      apply path.finish (fuel := 0) _ 24 (by omega)
      simp [X86Routine.run,result,active]
    · rw [if_neg active] at path
      have mask := mask_sequence s (some (logical8 (b &&& (4#8)))) b w h active
      obtain ⟨m,hm,mp,_⟩ := X86Routine.run_path mask
      have mp := transfer mp
      obtain ⟨k,hk,kp,_⟩ := X86Routine.run_path (to_ownership s b w h)
      have kp := transfer kp
      have tail := ownership_tail s (some (compare32 0 0)) b w h
      have tail := kp.finish tail 14 (by omega)
      have tail := mp.finish tail 19 (by omega)
      simpa only [result,if_neg active] using path.finish tail 24 (by omega)
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

theorem result_pc (s : X86Memory.State) (b : BitVec 8) (w : Fin 3) :
    (result s b w).pc=0x33476 := by
  unfold result selectionResult
  repeat' first | split | rfl

theorem result_memory (s : X86Memory.State) (b : BitVec 8) (w : Fin 3) :
    (result s b w).core.memory=
      if changes s b w then store32 s.memory (s.regs 2+116) (BitVec.ofNat 32 w.val) else s.memory := by
  have gate : (BitVec.ofNat 32 w.val=current s) ↔ (current s=BitVec.ofNat 32 w.val) := eq_comm
  simp [result,selectionResult,changes,loaded,putByte,put,selected,gate]
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all

theorem result_register (s : X86Memory.State) (b : BitVec 8) (w : Fin 3) (r : Reg) (hr : r≠0) :
    (result s b w).core.regs r=s.regs r := by
  unfold result selectionResult
  repeat' first | split | (simp [loaded,put_high,selected,put,write,hr])

theorem result_pending (s : X86Memory.State) (b : BitVec 8) (w : Fin 3) :
    load32 (result s b w).core.memory (s.regs 2+116)=
      if changes s b w then BitVec.ofNat 32 w.val else load32 s.memory (s.regs 2+116) := by
  rw [result_memory]; split <;> simp_all [load_store]

/-- The original selection block and the running Lean helper have the same
pending-weapon result. No health or ammunition premise is needed. -/
theorem live_pending (s : X86Memory.State) (b : BitVec 8) (w : Fin 3) (c : Weapon.Context)
    (owned : (owns s w != 0)=c.player.weapons[w.val])
    (ready : current s=BitVec.ofNat 32 c.player.readyWeapon.val)
    (pending : load32 s.memory (s.regs 2+116)=BitVec.ofNat 32 c.player.pendingWeapon.val) :
    load32 (result s b w).core.memory (s.regs 2+116)=
      BitVec.ofNat 32 (c.select (if b &&& (4#8) = (0#8) then none else some w.val)).player.pendingWeapon.val := by
  have small : w.val<9 := by omega
  have supported : Weapon.supported w.val=true := by simp [Weapon.supported]; omega
  have equal : (BitVec.ofNat 32 c.player.readyWeapon.val=BitVec.ofNat 32 w.val) ↔ c.player.readyWeapon.val=w.val := by
    constructor
    · intro h
      have e := congrArg BitVec.toNat h
      simpa [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show c.player.readyWeapon.val<2^32 by have := c.player.readyWeapon.isLt; omega),
        Nat.mod_eq_of_lt (show w.val<2^32 by omega)] using e
    · intro h; rw [h]
  have different : (BitVec.ofNat 32 c.player.readyWeapon.val != BitVec.ofNat 32 w.val)=
      (c.player.readyWeapon.val != w.val) := by
    apply Bool.eq_iff_iff.mpr
    simp [equal]
  have change : changes s b w=(b &&& (4#8) != (0#8) && c.player.weapons[w.val] && (c.player.readyWeapon.val != w.val)) := by
    unfold changes
    rw [owned,ready,different]
  change load32 s.memory (s.regs 2+(116#32))=BitVec.ofNat 32 c.player.pendingWeapon.val at pending
  rw [result_pending,change]
  by_cases active : b &&& (4#8)=(0#8)
  · simp [active,Weapon.Context.select,pending]
  · simp [active,Weapon.Context.select,small,supported,pending]
    split <;> simp_all

end Doom.Proofs.WeaponSelect
