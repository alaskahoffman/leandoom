import Doom.Proofs.OriginalPlayerArmor
import Doom.Proofs.OriginalHeightFrame
import Doom.Proofs.OriginalSectorSecret
import Doom.Weapon
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.WeaponLower
open Verification X86 X86Memory X86Control BlockSummary
def code : List UInt8 := [0x53,0x66,0x83,0x42,0xe,0x6,0x81,0x7a,0xc,0x0,0x0,0x80,0x0,0x7c,0x2b,0x83,0x78,0x4,0x1,0x75,0x9,0xc7,0x42,0xc,0x0,0x0,0x80,0x0,0x5b,0xc3,0x83,0x78,0x20,0x0,0x75,0xb,0x31,0xd2,0x31,0xdb,0xe8,0x83,0xfb,0xff,0xff,0x5b,0xc3,0x8b,0x50,0x74,0x89,0x50,0x70,0xe8,0x56,0xfc,0xff,0xff,0x5b,0xc3]
def bytesProgram (bytes : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2d490 ≤ pc ∧ pc < 0x2d4cc then X86Routine.decodeAt bytes (pc-0x2d490) else none
def program := bytesProgram code
def listed : X86Routine.Program
  | 0x2d490 => some (.push 3,1)
  | 0x2d491 => some (.addHalfImmediate ⟨some 2,none,0,14⟩ 6,5)
  | 0x2d496 => some (.control (.cmpImmediate ⟨some 2,none,0,12⟩ 0x800000),7)
  | 0x2d49d => some (.jumpSigned 3 43,2)
  | 0x2d49f => some (.control (.cmpImmediate ⟨some 0,none,0,4⟩ 1),4)
  | 0x2d4a3 => some (.control (.jumpZero false 9),2)
  | 0x2d4a5 => some (.storeImmediate ⟨some 2,none,0,12⟩ 0x800000,7)
  | 0x2d4ac => some (.pop 3,1)
  | 0x2d4ad => some (.ret,1)
  | 0x2d4ca => some (.pop 3,1)
  | 0x2d4cb => some (.ret,1)
  | _ => none

theorem decoded (pc : Nat) (h : listed pc ≠ none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

theorem add_high (hi lo : BitVec 16) : ((hi+6) ++ lo) = (hi ++ lo)+(0x60000#32) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_append,BitVec.toNat_add,BitVec.toNat_ofNat]
  rw [← Nat.shiftLeft_add_eq_or_of_lt lo.isLt,← Nat.shiftLeft_add_eq_or_of_lt lo.isLt]
  simp only [Nat.shiftLeft_eq]
  have hiBound := hi.isLt
  have loBound := lo.isLt
  simp only [show (6 : BitVec 16).toNat=6 from rfl,show 2^16=65536 from rfl,show 2^(16+16)=4294967296 from rfl]
  omega

theorem advance_word (m : Memory) (a : Word) :
    load32 (X86Routine.store16 m (a+2) (load16 m (a+2)+6)) a=load32 m a+(0x60000#32) := by
  have neq (i j : BitVec 32) (h : i ≠ j) : a+i ≠ a+j := fun eq => h ((BitVec.add_right_inj a).mp eq)
  have h02 : a ≠ a+(2#32) := by simpa using neq 0 2 (by decide)
  have h03 : a ≠ a+(3#32) := by simpa using neq 0 3 (by decide)
  have h12 := neq (1#32) (2#32) (by decide)
  have h13 := neq (1#32) (3#32) (by decide)
  have h32 := neq (3#32) (2#32) (by decide)
  simp only [load32,load16,X86Routine.store16,BitVec.add_assoc]
  simp only [show (1:Word)=(1#32) from rfl,show (2:Word)=(2#32) from rfl,
    show (3:Word)=(3#32) from rfl,show (2#32)+(1#32)=(3#32) from rfl,
    if_neg h02,if_neg h03,if_neg h12,if_neg h13,if_neg h32,ite_true]
  rw [BitVec.extractLsb'_append_extractLsb']
  exact add_high _ _

/-- The half-word update stays entirely inside this four-byte field. -/
theorem advance_apart (m : Memory) (a b : Word) (h : Apart b a) :
    load32 (X86Routine.store16 m (a+2) (load16 m (a+2)+6)) b=load32 m b := by
  apply SectorSecret.load32_store16
  intro i
  have h3 : b+BitVec.ofNat 32 i.val ≠ a+(3#32) := h i 3
  exact ⟨h i 2,by simpa only [BitVec.add_assoc,show (2:Word)+1=(3#32) from rfl] using h3⟩

def yAddress (s : X86Memory.State) := s.regs 2+(12#32)
def savedMemory (s : X86Memory.State) := store32 s.memory (s.regs 4-(4#32)) (s.regs 3)
def advancedMemory (s : X86Memory.State) :=
  X86Routine.store16 (savedMemory s) (yAddress s+2) (load16 (savedMemory s) (yAddress s+2)+6)
def height (s : X86Memory.State) := load32 (advancedMemory s) (yAddress s)
abbrev below (s : X86Memory.State) := (height s).toInt < 0x800000
def finalMemory (s : X86Memory.State) :=
  if below s then advancedMemory s else store32 (advancedMemory s) (yAddress s) (0x800000#32)
def result (s : X86Memory.State) : X86Control.State :=
  ⟨⟨write (write s.regs 4 (s.regs 4+(4#32))) 3 (load32 (finalMemory s) (s.regs 4-(4#32))),finalMemory s⟩,
    some (if below s then compare32 (height s) 0x800000 else compare32 1 1),0x2d095⟩

def middle (s : X86Memory.State) : X86Control.State :=
  ⟨⟨write s.regs 4 (s.regs 4-(4#32)),advancedMemory s⟩,none,0x2d496⟩

theorem prologue (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix listed [0x2d095] 2 ⟨s,f,0x2d490⟩ (middle s) := by
  apply X86Routine.Prefix.step (middle := ⟨X86Routine.pushWord s (s.regs 3),f,0x2d491⟩)
    (by simp) (by rfl) (by rfl)
  apply X86Routine.Prefix.step (middle := middle s) (by simp) (by rfl) (by
    simp [X86Routine.execute,middle,advancedMemory,savedMemory,yAddress,
      X86Routine.pushWord,X86Block.Address.eval,write,BitVec.add_assoc])
  exact X86Routine.Prefix.nil _

theorem execution (s : X86Memory.State) (f : Option Flags)
    (dead : load32 (advancedMemory s) (s.regs 0+(4#32))=1)
    (ret : load32 (finalMemory s) (s.regs 4)=0x2d095) :
    X86Routine.run listed [0x2d095] 9 ⟨s,f,0x2d490⟩=some (result s) := by
  have registers (v : Word) :
      write (write (write (write s.regs 4 (s.regs 4-(4#32))) 4 (s.regs 4)) 3 v) 4 (s.regs 4+(4#32))=
        write (write s.regs 4 (s.regs 4+(4#32))) 3 v := by
    funext r
    by_cases h3 : r=3 <;> by_cases h4 : r=4 <;> simp_all [write]
  apply (prologue s f).finish (fuel := 7) ?_ 9 (by decide)
  by_cases low : below s
  all_goals
    simp only [finalMemory,low,if_true,if_false,yAddress] at ret
    simp only [below,height,yAddress] at low
    simp [X86Routine.run,listed,X86Routine.execute,X86Control.execute,
      X86Block.Address.eval,put,write,BitVec.sub_add_cancel,middle,
      result,finalMemory,below,height,yAddress,PlayerArmor.cmp_lt,PlayerHeight.cmp_ge_prop,cmp32_zero,dead,ret,low,← Int.not_lt,registers]
abbrev layout (s : X86Memory.State) (n : Fin 4) : Word := match n.val with
  | 0 => s.regs 0+(4#32)
  | 1 => yAddress s
  | 2 => s.regs 4-(4#32)
  | _ => s.regs 4
structure Inputs (s : X86Memory.State) (y : Fixed) : Prop where
  dead : load32 s.memory (s.regs 0+(4#32))=1
  height : load32 s.memory (yAddress s)=y.raw.toBitVec
  ret : load32 s.memory (s.regs 4)=0x2d095
  separate : ∀ a b : Fin 4, a ≠ b → Apart (layout s a) (layout s b)

theorem advance_value (s : X86Memory.State) (y : Fixed) (h : Inputs s y) :
    height s=y.raw.toBitVec+(0x60000#32) := by
  unfold height advancedMemory
  rw [advance_word]
  unfold savedMemory
  have sep : Apart (yAddress s) (s.regs 4-(4#32)) := h.separate 1 2 (by decide)
  rw [load_store_apart _ _ _ _ sep,h.height]

theorem advanced_keep (s : X86Memory.State) (y : Fixed) (h : Inputs s y)
    (n : Fin 4) (notY : n ≠ 1) (notSave : n ≠ 2) :
    load32 (advancedMemory s) (layout s n)=load32 s.memory (layout s n) := by
  unfold advancedMemory
  have sep : Apart (layout s n) (yAddress s) := h.separate n 1 notY
  rw [advance_apart _ _ _ sep]
  exact load_store_apart _ _ _ _ (h.separate n 2 notSave)

theorem final_keep (s : X86Memory.State) (a : Word) (safe : Apart a (yAddress s)) :
    load32 (finalMemory s) a=load32 (savedMemory s) a := by
  unfold finalMemory
  split
  · exact advance_apart _ _ _ safe
  · rw [load_store_apart _ _ _ _ safe]
    exact advance_apart _ _ _ safe

theorem final_height (s : X86Memory.State) (y : Fixed) (h : Inputs s y) :
    load32 (finalMemory s) (yAddress s)=(Weapon.lowerHeight y true).raw.toBitVec := by
  have adv := advance_value s y h
  have word : y.raw.toBitVec+(0x60000#32)=(y.raw+393216).toBitVec := rfl
  have raw : (y + Fixed.ofInt 6).raw=y.raw+393216 := rfl
  unfold finalMemory below
  rw [adv,word,Int32.toInt_toBitVec]
  by_cases low : (y.raw+393216).toInt < 8388608
  · rw [if_pos low]
    change height s=_
    rw [adv,word]
    simp [Weapon.lowerHeight,raw,Int32.lt_iff_toInt_lt,low,Fixed.ofInt,-Int32.toInt_add]
  · rw [if_neg low,load_store]
    simp [Weapon.lowerHeight,raw,Int32.lt_iff_toInt_lt,low,Fixed.ofInt,-Int32.toInt_add]

theorem original_execution (s : X86Memory.State) (f : Option Flags) (y : Fixed) (h : Inputs s y) :
    X86Routine.run program [0x2d095] 9 ⟨s,f,0x2d490⟩=some (result s) := by
  have dead : load32 (advancedMemory s) (s.regs 0+(4#32))=1 :=
    (advanced_keep s y h 0 (by decide) (by decide)).trans h.dead
  have ret : load32 (finalMemory s) (s.regs 4)=0x2d095 := by
    have sep : Apart (s.regs 4) (yAddress s) := h.separate 3 1 (by decide)
    rw [final_keep _ _ sep]
    exact (load_store_apart _ _ _ _ (h.separate 3 2 (by decide))).trans h.ret
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [execution s f dead ret]; simp)]
  exact execution s f dead ret

theorem result_registers (s : X86Memory.State) (y : Fixed) (h : Inputs s y) :
    (result s).core.regs=write s.regs 4 (s.regs 4+(4#32)) := by
  have saved : load32 (finalMemory s) (s.regs 4-(4#32))=s.regs 3 := by
    have sep : Apart (s.regs 4-(4#32)) (yAddress s) := h.separate 2 1 (by decide)
    rw [final_keep _ _ sep]
    exact load_store _ _ _
  simp only [result,saved]
  funext r
  by_cases hr : r=3 <;> simp [write,hr]

theorem result_frame (s : X86Memory.State) :
    PlayerHeight.Frame s.memory (result s).core.memory [s.regs 4-(4#32),yAddress s] := by
  intro a safe
  change load32 (finalMemory s) a=load32 s.memory a
  rw [final_keep _ _ (safe _ (by simp))]
  exact load_store_apart _ _ _ _ (safe _ (by simp))

/-- Exact A_Lower execution for a dead player, through the action's RET. -/
theorem live_correspondence (s : X86Memory.State) (f : Option Flags) (y : Fixed) (h : Inputs s y) :
    ∃ t, X86Routine.run program [0x2d095] 9 ⟨s,f,0x2d490⟩=some t ∧
      load32 t.core.memory (yAddress s)=(Weapon.lowerHeight y true).raw.toBitVec ∧
      t.pc=0x2d095 ∧ t.core.regs=write s.regs 4 (s.regs 4+(4#32)) ∧
      PlayerHeight.Frame s.memory t.core.memory [s.regs 4-(4#32),yAddress s] :=
  ⟨result s,original_execution s f y h,final_height s y h,rfl,result_registers s y h,result_frame s⟩

end Doom.Proofs.WeaponLower
