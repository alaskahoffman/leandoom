import Doom.Proofs.OriginalWeaponLower
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.WeaponLowerProgress
open Verification X86 X86Memory X86Control BlockSummary WeaponLower

/-- The in-progress branch never reads player state or health. Its six real
instructions include the half-word addition, saved register and callback RET. -/
theorem execution (s : X86Memory.State) (f : Option Flags)
    (low : below s) (ret : load32 (advancedMemory s) (s.regs 4)=0x2d095) :
    X86Routine.run WeaponLower.program [0x2d095] 6 ⟨s,f,0x2d490⟩=some (result s) := by
  have run : X86Routine.run listed [0x2d095] 6 ⟨s,f,0x2d490⟩=some (result s) := by
    apply (prologue s f).finish (fuel := 4) ?_ 6 (by decide)
    simp only [below,height,yAddress] at low
    simp [X86Routine.run,listed,X86Routine.execute,X86Control.execute,
      X86Block.Address.eval,put,write,BitVec.sub_add_cancel,middle,
      result,finalMemory,below,height,yAddress,PlayerArmor.cmp_lt,PlayerHeight.cmp_ge_prop,
      ret,low,← Int.not_lt]
    funext r
    by_cases h3 : r=3 <;> by_cases h4 : r=4 <;> simp_all [write]
  rw [X86Routine.run_sound WeaponLower.program listed decoded _ _ _ (by rw [run]; simp)]
  exact run

structure Inputs (s : X86Memory.State) (y : Fixed) : Prop where
  height : load32 s.memory (yAddress s)=y.raw.toBitVec
  ret : load32 s.memory (s.regs 4)=0x2d095
  heightSave : Apart (yAddress s) (s.regs 4-(4#32))
  saveHeight : Apart (s.regs 4-(4#32)) (yAddress s)
  returnHeight : Apart (s.regs 4) (yAddress s)
  returnSave : Apart (s.regs 4) (s.regs 4-(4#32))
  inProgress : (y.raw.toBitVec+(0x60000#32)).toInt<0x800000

theorem advanced_height (s : X86Memory.State) (y : Fixed) (h : Inputs s y) :
    height s=y.raw.toBitVec+(0x60000#32) := by
  unfold height advancedMemory
  rw [advance_word]
  unfold savedMemory
  rw [load_store_apart _ _ _ _ h.heightSave,h.height]

theorem below_height (s : X86Memory.State) (y : Fixed) (h : Inputs s y) : below s := by
  unfold below
  rw [advanced_height s y h]
  exact h.inProgress

theorem return_address (s : X86Memory.State) (y : Fixed) (h : Inputs s y) :
    load32 (advancedMemory s) (s.regs 4)=0x2d095 := by
  unfold advancedMemory
  rw [advance_apart _ _ _ h.returnHeight]
  exact (load_store_apart _ _ _ _ h.returnSave).trans h.ret

theorem live_height (s : X86Memory.State) (y : Fixed) (dead : Bool) (h : Inputs s y) :
    load32 (result s).core.memory (yAddress s)=(Weapon.lowerHeight y dead).raw.toBitVec := by
  change load32 (finalMemory s) (yAddress s)=_
  rw [finalMemory,if_pos (below_height s y h)]
  change height s=_
  rw [advanced_height s y h]
  have raw : (y + Fixed.ofInt 6).raw=y.raw+393216 := rfl
  have low : (y.raw+393216).toInt<8388608 := by
    simpa only [show y.raw.toBitVec+(0x60000#32)=(y.raw+393216).toBitVec from rfl,
      Int32.toInt_toBitVec] using h.inProgress
  simp [Weapon.lowerHeight,raw,Int32.lt_iff_toInt_lt,low,-Int32.toInt_add]

theorem registers (s : X86Memory.State) (y : Fixed) (h : Inputs s y) :
    (result s).core.regs=write s.regs 4 (s.regs 4+(4#32)) := by
  have saved : load32 (finalMemory s) (s.regs 4-(4#32))=s.regs 3 := by
    rw [final_keep _ _ h.saveHeight]
    exact load_store _ _ _
  simp only [result,saved]
  funext r
  by_cases hr : r=3 <;> simp [write,hr]

/-- A live or dead player below the bottom threshold follows the same update;
all other memory lies outside the two explicit written fields. -/
theorem live_correspondence (s : X86Memory.State) (f : Option Flags) (y : Fixed)
    (dead : Bool) (h : Inputs s y) :
    X86Routine.run WeaponLower.program [0x2d095] 6 ⟨s,f,0x2d490⟩=some (result s) ∧
    load32 (result s).core.memory (yAddress s)=(Weapon.lowerHeight y dead).raw.toBitVec ∧
    (result s).core.regs=write s.regs 4 (s.regs 4+(4#32)) ∧
    PlayerHeight.Frame s.memory (result s).core.memory [s.regs 4-(4#32),yAddress s] :=
  ⟨execution s f (below_height s y h) (return_address s y h),
    live_height s y dead h,registers s y h,result_frame s⟩
end Doom.Proofs.WeaponLowerProgress
