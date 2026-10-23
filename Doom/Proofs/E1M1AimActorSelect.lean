import Doom.Proofs.OriginalAimActorSelect
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1AimActorSelect
open Verification X86 X86Memory X86Control BlockSummary Collision
attribute [local irreducible] load32 store32

def program : X86Routine.Program := fun pc =>
  match OriginalAimActorSelect.program pc with
  | some op => some op
  | none => E1M1AimActorBottom.program pc

theorem contains_select (pc : Nat) (h : OriginalAimActorSelect.program pc≠none) :
    program pc=OriginalAimActorSelect.program pc := by
  unfold program; cases eq : OriginalAimActorSelect.program pc <;> simp_all

theorem contains_prior (pc : Nat) (h : E1M1AimActorBottom.program pc≠none) :
    program pc=E1M1AimActorBottom.program pc := by
  have absent : OriginalAimActorSelect.program pc=none := by
    by_cases inside : 0x2b8a9≤pc ∧ pc<0x2b8d2
    · have all : ∀ i : Fin 41, E1M1AimActorBottom.program (0x2b8a9+i.val)=none := by decide
      have eq : 0x2b8a9+(pc-0x2b8a9)=pc := by omega
      exact False.elim (h (by simpa only [eq] using all ⟨pc-0x2b8a9,by omega⟩))
    · simp [OriginalAimActorSelect.program,OriginalAimActorSelect.bytesProgram,inside]
  simp [program,absent]

/-- Both copies of the target top are required: the original comparison uses
ESI but retains EDI when no upper clipping is needed. -/
theorem clipping (s : X86Memory.State) (lower upper targetBottom targetTop : Int32)
    (low : OriginalAimActorSelect.lower s=lower.toBitVec)
    (up : s.regs 3=upper.toBitVec) (bot : s.regs 0=targetBottom.toBitVec)
    (top1 : s.regs 6=targetTop.toBitVec) (top2 : s.regs 7=targetTop.toBitVec) :
    (OriginalAimActorSelect.clipped s).regs 0=(max targetBottom lower).toBitVec ∧
    (OriginalAimActorSelect.clipped s).regs 7=(min targetTop upper).toBitVec ∧
    (OriginalAimActorSelect.clipped s).regs 1=s.regs 1 ∧
    (OriginalAimActorSelect.clipped s).regs 4=s.regs 4 ∧
    (OriginalAimActorSelect.clipped s).memory=s.memory := by
  have lowWord : load32 s.memory (0x2c1e4#32)=lower.toBitVec := low
  have maxWord : (if targetBottom.toInt<lower.toInt then lower.toBitVec else targetBottom.toBitVec)=
      (max targetBottom lower).toBitVec := by
    simp only [max,maxOfLe,Int32.le_iff_toInt_le]
    by_cases lt : targetBottom.toInt<lower.toInt
    · simp [lt,Int.le_of_lt lt]
    · by_cases le : targetBottom.toInt≤lower.toInt
      · have eq : targetBottom=lower := Int32.toInt_inj.mp (by omega)
        simp [eq]
      · simp [lt,le]
  by_cases ht : targetTop.toInt≤upper.toInt
  all_goals
    simp [OriginalAimActorSelect.clipped,OriginalAimActorSelect.topClip,
      OriginalAimActorSelect.bottomClip,OriginalAimActorSelect.loaded,OriginalAimActorSelect.lower,
      put,write,lowWord,top1,top2,bot,up,Int32.toInt_toBitVec,ht,min,minOfLe,Int32.le_iff_toInt_le]
    by_cases hb : targetBottom.toInt<lower.toInt
    · simp only [if_pos hb] at maxWord ⊢
      simp [write,bot,top2,maxWord]
    · simp only [if_neg hb] at maxWord ⊢
      simp [write,bot,top2,maxWord]

/-- Reuse the compiler sign-correction theorem from player bob: this is wrapped
Int32 addition followed by division toward zero, including negative odd sums. -/
theorem center (s : X86Memory.State) (bottom top : Int32)
    (bot : s.regs 0=bottom.toBitVec) (hi : s.regs 7=top.toBitVec) :
    OriginalAimActorSelect.half s=(AutoAim.center bottom top).raw.toBitVec := by
  unfold OriginalAimActorSelect.half OriginalAimActorSelect.sum AutoAim.center
  rw [bot,hi,PlayerHeight.half_word,← Int32.toBitVec_add,Int32.toInt_toBitVec]
  rfl

/-- Exact selected actor and centered slope are stored by the original bytes.
This ends before the callback's false-return epilogue. -/
theorem execution (s : X86Memory.State) (f : Option Flags)
    (lower upper targetBottom targetTop : Int32) (pointer : Word)
    (low : OriginalAimActorSelect.lower s=lower.toBitVec)
    (up : s.regs 3=upper.toBitVec) (bot : s.regs 0=targetBottom.toBitVec)
    (top1 : s.regs 6=targetTop.toBitVec) (top2 : s.regs 7=targetTop.toBitVec)
    (actor : s.regs 1=pointer) :
    (∃ n≤14, X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2b8a9⟩ (OriginalAimActorSelect.result s)) ∧
    (OriginalAimActorSelect.result s).pc=0x2b8d2 ∧
    (OriginalAimActorSelect.result s).core.regs 0=(AutoAim.center (max targetBottom lower) (min targetTop upper)).raw.toBitVec ∧
    (OriginalAimActorSelect.result s).core.regs 7=(min targetTop upper).toBitVec ∧
    (OriginalAimActorSelect.result s).core.regs 4=s.regs 4 ∧
    (OriginalAimActorSelect.result s).core.memory=
      store32 (store32 s.memory 0x2b9f8 pointer) 0x2b9b4
        (AutoAim.center (max targetBottom lower) (min targetTop upper)).raw.toBitVec ∧
    load32 (OriginalAimActorSelect.result s).core.memory (0x2b9f8#32)=pointer ∧
    load32 (OriginalAimActorSelect.result s).core.memory (0x2b9b4#32)=
      (AutoAim.center (max targetBottom lower) (min targetTop upper)).raw.toBitVec := by
  obtain ⟨n,hn,run⟩ := OriginalAimActorSelect.execution s f
  have run := (X86CodeMemory.lift_success run FloorCaller.cm).transfer program [] contains_select (by simp)
  have clip := clipping s lower upper targetBottom targetTop low up bot top1 top2
  have mid := center (OriginalAimActorSelect.clipped s) (max targetBottom lower) (min targetTop upper) clip.1 clip.2.1
  refine ⟨⟨n,hn,run⟩,rfl,?_,?_,?_,?_,?_,?_⟩
  all_goals simp [OriginalAimActorSelect.result,OriginalAimActorSelect.finish,OriginalAimActorSelect.c6,
    OriginalAimActorSelect.c5,OriginalAimActorSelect.c4,OriginalAimActorSelect.c3,OriginalAimActorSelect.c2,
    OriginalAimActorSelect.c1,put,write,mid,clip.2.1,clip.2.2.1,clip.2.2.2.1,clip.2.2.2.2,actor]
  · rw [load_store_apart _ _ _ _ (by unfold Apart; decide),load_store]
  · rw [load_store]
end Doom.Proofs.E1M1AimActorSelect
