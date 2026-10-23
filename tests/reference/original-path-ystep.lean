import Doom.Proofs.E1M1PathGridSetup
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
namespace PathYStepFixture
open OriginalPathYStep
-- Up, down, same row, and up with a saturated division.
def path (i : Fin 4) : Collision.PathStart :=
  {trace:=⟨⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩⟩,
   y1:=⟨if i.val=0 then 32768 else if i.val=1 then 25198592 else if i.val=2 then 65536 else 8388607⟩,
   y2:=⟨if i.val=0 then 25198592 else if i.val=1 then 32768 else if i.val=2 then 131072 else 8388609⟩,
   x1:=⟨0⟩,x2:=Fixed.ofInt 192}
def machine (i : Fin 4) : X86Memory.State :=
  {regs:=fun r => if r=4 then 1 else if r=6 then (path i).x1.raw.toBitVec
    else if r=5 then ((path i).x2-(path i).x1).raw.toBitVec
    else if r=0 then ((path i).y2-(path i).y1).raw.toBitVec
    else if r=1 then (path i).startBlockY.toBitVec
    else if r=2 then (path i).endBlockY.toBitVec
    else if r=3 then (path i).yFraction.raw.toBitVec else 0x12345678,
   memory:=store32 (store32 (fun _ => 0x5a) 13 (path i).startBlockX.toBitVec) 17 (path i).startBlockY.toBitVec}
def expected (i : Fin 4) : Int32 × Fixed × Fixed :=
  if i.val=0 then (1,⟨65280⟩,⟨32768⟩)
  else if i.val=1 then (-1,⟨256⟩,⟨32768⟩)
  else if i.val=2 then (0,Fixed.ofInt 1,Fixed.ofInt 256)
  else (1,⟨1⟩,⟨2147483647⟩)
theorem inputs (i : Fin 4) : Inputs (machine i) (path i) := by
  constructor <;> revert i <;> decide +kernel
theorem successful : ∀ i : Fin 4, (path i).yStep=.ok (expected i) := by
  simp only [Fin.forall_fin_succ,Fin.forall_fin_zero]
  exact ⟨rfl,rfl,rfl,rfl,True.intro⟩
example (i : Fin 4) : Safe (machine i) ∧ observe (machine i) (result (machine i))=liveObserve (expected i) :=
  live _ _ _ (inputs i) (successful i)
example (i : Fin 4) : ∃ n, n≤41 ∧ X86Routine.Prefix program [] n ⟨machine i,comparison (machine i),0x2ca10⟩ (result (machine i)) :=
  execution _ (live _ _ _ (inputs i) (successful i)).1
example : (result (machine 0)).pc=0x2ca5f := result_pc _
example : OriginalAbs.value 0x80000000=0x80000000 := by decide +kernel
example : Collision.checkedPathAbs ⟨-2147483648⟩=.error "path: unverified abs(INT_MIN)" := rfl


theorem second_inputs (i : Fin 4) : OriginalPathSecondIntercept.Inputs (result (machine i)).core
    (path i) (expected i).2.1 (expected i).2.2 := by
  apply E1M1PathGridSetup.second_inputs (machine i) (path i) (expected i) (inputs i) (successful i)
  all_goals revert i; decide +kernel
example (i : Fin 4) : OriginalPathSecondIntercept.Ready (result (machine i)).core
    (E1M1PathGridSetup.after (machine i)) (path i) (expected i).2.1 (expected i).2.2 :=
  OriginalPathSecondIntercept.live _ _ _ _ (second_inputs i)
example : ∀ i : Fin 4, (E1M1PathGridSetup.after (machine i)).core.regs 5=
    (if i.val=0 then 32640 else if i.val=1 then 128 else if i.val=2 then 16777216 else 32767) := by decide +kernel
example (i : Fin 4) : load32 (E1M1PathGridSetup.after (machine i)).core.memory (1+44)=
    load32 (machine i).memory (1+44) := E1M1PathGridSetup.after_local (machine i) 44 (by simp)
end PathYStepFixture
