import Doom.Proofs.E1M1PathXStep
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
namespace PathXStepFixture
open OriginalPathXStep
-- Right, left, same column, and right with a saturated division.
def path (i : Fin 4) : Collision.PathStart :=
  {trace:=⟨⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩⟩,
   x1:=⟨if i.val=0 then 32768 else if i.val=1 then 25198592 else if i.val=2 then 65536 else 8388607⟩,
   x2:=⟨if i.val=0 then 25198592 else if i.val=1 then 32768 else if i.val=2 then 131072 else 8388609⟩,
   y1:=⟨0⟩,y2:=Fixed.ofInt 192}
def machine (i : Fin 4) : X86Memory.State :=
  {regs:=fun r => if r=4 then 1 else if r=6 then (path i).x1.raw.toBitVec
    else if r=5 then (path i).x2.raw.toBitVec else if r=2 then ((path i).y2-(path i).y1).raw.toBitVec else 0x12345678,
   memory:=store32 (store32 (store32 (fun _ => 0x5a) 9 (path i).xFraction.raw.toBitVec)
      13 (path i).startBlockX.toBitVec) 21 (path i).endBlockX.toBitVec}
def expected (i : Fin 4) : Int32 × Fixed × Fixed :=
  if i.val=0 then (1,⟨65280⟩,⟨32768⟩)
  else if i.val=1 then (-1,⟨256⟩,⟨32768⟩)
  else if i.val=2 then (0,Fixed.ofInt 1,Fixed.ofInt 256)
  else (1,⟨1⟩,⟨2147483647⟩)
theorem inputs (i : Fin 4) : Inputs (machine i) (path i) := by
  constructor <;> revert i <;> decide +kernel
theorem successful : ∀ i : Fin 4, (path i).xStep=.ok (expected i) := by
  simp only [Fin.forall_fin_succ,Fin.forall_fin_zero]
  exact ⟨rfl,rfl,rfl,rfl,True.intro⟩
example (i : Fin 4) : Safe (machine i) ∧ observe (machine i) (result (machine i))=liveObserve (expected i) :=
  live _ _ _ (inputs i) (successful i)
example (i : Fin 4) : ∃ n, n≤45 ∧ X86Routine.Prefix program [] n ⟨machine i,none,0x2c96c⟩ (result (machine i)) :=
  execution _ _ (live _ _ _ (inputs i) (successful i)).1
example : (result (machine 0)).pc=0x2c9d3 := result_pc _
example : OriginalAbs.value 0x80000000=0x80000000 := by decide +kernel
example : Collision.checkedPathAbs ⟨-2147483648⟩=.error "path: unverified abs(INT_MIN)" := rfl
end PathXStepFixture
