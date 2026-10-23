import Doom.Proofs.E1M1PathIntercept
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
namespace PathInterceptFixture
def starts : Array Int32 := #[(-128), 1, 8388607, (-8388608), 2147483647, (-2147483648), 0, 8388608]
def portions : Array Int32 := #[65536, 32768, 1, (-65536), 2147483647, (-2147483648), 0, 65535]
def strides : Array Int32 := #[32768, (-65536), 2147483647, 65536, 2147483647, (-2147483648), 16777216, (-65536)]
def answers : Array Word := #[32767, 4294934528, 98302, 4294836224, 16711679, 4278190080, 0, 1]
def path (i : Fin 8) : Collision.PathStart :=
  {trace:=⟨⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩⟩,x1:=⟨-2147483648⟩,x2:=⟨2147483647⟩,
   y1:=⟨starts[i.val]'(by exact i.isLt)⟩,y2:=⟨-8388608⟩}
def portion (i : Fin 8) : Fixed := ⟨portions[i.val]'(by exact i.isLt)⟩
def stride (i : Fin 8) : Fixed := ⟨strides[i.val]'(by exact i.isLt)⟩
def machine (i : Fin 8) : X86Memory.State :=
  {regs:=fun r => if r=4 then 0xfffffffd else if r=6 then (path i).x1.raw.toBitVec
    else if r=7 then (path i).y1.raw.toBitVec else if r=5 then (path i).x2.raw.toBitVec
    else if r=1 then (path i).y2.raw.toBitVec else if r=3 then (portion i).raw.toBitVec
    else if r=0 then (stride i).raw.toBitVec else 0x12345678,
   memory:=store32 (store32 (fun _ => 0x5a) 13 (path i).startBlockY.toBitVec) 21 (path i).endBlockY.toBitVec}
theorem inputs (i : Fin 8) : OriginalPathIntercept.Inputs (machine i) (path i) (portion i) (stride i) := by
  constructor <;> revert i <;> decide +kernel
example (i : Fin 8) : OriginalPathIntercept.Ready (machine i) (OriginalPathIntercept.result (machine i))
    (path i) (portion i) (stride i) := OriginalPathIntercept.live _ _ _ _ (inputs i)
example : ∀ i : Fin 8, (Collision.pathFirstIntercept (path i).y1 (portion i) (stride i)).raw.toBitVec=
    answers[i.val]'(by exact i.isLt) := by decide +kernel
example : ∀ i : Fin 8, load32 (OriginalPathIntercept.result (machine i)).core.memory 41=
    answers[i.val]'(by exact i.isLt) := by decide +kernel
end PathInterceptFixture
