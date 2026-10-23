import Doom.Proofs.OriginalDivlineSide
set_option maxRecDepth 32768
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control OriginalDivlineSide
namespace DivlineSideFixtures
example : X86Routine.decodeAt [0x33,0x59,0x0c] 0=some (.xorMemory 3 ⟨some 1,none,0,12⟩,3) := by decide
example : X86Routine.decodeAt [0xf7,0xc3,0,0,0,0x80] 0=some (.testRegisterImmediate 3 0x80000000,6) := by decide
example : X86Routine.decodeAt [0x33,0xd9] 0=none := by decide
example : X86Routine.decodeAt [0x33,0x59] 0=none := by decide
example : X86Routine.decodeAt [0xf7,0xc3,0,0,0] 0=none := by decide
example : X86Routine.decodeAt [0xf7,0x03,0,0,0,0x80] 0=none := by decide
example (w : Word) : (logical32 (w &&& (0x80000000#32))).zero = !decide (w.toInt<0) := sign_zero w

def line (dx dy : Int32) : Collision.Divline :=
  { x:=⟨0⟩,y:=⟨0⟩,dx:=⟨dx⟩,dy:=⟨dy⟩ }
def memory (dx dy : Int32) : Memory :=
  [(0x600200,0),(0x600204,0),(0x600208,dx.toBitVec),
   (0x60020c,dy.toBitVec),(0x600100,0x2c637)].foldl (fun m (a,v) => store32 m a v) (fun _ => 0)
def fixture (dx dy x y : Int32) : X86Memory.State :=
  ⟨fun r => if r=0 then x.toBitVec else if r=2 then y.toBitVec else if r=3 then 0x600200
    else if r=4 then 0x600100 else BitVec.ofNat 32 (r.val*11),memory dx dy⟩
def answer (dx dy x y : Int32) := (result (fixture dx dy x y)).core.regs 0
example : answer 0 65536 0 0=(1#32) := by decide
example : answer 0 65536 1 0=(0#32) := by decide
example : answer 0 (-65536) 0 0=(0#32) := by decide
example : answer 0 (-65536) 1 0=(1#32) := by decide
example : answer 65536 0 0 0=(0#32) := by decide
example : answer 65536 0 0 1=(1#32) := by decide
example : answer (-65536) 0 0 0=(1#32) := by decide
example : answer (-65536) 0 0 1=(0#32) := by decide
example : answer 65536 65536 131072 65536=(0#32) := by decide
example : answer 65536 65536 65536 131072=(1#32) := by decide
example : answer 65536 65536 65536 65536=(1#32) := by decide
-- Shifts truncate both products to zero, but only after the sign shortcut.
example : answer 1 1 255 0=(1#32) := by decide
example : answer 1 1 0 (-1)=(0#32) := by decide
example : answer 1 1 (-1) 0=(1#32) := by decide
example : answer 1 1 2147483647 (-2147483648)=(0#32) := by decide
example : answer 0 0 0 0=(0#32) := by decide
example : (result (fixture 65536 65536 131072 65536)).pc=0x2c637 := by decide
example : (result (fixture 65536 65536 131072 65536)).core.regs 4=(0x600104#32) := by decide
example : (result (fixture 65536 65536 131072 65536)).core.regs 1=(11#32) := by decide
example : (result (fixture 65536 65536 131072 65536)).core.regs 5=(55#32) := by decide
example : (result (fixture 65536 65536 131072 65536)).core.regs 6=(66#32) := by decide
example : (result (fixture 65536 65536 131072 65536)).core.regs 7=(77#32) := by decide
example : Inputs (fixture 65536 65536 131072 65536) (line 65536 65536) ⟨131072⟩ ⟨65536⟩ 0x600200 := by
  constructor <;> try decide
  intro a ha off ho
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ha ho
  rcases ha with rfl|rfl|rfl|rfl <;> rcases ho with rfl|rfl|rfl|rfl <;>
    unfold BlockSummary.Apart <;> decide
end DivlineSideFixtures
