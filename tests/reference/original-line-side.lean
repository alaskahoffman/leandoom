import Doom.Proofs.OriginalLineSide
set_option maxRecDepth 32768
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control OriginalLineSide
namespace LineSideFixtures
example : X86Routine.decodeAt [0x0f,0x9f,0xc0] 0=some (.setGreater 0,3) := by decide
example : X86Routine.decodeAt [0x0f,0x9f,0xc7] 0=some (.setGreater 7,3) := by decide
example : X86Routine.decodeAt [0x0f,0x9f,0x00] 0=none := by decide
example : X86Routine.decodeAt [0x0f,0x9f] 0=none := by decide
example : X86Routine.execute (.setGreater 0) ⟨⟨fun _ => 0,fun _ => 0⟩,none,0⟩=none := by rfl

def line (dx dy : Int32) : Collision.Line :=
  { (default : Collision.Line) with x:=⟨0⟩,y:=⟨0⟩,dx:=⟨dx⟩,dy:=⟨dy⟩ }
def memory (dx dy : Int32) : Memory :=
  [(0x600200,0x600400),(0x600400,0),(0x600404,0),(0x600208,dx.toBitVec),
   (0x60020c,dy.toBitVec),(0x600100,0x2c65f)].foldl (fun m (a,v) => store32 m a v) (fun _ => 0)
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
-- Both shifted deltas truncate to zero: the original comparison is a tie.
example : answer 1 1 2147483647 (-2147483648)=(1#32) := by decide
example : answer 0 0 0 0=(0#32) := by decide
example : (result (fixture 65536 65536 131072 65536)).pc=0x2c65f := by decide
example : (result (fixture 65536 65536 131072 65536)).core.regs 4=(0x600104#32) := by decide
example : (result (fixture 65536 65536 131072 65536)).core.regs 1=(11#32) := by decide
example : (result (fixture 65536 65536 131072 65536)).core.regs 5=(55#32) := by decide
example : (result (fixture 65536 65536 131072 65536)).core.regs 6=(66#32) := by decide
example : (result (fixture 65536 65536 131072 65536)).core.regs 7=(77#32) := by decide
example : Inputs (fixture 65536 65536 131072 65536) (line 65536 65536) ⟨131072⟩ ⟨65536⟩ 0x600200 0x600400 := by
  constructor <;> try decide
  intro a ha off ho
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ha ho
  rcases ha with rfl|rfl|rfl|rfl|rfl <;> rcases ho with rfl|rfl|rfl|rfl <;>
    unfold BlockSummary.Apart <;> decide
end LineSideFixtures
