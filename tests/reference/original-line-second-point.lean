import Doom.Proofs.E1M1LineSecondPoint
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
namespace LineSecondPointFixtures
open OriginalLineSecondPoint

def wall : Collision.Line := { (default : Collision.Line) with x:=⟨0⟩,y:=⟨0⟩,dx:=⟨0⟩,dy:=⟨65536⟩ }
def ray (wide same : Bool) : Collision.Divline :=
  if wide then ⟨⟨-65536⟩,⟨if same then 131072 else 32768⟩,⟨2097152⟩,⟨0⟩⟩
  else ⟨⟨-131072⟩,⟨32768⟩,⟨if same then 65536 else 196608⟩,⟨0⟩⟩
def mem (wide same : Bool) : Memory :=
  [(0x600200,0x600400),(0x600204,0x600410),(0x600208,0),(0x60020c,65536),
   (0x600400,0),(0x600404,0),(0x600410,0),(0x600414,65536),
   (0x2ba10,(ray wide same).x.raw.toBitVec),(0x2ba14,(ray wide same).y.raw.toBitVec),
   (0x2ba18,(ray wide same).dx.raw.toBitVec),(0x2ba1c,(ray wide same).dy.raw.toBitVec),
   (0x600100,0x4f000),(0x600110,111),(0x600114,222),(0x600118,333),(0x60011c,444),
   (0x600120,555),(0x600124,0x4f000),(0x2c028,0x600800),(0x600800,0x12345678)].foldl
    (fun m (a,v) => store32 m a v) (fun _ => 0)
def fixture (wide same : Bool) : X86Memory.State :=
  ⟨fun r => if r=0 then OriginalLineSide.bit (firstSide (ray wide same) wall)
    else if r=1 then 0x600200 else if r=4 then 0x600100 else BitVec.ofNat 32 (r.val*11),mem wide same⟩

example : (result false (fixture false true)).pc=0x4f000 := by decide
example : (result true (fixture true true)).pc=0x4f000 := by decide
example : (result false (fixture false false)).pc=0x2c691 := by decide
example : (result true (fixture true false)).pc=0x2c691 := by decide
example : (result true (fixture true true)).core.regs 0=(1#32) := by decide
example : (result false (fixture false true)).core.regs 4=(0x600128#32) := by decide
example : (result false (fixture false true)).core.regs 5=(111#32) := by decide
example : (result false (fixture false true)).core.regs 6=(222#32) := by decide
example : (result false (fixture false true)).core.regs 2=(333#32) := by decide
example : (result false (fixture false true)).core.regs 1=(444#32) := by decide
example : (result false (fixture false true)).core.regs 3=(555#32) := by decide
example : (result false (fixture false true)).core.regs 7=(77#32) := by decide
example : load32 (result true (fixture true true)).core.memory 0x2c028=(0x600800#32) := by decide
example : load32 (result true (fixture true true)).core.memory 0x600800=(0x12345678#32) := by decide
example : Collision.lineIntercept (ray false true) wall=.ok none := same_side_none _ _ (by decide)
example : Collision.lineIntercept (ray true true) wall=.ok none := same_side_none _ _ (by decide)
example : (ray false false).usesDivlineTest=false := by decide
example : (ray true false).usesDivlineTest=true := by decide
example (wide same : Bool) : Inputs (fixture wide same) (ray wide same) wall 0x600200 0x600400 0x600410 := by
  cases wide <;> cases same
  all_goals constructor <;> try decide
  all_goals
    intro a ha off ho
    simp only [reads,List.mem_cons,List.not_mem_nil,or_false] at ha ho
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      rcases ho with rfl|rfl|rfl|rfl|rfl <;> unfold Apart <;> decide

def callback (wide same : Bool) := put (fixture wide same) 0 0x600200
example : (E1M1LineSecondPoint.continueTest (E1M1LineSecondPoint.firstReturn (callback false true))).pc=0x4f000 := by decide
example : (E1M1LineSecondPoint.continueTest (E1M1LineSecondPoint.firstReturn (callback true true))).pc=0x4f000 := by decide
example : (E1M1LineSecondPoint.continueTest (E1M1LineSecondPoint.firstReturn (callback false false))).pc=0x2c691 := by decide
example : (E1M1LineSecondPoint.continueTest (E1M1LineSecondPoint.firstReturn (callback true false))).pc=0x2c691 := by decide
end LineSecondPointFixtures
