import Doom.Proofs.E1M1LineCrossing
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open OriginalLineSecondPoint
namespace LineCrossingFixtures
def wall : Collision.Line := { (default : Collision.Line) with x:=⟨0⟩,y:=⟨0⟩,dx:=⟨0⟩,dy:=⟨65536⟩ }
def ray (wide same : Bool) : Collision.Divline :=
  if wide then ⟨⟨-65536⟩,⟨if same then 131072 else 32768⟩,⟨2097152⟩,⟨0⟩⟩
  else ⟨⟨-131072⟩,⟨32768⟩,⟨if same then 65536 else 196608⟩,⟨0⟩⟩
def mem (wide same : Bool) : Memory :=
  [(0x600200,0x600400),(0x600204,0x600410),(0x600208,0),(0x60020c,65536),
   (0x600400,0),(0x600404,0),(0x600410,0),(0x600414,65536),
   (0x2ba10,(ray wide same).x.raw.toBitVec),(0x2ba14,(ray wide same).y.raw.toBitVec),
   (0x2ba18,(ray wide same).dx.raw.toBitVec),(0x2ba1c,(ray wide same).dy.raw.toBitVec),
   (0x600100,0x2c578),(0x600110,111),(0x600114,222),(0x600118,333),(0x60011c,444),
   (0x600120,555),(0x600124,0x4f000),(0x2c028,0x600800),(0x600800,0x12345678)].foldl
    (fun m (a,v) => store32 m a v) (fun _ => 0)
def fixture (wide same : Bool) : X86Memory.State :=
  ⟨fun r => if r=0 then OriginalLineSide.bit (firstSide (ray wide same) wall)
    else if r=1 then 0x600200 else if r=4 then 0x600100 else BitVec.ofNat 32 (r.val*11),mem wide same⟩


def callback (wide : Bool) := put (fixture wide false) 0 0x600200
def fraction (wide : Bool) : Fixed := if wide then ⟨2048⟩ else ⟨43690⟩

theorem inputs (wide : Bool) : OriginalLineCrossing.Inputs (callback wide) (ray wide false) wall 0x600200 0x600400 0x600410 := by
  cases wide
  all_goals
    constructor
    · constructor <;> try decide
      intro a ha off ho
      simp only [OriginalLineInterceptEntry.reads,List.mem_cons,List.not_mem_nil,or_false] at ha ho
      rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases ho with rfl|rfl|rfl|rfl|rfl <;> unfold Apart <;> decide
    · constructor <;> try decide
      intro a ha off ho
      simp only [OriginalLineSecondPoint.reads,List.mem_cons,List.not_mem_nil,or_false] at ha ho
      rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> unfold Apart <;> decide
    · decide

theorem scratch (wide : Bool) (a : Word)
    (ha : a∈[(0x600200#32),0x600208,0x60020c,0x600400,0x600404,0x2ba10,0x2ba14,0x2ba18,0x2ba1c,0x2c024,0x600232,0x2c028]) :
    OriginalLineCrossing.ScratchSafe (callback wide) a := by
  intro off ho
  change Apart a ((0x600100#32)-(36#32)+off)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
  simp only [OriginalLineTail.stackOffsets,List.mem_cons,List.not_mem_nil,or_false] at ho
  rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> unfold Apart <;> decide

theorem sides (wide : Bool) (a : Word) (ha : a∈[(0x2c024#32),0x600232,0x2c028]) :
    OriginalLineCrossing.SideSafe (callback wide) a := by
  intro off ho
  change Apart a ((0x600100#32)-off)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ha ho
  rcases ha with rfl|rfl|rfl <;>
    rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> unfold Apart <;> decide

theorem tail (wide : Bool) : OriginalLineCrossing.TailData (callback wide) (ray wide false) wall (fraction wide) 0 0x600200 0x600400 := by
  constructor
  · cases wide <;> rfl
  · intro a ha
    apply scratch
    simp only [OriginalLineFraction.reads,List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp
  · cases wide <;> decide
  · cases wide <;> decide
  · exact ⟨sides wide _ (by simp),scratch wide _ (by simp)⟩
  · exact ⟨sides wide _ (by simp),scratch wide _ (by simp)⟩
  · exact ⟨sides wide _ (by simp),scratch wide _ (by simp)⟩
  · cases wide <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl|rfl <;> cases wide <;> unfold Apart <;> decide

example (wide : Bool) : ∃ n≤270, X86Routine.Prefix OriginalLineCrossing.program [] n
    ⟨callback wide,none,0x2c5f0⟩ (OriginalLineCrossing.result (callback wide)) :=
  OriginalLineCrossing.execution _ _ _ _ _ _ (inputs wide) _ _ (tail wide) none
example : (OriginalLineCrossing.result (callback false)).core.regs 2=(24#32) := by decide
example : (OriginalLineCrossing.result (callback true)).core.regs 4=(0x600104#32) := by decide
example : (OriginalLineCrossing.result (callback true)).pc=0x2c57f := by decide
example : load32 (OriginalLineCrossing.result (callback false)).core.memory (0x600800#32)=(43690#32) := by decide
example : load32 (OriginalLineCrossing.result (callback true)).core.memory (0x600800#32)=(2048#32) := by decide
example : load32 (OriginalLineCrossing.result (callback true)).core.memory (0x2c028#32)=(0x60080c#32) := by decide
end LineCrossingFixtures
