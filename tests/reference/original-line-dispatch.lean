import Doom.Proofs.OriginalLineMixed
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open OriginalLineSecondPoint
namespace LineDispatchFixtures
def wall : Collision.Line := { (default : Collision.Line) with x:=⟨0⟩,y:=⟨0⟩,dx:=⟨0⟩,dy:=⟨65536⟩ }
def ray (wide same : Bool) : Collision.Divline :=
  if wide then ⟨⟨-65536⟩,⟨if same then 131072 else 32768⟩,⟨2097152⟩,⟨0⟩⟩
  else ⟨⟨-131072⟩,⟨32768⟩,⟨if same then 65536 else 196608⟩,⟨0⟩⟩
def mem (wide same : Bool) : Memory :=
  [(0x600200,0x600400),(0x600204,0x600410),(0x600208,0),(0x60020c,65536),
   (0x600400,0),(0x600404,0),(0x600410,0),(0x600414,65536),
   (0x2ba10,(ray wide same).x.raw.toBitVec),(0x2ba14,(ray wide same).y.raw.toBitVec),
   (0x2ba18,(ray wide same).dx.raw.toBitVec),(0x2ba1c,(ray wide same).dy.raw.toBitVec),
   (0x600100,0xdeadbeef),(0x600104,0x2c5f0),(0x600108,777),(0x60010c,0x4f000),(0x13580,99),(0x2c120,0x600200),(0x600900,0),(0x600904,0xffff),(0x600110,111),(0x600114,222),(0x600118,333),(0x60011c,444),
   (0x600120,555),(0x600124,0x4f000),(0x2c028,0x600800),(0x600800,0x12345678)].foldl
    (fun m (a,v) => store32 m a v) (fun _ => 0)
def fixture (wide same : Bool) : X86Memory.State :=
  ⟨fun r => if r=0 then OriginalLineSide.bit (firstSide (ray wide same) wall)
    else if r=1 then 0x600200 else if r=4 then 0x600100 else BitVec.ofNat 32 (r.val*11),mem wide same⟩


def iterator (wide : Bool) : X86Memory.State :=
  ⟨fun r => if r=2 then 0x600900 else if r=4 then 0x600104 else 0,mem wide false⟩
def callback (wide : Bool) := OriginalLineDispatch.view (iterator wide)
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
  change Apart a ((OriginalLineDispatch.entry (iterator wide)).core.regs 4-(36#32)+off)
  rw [(OriginalLineDispatch.entry_regs (iterator wide)).2.2]
  have sp : (iterator wide).regs 4-(4#32)=(0x600100#32) := by cases wide <;> decide
  rw [sp]
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
  simp only [OriginalLineTail.stackOffsets,List.mem_cons,List.not_mem_nil,or_false] at ho
  rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> unfold Apart <;> decide

theorem sides (wide : Bool) (a : Word) (ha : a∈[(0x2c024#32),0x600232,0x2c028]) :
    OriginalLineCrossing.SideSafe (callback wide) a := by
  intro off ho
  change Apart a ((OriginalLineDispatch.entry (iterator wide)).core.regs 4-off)
  rw [(OriginalLineDispatch.entry_regs (iterator wide)).2.2]
  have sp : (iterator wide).regs 4-(4#32)=(0x600100#32) := by cases wide <;> decide
  rw [sp]
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ha ho
  rcases ha with rfl|rfl|rfl <;>
    rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> unfold Apart <;> decide

theorem tail (wide : Bool) : OriginalLineDispatch.TailData (iterator wide) (ray wide false) wall (fraction wide) 0 0x600200 0x600400 := by
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
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl|rfl <;> cases wide <;> unfold Apart <;> decide

  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl <;> cases wide <;> constructor <;> unfold Apart <;> decide

theorem fresh (wide : Bool) : OriginalLineDispatch.Fresh (iterator wide) := by
  cases wide <;> constructor <;> try decide
  all_goals unfold Apart; decide

theorem ready (wide : Bool) : OriginalLineDispatch.Ready (iterator wide) (ray wide false) wall (fraction wide) 0 0x600200 0x600400 0x600410 := by
  refine ⟨fresh wide,inputs wide,?_,tail wide⟩
  intro a ha
  simp only [OriginalLineSecondPoint.reads,List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    cases wide <;> constructor <;> unfold Apart <;> decide

def start (wide : Bool) : X86Control.State := ⟨iterator wide,none,0x2c57f⟩

theorem admitted (wide : Bool) : OriginalLineMixed.Admitted 2 (start wide) := by
  refine ⟨(fresh wide).item,?_,?_⟩
  · intro _
    refine ⟨ray wide false,wall,fraction wide,0,0x600200,0x600400,0x600410,ready wide,?_,?_⟩
    · intro a ha
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl <;> cases wide <;> unfold Apart <;> decide
    · cases wide <;> decide
  · change OriginalLineMixed.Admitted 1 (OriginalLineMixed.step (iterator wide))
    rw [OriginalLineMixed.step,if_neg (fresh wide).unseen]
    refine ⟨?_,?_,trivial⟩
    · cases wide <;> decide
    · intro missing
      have seen : OriginalLineCell.already (OriginalLineCell.header (OriginalLineDispatch.result (iterator wide)).core).core := by
        cases wide <;> decide
      exact False.elim (missing seen)

example (wide : Bool) : ∃ steps≤569, X86Routine.Prefix OriginalLineMixed.program [] steps (start wide)
    (OriginalLineBounds.returned (OriginalLineCell.header (OriginalLineMixed.run 2 (start wide)).core).core) :=
  OriginalLineMixed.through_sentinel 2 (start wide) rfl (admitted wide) (by cases wide <;> decide)

-- Line zero is fresh on the first visit; the second visit sees its new stamp.
example : OriginalLineCell.item (iterator false)=(0#16) := by decide
example : load32 (OriginalLineDispatch.entry (iterator false)).core.memory (0x600100#32)=(0x2c578#32) := by decide
example : load32 (OriginalLineDispatch.result (iterator false)).core.memory (0x600236#32)=(99#32) := by decide
example : (OriginalLineMixed.run 2 (start false)).core.regs 2=(0x600904#32) := by decide
example : load32 (OriginalLineMixed.run 2 (start false)).core.memory (0x2c028#32)=(0x60080c#32) := by decide
example : load32 (OriginalLineMixed.run 2 (start true)).core.memory (0x600800#32)=(2048#32) := by decide
example : (OriginalLineBounds.returned (OriginalLineCell.header (OriginalLineMixed.run 2 (start false)).core).core).pc=0x4f000 := by decide
end LineDispatchFixtures
