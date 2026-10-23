import Doom.Proofs.OriginalLineInvariant
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open OriginalLineSecondPoint
namespace LineInvariantFixtures
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
  ⟨fun r => if r=2 then 0x600900 else if r=4 then 0x600104 else 0,mem wide true⟩
def callback (wide : Bool) := OriginalLineDispatch.view (iterator wide)
def fraction (wide : Bool) : Fixed := if wide then ⟨2048⟩ else ⟨43690⟩

theorem inputs (wide : Bool) : OriginalLineReject.Inputs (callback wide) (ray wide true) wall 0x600200 0x600400 0x600410 := by
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

open OriginalLineInvariant

def protectedWords : List Word := OriginalLineSecondPoint.reads 0x600200 0x600400 0x600410 ++
  [0x600900,0x600902,0x600904,0x600104,0x13580,0x2c120,0x600108,0x60010c,0x2c028,0x600800]

def plan (wide : Bool) : Initial (iterator wide) 2 := by
  refine ⟨protectedWords,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i hi
    have cases : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases cases with rfl|rfl|rfl <;> cases wide <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl <;> cases wide <;> decide
  · cases wide <;> decide
  · intro i hi
    have cases : i=0 ∨ i=1 := by omega
    rcases cases with rfl|rfl <;> cases wide <;> decide
  · cases wide <;> decide
  · intro i hi
    refine ⟨ray wide true,wall,0x600200,0x600400,0x600410,?_,?_⟩
    · apply reject_inputs (callback wide) _ _ _ _ _ _ (inputs wide)
      · change (OriginalLineDispatch.entry (atIndex (iterator wide) i)).core.regs 0 =
          (OriginalLineDispatch.entry (iterator wide)).core.regs 0
        rw [(OriginalLineDispatch.entry_regs _).1,(OriginalLineDispatch.entry_regs _).1]
        have cases : i=0 ∨ i=1 := by omega
        rcases cases with rfl|rfl <;> cases wide <;> decide
      · change (OriginalLineDispatch.entry (atIndex (iterator wide) i)).core.regs 4 =
          (OriginalLineDispatch.entry (iterator wide)).core.regs 4
        rw [(OriginalLineDispatch.entry_regs _).2.2,(OriginalLineDispatch.entry_regs _).2.2]
        rfl
      · intro a ha; rfl
    · intro a ha; exact List.mem_append_left _ ha
  · intro i hi a ha
    have cases : i=0 ∨ i=1 := by omega
    have stamp : OriginalLineDispatch.stamp (atIndex (iterator wide) i)=(0x600236#32) := by
      rcases cases with rfl|rfl <;> cases wide <;> decide
    have stack : (atIndex (iterator wide) i).regs 4=(0x600104#32) := rfl
    have sp : (OriginalLineDispatch.view (atIndex (iterator wide) i)).regs 4=(0x600100#32) :=
      (OriginalLineDispatch.entry_regs _).2.2.trans (by rw [stack]; decide)
    simp only [OriginalLineDispatch.Safe,OriginalLineCrossing.SideSafe,stamp,stack,sp]
    simp only [protectedWords,OriginalLineSecondPoint.reads,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at ha
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals
      constructor
      · constructor <;> unfold Apart <;> decide
      · intro off ho
        simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
        rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> unfold Apart <;> decide
  · intro i hi
    have cases : i=0 ∨ i=1 := by omega
    rcases cases with rfl|rfl <;> cases wide <;> unfold Apart <;> decide

-- The entire run follows from one initial contract: no post-step geometry,
-- visited predicate, target, or final-sentinel premise is supplied here.
example (wide : Bool) : ∃ steps≤363, X86Routine.Prefix OriginalLineInvariant.program [] steps
    ⟨iterator wide,none,0x2c57f⟩ (finished 2 ⟨iterator wide,none,0x2c57f⟩) :=
  (through_sentinel (iterator wide) 2 (plan wide) none).1
example (wide : Bool) : OriginalLineTraversal.Runs ⟨iterator wide,none,0x2c57f⟩
    (finished 2 ⟨iterator wide,none,0x2c57f⟩) 2 :=
  (through_sentinel (iterator wide) 2 (plan wide) none).2
example (wide : Bool) : load32 (finished 2 ⟨iterator wide,none,0x2c57f⟩).core.memory 0x2c028 =
    load32 (iterator wide).memory 0x2c028 :=
  OriginalLineInvariant.frame (iterator wide) 2 (plan wide) none _ (by cases wide <;> decide)
example (wide : Bool) : (finished 2 ⟨iterator wide,none,0x2c57f⟩).pc=0x4f000 := by
  have out := parent_return (iterator wide) 2 (plan wide) none
    (by cases wide <;> decide) (by cases wide <;> decide)
  exact out.2.2.2.trans (by cases wide <;> decide)
example : ¬OriginalLineCell.already (OriginalLineCell.header (iterator false)).core := by decide
example : (0x600236#32) ∉ (plan false).words := by decide
example : OriginalLineCell.already (OriginalLineCell.header (step (iterator false)).core).core := by decide
example : (run 2 ⟨iterator true,none,0x2c57f⟩).core.regs 2=(0x600904#32) := by decide
example : load32 (run 2 ⟨iterator true,none,0x2c57f⟩).core.memory (0x600236#32)=(99#32) := by decide
end LineInvariantFixtures
