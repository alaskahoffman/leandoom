import Doom.Proofs.OriginalPathAdvance
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1PathAdvance
open Verification X86 X86Memory X86Control BlockSummary
open OriginalPathAdvance

/-- Numeric state read by the original end-of-cell block. All arithmetic wraps;
the loop counter is interpreted as 0..63 separately. -/
structure Cell where
  mapX : Word
  mapY : Word
  endX : Word
  endY : Word
  xi : Word
  yi : Word
  xDirection : Word
  yDirection : Word
  xStride : Word
  yStride : Word
  count : Word
  deriving DecidableEq

def observe (s : X86Memory.State) : Cell :=
  ⟨s.regs 6,s.regs 1,localWord s 20,localWord s 24,s.regs 5,localWord s 44,
    localWord s 32,localWord s 28,localWord s 36,localWord s 40,s.regs 7⟩

def ended (g : Cell) : Bool := g.mapX==g.endX && g.mapY==g.endY
/-- This is the numeric fragment of Path.pathTraverse, after the cell visitors.
The first matching axis wins; a stall still consumes an iteration. -/
def axis (g : Cell) : Cell :=
  if g.yi.sshiftRight 16=g.mapY then
    {g with yi:=g.yi+g.yStride, mapX:=g.mapX+g.xDirection}
  else if g.xi.sshiftRight 16=g.mapX then
    {g with xi:=g.xi+g.xStride, mapY:=g.mapY+g.yDirection}
  else g

def step (g : Cell) : Cell :=
  if ended g then g else {axis g with count:=g.count+1}
def nextPc (g : Cell) : Nat :=
  if ended g then 0x2cafd else if (g.count+1).toInt<64 then 0x2ca7f else 0x2cafd

theorem slot_frame (s : X86Memory.State) (v off : Word)
    (member : off∈[(20#32),24,28,32,36,40]) :
    load32 (store32 s.memory (s.regs 4+(44#32)) v) (s.regs 4+off)=localWord s off := by
  apply load_store_apart
  apply OriginalPathXStep.apart_translate
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl <;> unfold Apart <;> decide

@[local simp] theorem slot20 (s : X86Memory.State) (v : Word) :
    load32 (store32 s.memory (s.regs 4+(44#32)) v) (s.regs 4+(20#32))=localWord s 20 := slot_frame s v 20 (by simp)
@[local simp] theorem slot24 (s : X86Memory.State) (v : Word) :
    load32 (store32 s.memory (s.regs 4+(44#32)) v) (s.regs 4+(24#32))=localWord s 24 := slot_frame s v 24 (by simp)
@[local simp] theorem slot28 (s : X86Memory.State) (v : Word) :
    load32 (store32 s.memory (s.regs 4+(44#32)) v) (s.regs 4+(28#32))=localWord s 28 := slot_frame s v 28 (by simp)
@[local simp] theorem slot32 (s : X86Memory.State) (v : Word) :
    load32 (store32 s.memory (s.regs 4+(44#32)) v) (s.regs 4+(32#32))=localWord s 32 := slot_frame s v 32 (by simp)
@[local simp] theorem slot36 (s : X86Memory.State) (v : Word) :
    load32 (store32 s.memory (s.regs 4+(44#32)) v) (s.regs 4+(36#32))=localWord s 36 := slot_frame s v 36 (by simp)
@[local simp] theorem slot40 (s : X86Memory.State) (v : Word) :
    load32 (store32 s.memory (s.regs 4+(44#32)) v) (s.regs 4+(40#32))=localWord s 40 := slot_frame s v 40 (by simp)

/-- The sole write is the Y-intercept local on the X branch. -/
theorem selected_observe (s : X86Memory.State) :
    observe (selected s).core=axis (observe s) ∧ (selected s).core.regs 4=s.regs 4 ∧
    (selected s).core.memory=if takeX s then store32 s.memory (s.regs 4+44)
      (localWord s 44+localWord s 40) else s.memory := by
  by_cases hx : takeX s <;> by_cases hy : takeY s <;>
    simp_all [observe,axis,selected,takeX,takeY,xcheck,x2,x1,ycheck,y2,y1,
      xadvanced,a6,a5,a4,a3,a2,a1,yadvanced,b4,b3,b2,b1,put,write,localWord,load_store]

/-- Every numeric field required by the next iteration agrees, including
unchanged endpoint, direction and stride locals. -/
theorem result_observe (s : X86Memory.State) :
    observe (OriginalPathAdvance.result s).core=step (observe s) ∧
    (OriginalPathAdvance.result s).pc=nextPc (observe s) ∧
    (OriginalPathAdvance.result s).core.regs 4=s.regs 4 := by
  have selected := selected_observe s
  have count : (OriginalPathAdvance.selected s).core.regs 7=s.regs 7 := by
    have eq := congrArg Cell.count selected.1
    have same : (axis (observe s)).count=(observe s).count := by
      unfold axis; split <;> (try split) <;> rfl
    exact eq.trans same
  by_cases h : atEnd s
  · simp_all [OriginalPathAdvance.result,gate,step,nextPc,ended,observe,atEnd]
  · simp only [OriginalPathAdvance.result,if_neg h,counted]
    have obs : observe (incremented (OriginalPathAdvance.selected s).core)=
        {observe (OriginalPathAdvance.selected s).core with count:=(OriginalPathAdvance.selected s).core.regs 7+1} := by
      simp [observe,incremented,localWord,put,write]
    rw [obs,selected.1,count]
    simp_all [step,nextPc,ended,observe,atEnd,incremented,put,write]

/-- Bit-vector shifts/additions are exactly the signed Int32 and Fixed operations
used in Path.pathTraverse's two-axis fragment, including negative intercepts. -/
def productionAxis (mapx mapy : Int32) (xi yi : Fixed)
    (mapxstep mapystep : Int32) (xstep ystep : Fixed) : Int32 × Int32 × Fixed × Fixed :=
  if yi.raw >>> 16 == mapy then (mapx+mapxstep,mapy,xi,yi+ystep)
  else if xi.raw >>> 16 == mapx then (mapx,mapy+mapystep,xi+xstep,yi)
  else (mapx,mapy,xi,yi)

def numeric (g : Cell) : Word × Word × Word × Word := (g.mapX,g.mapY,g.xi,g.yi)

theorem production_axis (mapx mapy : Int32) (xi yi : Fixed)
    (mapxstep mapystep : Int32) (xstep ystep : Fixed) (endx endy count : Word) :
    let g : Cell := ⟨mapx.toBitVec,mapy.toBitVec,endx,endy,xi.raw.toBitVec,yi.raw.toBitVec,
      mapxstep.toBitVec,mapystep.toBitVec,xstep.raw.toBitVec,ystep.raw.toBitVec,count⟩
    let p := productionAxis mapx mapy xi yi mapxstep mapystep xstep ystep
    numeric (axis g)=(p.1.toBitVec,p.2.1.toBitVec,p.2.2.1.raw.toBitVec,p.2.2.2.raw.toBitVec) := by
  have sx : (yi.raw >>> 16=mapy) ↔ yi.raw.toBitVec.sshiftRight 16=mapy.toBitVec := by
    rw [← Int32.toBitVec_inj]; rfl
  have sy : (xi.raw >>> 16=mapx) ↔ xi.raw.toBitVec.sshiftRight 16=mapx.toBitVec := by
    rw [← Int32.toBitVec_inj]; rfl
  by_cases hx : yi.raw >>> 16=mapy <;> by_cases hy : xi.raw >>> 16=mapx <;>
    simp_all [productionAxis,axis,numeric,Fixed.add,Int32.toBitVec_add]

/-- The signed DOS counter test is the finite-loop budget on legal iteration
indices. This is not a claim for an arbitrary corrupted/negative counter. -/
theorem counter_limit (n : Nat) (bound : n<64) :
    ((BitVec.ofNat 32 n+(1#32)).toInt<64 ↔ n+1<64) := by
  have all : ∀ i : Fin 64, ((BitVec.ofNat 32 i.val+(1#32)).toInt<64 ↔ i.val+1<64) := by decide
  exact all ⟨n,bound⟩

/-- Refinement of the decoded byte block, without assuming its branch result. -/
theorem execution (s : X86Memory.State) (f : Option Flags) :
    (∃ n≤19, X86Routine.Prefix program [] n ⟨s,f,0x2cab5⟩ (OriginalPathAdvance.result s)) ∧
    observe (OriginalPathAdvance.result s).core=step (observe s) ∧
    (OriginalPathAdvance.result s).pc=nextPc (observe s) ∧
    (OriginalPathAdvance.result s).core.regs 4=s.regs 4 :=
  ⟨OriginalPathAdvance.execution s f,result_observe s⟩
end Doom.Proofs.E1M1PathAdvance
