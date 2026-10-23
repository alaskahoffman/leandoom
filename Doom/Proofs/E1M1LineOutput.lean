import Doom.Proofs.E1M1LineSource
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1LineOutput
open Verification X86 X86Memory X86Control BlockSummary E1M1LineIteration

structure Sides where
  frontIndex : BitVec 16
  backIndex : BitVec 16
  front : Word
  back : Word
  deriving Inhabited

def line (e : Sides) (address : Word) : OriginalGroupOutput.Line := ⟨address,e.front,e.back⟩
def sideReads (base : Word) (i : BitVec 16) : List Word :=
  if i=65535 then [] else [E1M1NoiseGraph.sideAddress base i]
def reads (e : Sides) (raw base : Word) : List Word :=
  [0x2c118,raw+10,raw+12]++sideReads base e.frontIndex++sideReads base e.backIndex
structure Source (e : Sides) (raw base : Word) (m : Memory) : Prop where
  sideBase : load32 m 0x2c118=base
  frontRead : load16 m (raw+10)=e.frontIndex
  backRead : load16 m (raw+12)=e.backIndex
  front : E1M1LineCache.target m base e.frontIndex=e.front
  back : E1M1LineCache.target m base e.backIndex=e.back

def Separated (e : Sides) (raw base output sp : Word) : Prop :=
  ∀ a∈reads e raw base, E1M1LineFrame.Protected a output sp

theorem target_transport {m n : Memory} {base : Word} {i : BitVec 16}
    (same : ∀ a∈sideReads base i, load32 n a=load32 m a) :
    E1M1LineCache.target n base i=E1M1LineCache.target m base i := by
  unfold E1M1LineCache.target
  split
  · rfl
  · rename_i present
    change i≠(65535#16) at present
    exact same _ (by simp [sideReads,present])

theorem transport {e raw base m n} (source : Source e raw base m)
    (same : ∀ a∈reads e raw base, load32 n a=load32 m a) : Source e raw base n := by
  refine ⟨(same _ (by simp [reads])).trans source.sideBase,
    (E1M1LineSource.half_of_word (same _ (by simp [reads]))).trans source.frontRead,
    (E1M1LineSource.half_of_word (same _ (by simp [reads]))).trans source.backRead,?_,?_⟩
  · exact (target_transport (fun a ha => same a (by simp [reads,ha]))).trans source.front
  · exact (target_transport (fun a ha => same a (by simp [reads,ha]))).trans source.back

/-- State before the raw side-index copy, after all earlier geometry and calls. -/
def copyInput (s : X86Memory.State) :=
  (OriginalLineGeometry.bounds (E1M1LineFrame.beforeBounds s)).core
@[simp] theorem copy_reg (s : X86Memory.State) (r : Reg) (h : r∈[1,3]) :
    (copyInput s).regs r=s.regs r := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl <;> simp [copyInput]

theorem copy_frame (s : X86Memory.State) (a : Word)
    (h : E1M1LineFrame.Protected a (s.regs 3) (s.regs 4)) :
    load32 (copyInput s).memory a=load32 s.memory a := by
  have box := OriginalLineGeometry.bounds_frame (E1M1LineFrame.beforeBounds s) a (by
    intro off mem
    rw [E1M1LineFrame.before_reg s 3 (by simp)]
    exact h.words off (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at mem ⊢
      rcases mem with rfl|rfl|rfl|rfl <;> simp))
  exact box.trans (E1M1LineFrame.before_frame s a h)

/-- Construct the existing suffix contract from the initial raw side records.
Absent sides require no side-table read or separation at a dummy address. -/
def copy_source (e : Sides) (base : Word) (s : X86Memory.State)
    (source : Source e (s.regs 1) base s.memory)
    (sep : Separated e (s.regs 1) base (s.regs 3) (s.regs 4)) :
    E1M1LineLoad.Source (line e (s.regs 3)) (copyInput s) := by
  have copied := transport source (fun a ha => copy_frame s a (sep a ha))
  have global := sep 0x2c118 (by simp [reads])
  have front (present : e.frontIndex≠(65535#16)) :=
    sep (E1M1NoiseGraph.sideAddress base e.frontIndex) (by simp [reads,sideReads,present])
  have back (present : e.backIndex≠(65535#16)) :=
    sep (E1M1NoiseGraph.sideAddress base e.backIndex) (by simp [reads,sideReads,present])
  refine ⟨e.frontIndex,e.backIndex,base,copy_reg s 3 (by simp),copied.sideBase,
    ?_,?_,?_,copied.front,copied.back,?_,?_,?_,?_,?_⟩
  · rw [copy_reg s 1 (by simp)]; exact copied.frontRead
  · rw [copy_reg s 1 (by simp)]; exact copied.backRead
  · have apart := (sep (s.regs 1+12) (by simp [reads])).halves 22 (by simp)
    rw [copy_reg s 1 (by simp)]
    intro i j eq
    exact apart ⟨i.val,by have := i.isLt; omega⟩ j eq
  · exact ⟨global.halves 22 (by simp),global.halves 24 (by simp)⟩
  · intro h; exact ⟨(front h).halves 22 (by simp),(front h).halves 24 (by simp)⟩
  · intro h; exact ⟨(back h).halves 22 (by simp),(back h).halves 24 (by simp)⟩
  · exact global.words 46 (by simp)
  · intro h; exact (back h).words 46 (by simp)

/-- One complete iteration establishes the two cached pointers consumed by
P_GroupLines. No already-cached pointer is assumed at entry. -/
theorem iteration_output (e : Sides) (base : Word) (s : X86Memory.State)
    (source : Source e (s.regs 1) base s.memory)
    (sep : Separated e (s.regs 1) base (s.regs 3) (s.regs 4)) :
    load32 (result s).core.memory (s.regs 3+46)=e.front ∧
    load32 (result s).core.memory (s.regs 3+50)=e.back := by
  obtain ⟨out,run,inputs,_⟩ := E1M1LineLoad.establishes (line e (s.regs 3)) (copyInput s) none
    (copy_source e base s source sep)
  rw [OriginalLineLoad.joined_execution] at run
  have eq := Option.some.inj run
  subst out
  have values := inputs (line e (s.regs 3)) (by simp)
  simpa only [E1M1LineFrame.result_eq,E1M1LineGeometry.result,copyInput,line] using values

def Image {total : Nat} (records : Fin total → Sides) (raw base : Word) (m : Memory) : Prop :=
  ∀ i, Source (records i) (E1M1LineScan.cursor raw 14 i.val) base m

def ImageLayout {total : Nat} (records : Fin total → Sides) (raw base output sp : Word) : Prop :=
  ∀ i j : Fin total, Separated (records i) (E1M1LineScan.cursor raw 14 i.val) base
    (E1M1LineScan.cursor output 62 j.val) sp

/-- Only later iterations must preserve an already-written cached pointer. -/
def OutputLayout (total : Nat) (output sp : Word) : Prop :=
  ∀ i j : Fin total, i.val<j.val → ∀ off∈[(46#32),50],
    E1M1LineFrame.Protected (E1M1LineScan.cursor output 62 i.val+off)
      (E1M1LineScan.cursor output 62 j.val) sp

def lines {total : Nat} (records : Fin total → Sides) (output : Word) : List OriginalGroupOutput.Line :=
  (List.finRange total).map (fun i => line (records i) (E1M1LineScan.cursor output 62 i.val))

theorem image_preserved {total : Nat} {records : Fin total → Sides}
    {raw base output sp : Word} {s : X86Memory.State} {f : Option Flags}
    (layout : E1M1LineScan.Layout total output sp)
    (ready : E1M1LineScan.Ready total raw output sp 0 s)
    (separate : ImageLayout records raw base output sp)
    (image : Image records raw base s.memory) (n : Nat) (bound : n≤total) :
    Image records raw base (E1M1LineScan.states s f n).core.memory := by
  intro i
  apply transport (image i)
  intro a ha
  have keep := E1M1LineScan.suffix_frame (total:=total) (raw:=raw) (line:=output) (sp:=sp) (s:=s) (f:=f)
    layout ready a 0 n (by omega) (by intro j _ hj; exact separate i ⟨j,by omega⟩ a ha)
  simpa only [Nat.zero_add,E1M1LineScan.states] using keep

theorem final_record {total : Nat} {records : Fin total → Sides}
    {raw base output sp : Word} {s : X86Memory.State} {f : Option Flags}
    (layout : E1M1LineScan.Layout total output sp)
    (ready : E1M1LineScan.Ready total raw output sp 0 s)
    (separate : ImageLayout records raw base output sp)
    (image : Image records raw base s.memory) (storage : OutputLayout total output sp) (i : Fin total) :
    load32 (E1M1LineScan.states s f total).core.memory (E1M1LineScan.cursor output 62 i.val+46)=(records i).front ∧
    load32 (E1M1LineScan.states s f total).core.memory (E1M1LineScan.cursor output 62 i.val+50)=(records i).back := by
  have current := (E1M1LineScan.states_ready (f:=f) layout ready i.val (by omega)).1
  have source := image_preserved (f:=f) layout ready separate image i.val (by omega) i
  have values := iteration_output (records i) base (E1M1LineScan.states s f i.val).core
    (by rw [current.source]; exact source)
    (by rw [current.source,current.output,current.stack]; exact separate i i)
  rw [current.output] at values
  have keep (off : Word) (mem : off∈[(46#32),50]) :
      load32 (E1M1LineScan.states s f total).core.memory (E1M1LineScan.cursor output 62 i.val+off)=
      load32 (E1M1LineScan.states s f (i.val+1)).core.memory (E1M1LineScan.cursor output 62 i.val+off) := by
    have h := E1M1LineScan.suffix_frame (total:=total) (raw:=raw) (line:=output) (sp:=sp) (s:=s) (f:=f)
      layout ready (E1M1LineScan.cursor output 62 i.val+off) (i.val+1) (total-(i.val+1)) (by omega)
      (by intro j lo hi; exact storage i ⟨j,by omega⟩ (by change i.val<j; omega) off mem)
    simpa only [Nat.add_sub_of_le (show i.val+1≤total by omega)] using h
  exact ⟨(keep 46 (by simp)).trans values.1,(keep 50 (by simp)).trans values.2⟩

/-- The exact input relation of the existing sector grouping theorem, for all
records simultaneously after the full loader loop. -/
theorem grouping_inputs {total : Nat} {records : Fin total → Sides}
    {raw base output sp : Word} {s : X86Memory.State} {f : Option Flags}
    (layout : E1M1LineScan.Layout total output sp)
    (ready : E1M1LineScan.Ready total raw output sp 0 s)
    (separate : ImageLayout records raw base output sp)
    (image : Image records raw base s.memory) (storage : OutputLayout total output sp) :
    OriginalGroupOutput.Inputs (lines records output) (E1M1LineScan.states s f total).core.memory := by
  intro e member
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp member
  exact final_record layout ready separate image storage i

def physicalSides (a : E1M1NoiseTopology.Addresses) (e : E1M1NoiseTopology.Line) : Sides :=
  ⟨e.frontIndex,e.backIndex,a.sector e.front,OriginalGroupLines.backAddress e a⟩

/-- The loader's ordered output list is exactly the relocated topology list used
by the existing grouping proof; only the actual address stride is required. -/
theorem physical_lines (es : List E1M1NoiseTopology.Line) (a : E1M1NoiseTopology.Addresses)
    (output : Word) (addresses : ∀ i : Fin es.length,
      a.line (es.get i).index=E1M1LineScan.cursor output 62 i.val) :
    lines (fun i => physicalSides a (es.get i)) output=es.map (E1M1GroupOutput.physical a) := by
  apply List.ext_getElem (by simp [lines])
  intro i h1 h2
  have hi : i<es.length := by simpa using h2
  have address := addresses ⟨i,hi⟩
  simpa [lines,List.get_eq_getElem,physicalSides,line,E1M1GroupOutput.physical] using
    address.symm

/-- Actual loader execution plus its grouping-input postcondition. Startup image
construction and instructions between cleanup and grouping remain separate. -/
theorem scan_to_grouping {total : Nat} {geometry : Fin total → E1M1LineSource.Record}
    {records : Fin total → Sides} {raw vertexBase sideBase output sp : Word}
    {s : X86Memory.State} {f : Option Flags}
    (layout : E1M1LineScan.Layout total output sp)
    (ready : E1M1LineScan.Ready total raw output sp 0 s)
    (verticesSafe : E1M1LineSource.ImageLayout geometry raw vertexBase output sp)
    (vertices : E1M1LineSource.Image geometry raw vertexBase s.memory)
    (good : ∀ i, E1M1LineSource.good (geometry i)=true)
    (sidesSafe : ImageLayout records raw sideBase output sp)
    (sides : Image records raw sideBase s.memory) (storage : OutputLayout total output sp)
    (positive : 0<total) :
    X86Routine.run program [0x2e3c1] (104*total) ⟨s,f,0x2e29a⟩=some (E1M1LineScan.states s f total) ∧
    (E1M1LineScan.states s f total).pc=0x2e3c1 ∧
    OriginalGroupOutput.Inputs (lines records output) (E1M1LineScan.states s f total).core.memory := by
  have run := E1M1LineSource.scan_from_image (f:=f) layout ready verticesSafe vertices good positive
  exact ⟨run.1,run.2.1,grouping_inputs layout ready sidesSafe sides storage⟩
end Doom.Proofs.E1M1LineOutput
