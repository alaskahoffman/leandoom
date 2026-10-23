import Doom.Proofs.E1M1LineScan
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1LineSource
open Verification X86 X86Memory X86Control BlockSummary E1M1LineIteration

/-- Raw signed 16-bit indices and already decoded fixed-point vertex words. -/
structure Record where
  first : BitVec 16
  second : BitVec 16
  x1 : Word
  y1 : Word
  x2 : Word
  y2 : Word
  deriving Inhabited

def address (base : Word) (index : BitVec 16) : Word := base+(index.signExtend 32 <<< 3)
def reads (e : Record) (raw base : Word) : List Word :=
  [0x2c138,raw,raw+2,address base e.first,address base e.first+4,
    address base e.second,address base e.second+4]
structure Source (e : Record) (raw base : Word) (m : Memory) : Prop where
  vertexBase : load32 m 0x2c138=base
  first : load16 m raw=e.first
  second : load16 m (raw+2)=e.second
  x1 : load32 m (address base e.first)=e.x1
  y1 : load32 m (address base e.first+4)=e.y1
  x2 : load32 m (address base e.second)=e.x2
  y2 : load32 m (address base e.second+4)=e.y2

def Separated (e : Record) (raw base line sp : Word) : Prop :=
  ∀ a∈reads e raw base, E1M1LineFrame.Protected a line sp

def good (e : Record) : Bool :=
  (e.x2-e.x1)==0 || (e.y2-e.y1)==0 ||
    (Fixed.divChecked ⟨Int32.ofBitVec (e.y2-e.y1)⟩ ⟨Int32.ofBitVec (e.x2-e.x1)⟩).isOk

theorem half_of_word {m n : Memory} {a : Word} (h : load32 m a=load32 n a) :
    load16 m a=load16 n a := by
  have h := congrArg (fun w : Word => w.extractLsb' 0 16) h
  simpa only [load32,BitVec.extractLsb'_append_eq_right,load16] using h

/-- Only the seven finite read locations are needed to transport this relation. -/
theorem transport {e raw base m n} (source : Source e raw base m)
    (same : ∀ a∈reads e raw base, load32 n a=load32 m a) : Source e raw base n := by
  exact ⟨(same _ (by simp [reads])).trans source.vertexBase,
    (half_of_word (same _ (by simp [reads]))).trans source.first,
    (half_of_word (same _ (by simp [reads]))).trans source.second,
    (same _ (by simp [reads])).trans source.x1,(same _ (by simp [reads])).trans source.y1,
    (same _ (by simp [reads])).trans source.x2,(same _ (by simp [reads])).trans source.y2⟩

theorem vertices_frame (s : X86Memory.State) (a : Word)
    (lo : Apart a (s.regs 3)) (hi : Apart a (s.regs 3+4)) :
    load32 (OriginalLineGeometry.vertices s).core.memory a=load32 s.memory a := by
  change load32 (store32 (store32 s.memory _ _) _ _) a=_
  rw [load_store_apart _ _ _ _ hi,load_store_apart _ _ _ _ lo]

/-- Exact WAD deltas after the real metadata/vertex/delta prefix. Every read
observes preceding writes; finite separation justifies recovering source values. -/
theorem prepared_deltas (e : Record) (base : Word) (s : X86Memory.State)
    (source : Source e (s.regs 1) base s.memory)
    (sep : Separated e (s.regs 1) base (s.regs 3) (s.regs 4)) :
    OriginalLineSetup.dx (E1M1LineSetup.prepared s).core=e.x2-e.x1 ∧
    OriginalLineSetup.dy (E1M1LineSetup.prepared s).core=e.y2-e.y1 := by
  let m := OriginalLineSetup.metadata s
  have afterMeta : Source e (s.regs 1) base m.memory := transport source (by
    intro a ha
    apply OriginalLineSetup.metadata_frame
    intro off mem
    exact (sep a ha).halves off (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at mem ⊢
      rcases mem with rfl|rfl|rfl <;> simp))
  have regs : m.regs 1=s.regs 1 ∧ m.regs 3=s.regs 3 := by simp [m]
  have pointers := OriginalLineGeometry.vertex_addresses m e.first e.second base
    (by rw [regs.1]; exact afterMeta.first) (by rw [regs.1]; exact afterMeta.second) afterMeta.vertexBase
    (by rw [regs.1,regs.2]; simpa using (sep _ (by simp [reads])).words 0 (by simp))
  let v := (OriginalLineGeometry.vertices m).core
  have vertices : Source e (s.regs 1) base v.memory := transport afterMeta (by
    intro a ha
    apply vertices_frame
    · rw [regs.2]; simpa using (sep a ha).words 0 (by simp)
    · rw [regs.2]; exact (sep a ha).words 4 (by simp))
  have v0 : v.regs 0=address base e.second := by
    simpa [v,OriginalLineGeometry.vertices,put,write,address] using pointers.2
  have v6 : v.regs 6=address base e.first := by
    simpa [v,OriginalLineGeometry.vertices,put,write,address] using pointers.1
  have v3 : v.regs 3=s.regs 3 := by simp [v,m,OriginalLineGeometry.vertices,put,write]
  have x : OriginalLineGeometry.dx v=e.x2-e.x1 := by
    rw [OriginalLineGeometry.dx,v0,v6,vertices.x2,vertices.x1]
  have afterX : Source e (s.regs 1) base (OriginalLineGeometry.xMemory v) := transport vertices (by
    intro a ha
    apply load_store_apart
    rw [v3]; exact (sep a ha).words 8 (by simp))
  have y : OriginalLineGeometry.dy v=e.y2-e.y1 := by
    rw [OriginalLineGeometry.dy,v0,v6,afterX.y2,afterX.y1]
  have fields := OriginalLineGeometry.prepared_fields m
  have line := E1M1LineFrame.prepared_reg s 3 (by simp)
  change load32 (E1M1LineSetup.prepared s).core.memory (_+8)=_ ∧
    load32 (E1M1LineSetup.prepared s).core.memory (_+12)=_
  rw [line]
  exact by simpa only [regs.2,E1M1LineSetup.prepared,m] using And.intro (fields.2.2.1.trans x) (fields.2.2.2.trans y)

/-- The division premise follows from source data, not from an assumed machine
execution or a supplied per-iteration success assertion. -/
theorem safe_of_source (e : Record) (base : Word) (s : X86Memory.State)
    (source : Source e (s.regs 1) base s.memory)
    (sep : Separated e (s.regs 1) base (s.regs 3) (s.regs 4))
    (ok : good e=true) : Safe s := by
  intro axis
  obtain ⟨dx,dy⟩ := prepared_deltas e base s source sep
  have x : OriginalLineSetup.dx (E1M1LineSetup.prepared s).core≠0 := fun h => axis (Or.inl h)
  have y : OriginalLineSetup.dy (E1M1LineSetup.prepared s).core≠0 := fun h => axis (Or.inr h)
  have call := OriginalLineSetup.diagonal_call (E1M1LineSetup.prepared s).core x y
  apply OriginalDivMemory.safe_of_fixed_success
  change (Fixed.divChecked ⟨Int32.ofBitVec ((OriginalLineSetup.selected (E1M1LineSetup.prepared s).core).core.regs 0)⟩
    ⟨Int32.ofBitVec ((OriginalLineSetup.selected (E1M1LineSetup.prepared s).core).core.regs 2)⟩).isOk=true
  rw [call.2.1,call.2.2.1,dx,dy]
  have nx : e.x2-e.x1≠(0#32) := by rwa [dx] at x
  have ny : e.y2-e.y1≠(0#32) := by rwa [dy] at y
  simpa [good,nx,ny] using ok

/-- Static separation of each record's source reads from every loader output.
These are finite address obligations, independent of evolving machine states. -/
def ImageLayout {total : Nat} (records : Fin total → Record) (raw base line sp : Word) : Prop :=
  ∀ i : Fin total, ∀ j : Fin total,
    Separated (records i) (E1M1LineScan.cursor raw 14 i.val) base
      (E1M1LineScan.cursor line 62 j.val) sp

def Image {total : Nat} (records : Fin total → Record) (raw base : Word) (m : Memory) : Prop :=
  ∀ i : Fin total, Source (records i) (E1M1LineScan.cursor raw 14 i.val) base m

/-- The initial memory relation survives every already-completed iteration. -/
theorem image_preserved {total : Nat} {records : Fin total → Record} {raw base line sp : Word} {s : X86Memory.State} {f : Option Flags}
    (layout : E1M1LineScan.Layout total line sp)
    (ready : E1M1LineScan.Ready total raw line sp 0 s)
    (separate : ImageLayout records raw base line sp)
    (image : Image records raw base s.memory) (n : Nat) (bound : n≤total) :
    Image records raw base (E1M1LineScan.states s f n).core.memory := by
  intro i
  apply transport (image i)
  intro a ha
  have keep := E1M1LineScan.suffix_frame (total:=total) (raw:=raw) (line:=line) (sp:=sp) (s:=s) (f:=f) layout ready a 0 n (by omega) (by
    intro j _ hj
    exact separate i ⟨j,by omega⟩ a ha)
  simpa only [Nat.zero_add,E1M1LineScan.states] using keep

/-- At every record, the machine prefix reads the exact initial WAD-coordinate
subtractions, with 32-bit wrap and signed index addressing preserved. -/
theorem iteration_deltas {total : Nat} {records : Fin total → Record}
    {raw base line sp : Word} {s : X86Memory.State} {f : Option Flags}
    (layout : E1M1LineScan.Layout total line sp)
    (ready : E1M1LineScan.Ready total raw line sp 0 s)
    (separate : ImageLayout records raw base line sp)
    (image : Image records raw base s.memory) (i : Fin total) :
    OriginalLineSetup.dx (E1M1LineSetup.prepared (E1M1LineScan.states s f i.val).core).core=
      (records i).x2-(records i).x1 ∧
    OriginalLineSetup.dy (E1M1LineSetup.prepared (E1M1LineScan.states s f i.val).core).core=
      (records i).y2-(records i).y1 := by
  have current := (E1M1LineScan.states_ready (f:=f) layout ready i.val (by omega)).1
  have source := image_preserved (f:=f) layout ready separate image i.val (by omega) i
  exact prepared_deltas (records i) base (E1M1LineScan.states s f i.val).core
    (by rw [current.source]; exact source)
    (by rw [current.source,current.output,current.stack]; exact separate i i)

/-- All diagonal arithmetic obligations are discharged from one initial image,
static storage separation, and finite successful-delta facts. -/
theorem arithmetic_of_image {total : Nat} {records : Fin total → Record} {raw base line sp : Word} {s : X86Memory.State} {f : Option Flags}
    (layout : E1M1LineScan.Layout total line sp)
    (ready : E1M1LineScan.Ready total raw line sp 0 s)
    (separate : ImageLayout records raw base line sp)
    (image : Image records raw base s.memory)
    (good : ∀ i, good (records i)=true) : E1M1LineScan.Arithmetic total s f := by
  intro i inside
  let idx : Fin total := ⟨i,inside⟩
  have current := (E1M1LineScan.states_ready (f:=f) layout ready i (by omega)).1
  have source := image_preserved (f:=f) layout ready separate image i (by omega) idx
  exact safe_of_source (records idx) base (E1M1LineScan.states s f i).core
    (by rw [current.source]; exact source)
    (by rw [current.source,current.output,current.stack]; exact separate idx idx)
    (good idx)

theorem scan_from_image {total : Nat} {records : Fin total → Record} {raw base line sp : Word} {s : X86Memory.State} {f : Option Flags}
    (layout : E1M1LineScan.Layout total line sp)
    (ready : E1M1LineScan.Ready total raw line sp 0 s)
    (separate : ImageLayout records raw base line sp)
    (image : Image records raw base s.memory)
    (good : ∀ i, good (records i)=true) (positive : 0<total) :
    X86Routine.run program [0x2e3c1] (104*total) ⟨s,f,0x2e29a⟩=
      some (E1M1LineScan.states s f total) ∧
    (E1M1LineScan.states s f total).pc=0x2e3c1 ∧
    E1M1LineScan.Ready total raw line sp total (E1M1LineScan.states s f total).core :=
  E1M1LineScan.scan_execution layout ready
    (arithmetic_of_image layout ready separate image good) positive
end Doom.Proofs.E1M1LineSource
