import Doom.Proofs.E1M1NoiseOpeningFrame
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1NoiseGraph
open Verification X86 X86Memory X86Control BlockSummary E1M1NoiseLedger E1M1NoiseMap
open E1M1NoiseFootprint E1M1NoisePreservation E1M1NoiseMapGuards

structure Edge where
  line : Word
  flags : BitVec 8
  frontIndex : BitVec 16
  backIndex : BitVec 16
  front : Word
  back : Word
  deriving DecidableEq, Repr

def Edge.two (e : Edge) : Prop := e.flags &&& (4#8) ≠ (0#8)
def sideAddress (base : Word) (index : BitVec 16) : Word := index.signExtend 32*(18#32)+base+(14#32)

def edgeReads (base : Word) (e : Edge) : List Word :=
  [e.line+(16#32),e.line+(22#32),e.line+(24#32),sideAddress base e.frontIndex,sideAddress base e.backIndex]
def graphReads (base : Word) (edges : List Edge) : List Word :=
  (0x2c118#32) :: edges.flatMap (edgeReads base)

/-- Side indices use the original signed 16-bit arithmetic. Back-sector data
is required only for two-sided lines; one-sided lines can retain index -1. -/
structure EdgeRep (base : Word) (e : Edge) (mem : Memory) : Prop where
  flags : mem (e.line+(16#32))=e.flags
  frontIndex : load16 mem (e.line+(22#32))=e.frontIndex
  backIndex : load16 mem (e.line+(24#32))=e.backIndex
  front : load32 mem (sideAddress base e.frontIndex)=e.front
  back : e.two → load32 mem (sideAddress base e.backIndex)=e.back

structure GraphRep (base : Word) (edges : List Edge) (mem : Memory) : Prop where
  pointer : load32 mem (0x2c118#32)=base
  edges : ∀ e∈edges, EdgeRep base e mem

def Covered (table : List SectorLines) (edges : List Edge) : Prop :=
  ∀ sector∈table, ∀ line∈sector.lines, ∃ e∈edges, e.line=line

def Closed (table : List SectorLines) (edges : List Edge) : Prop :=
  ∀ e∈edges, e.two → e.front∈layout table ∧ e.back∈layout table

theorem load16_of_word {before after : Memory} {address : Word}
    (h : load32 after address=load32 before address) : load16 after address=load16 before address := by
  have eq := congrArg (fun w : Word => w.extractLsb' 0 16) h
  simpa only [load32,load16,BitVec.extractLsb'_append_eq_right] using eq

theorem byte_of_word {before after : Memory} {address : Word}
    (h : load32 after address=load32 before address) : after address=before address := by
  have eq := congrArg (fun w : BitVec 16 => w.extractLsb' 0 8) (load16_of_word h)
  simpa only [load16,BitVec.extractLsb'_append_eq_right] using eq

theorem EdgeRep.frame {base e before after writes} (rep : EdgeRep base e before)
    (frame : PlayerHeight.Frame before after writes) (safe : Protect (edgeReads base e) writes) :
    EdgeRep base e after := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact (byte_of_word (frame _ (safe _ (by simp [edgeReads])))).trans rep.flags
  · exact (load16_of_word (frame _ (safe _ (by simp [edgeReads])))).trans rep.frontIndex
  · exact (load16_of_word (frame _ (safe _ (by simp [edgeReads])))).trans rep.backIndex
  · exact (frame _ (safe _ (by simp [edgeReads]))).trans rep.front
  · intro two
    exact (frame _ (safe _ (by simp [edgeReads]))).trans (rep.back two)

theorem GraphRep.frame {base edges before after writes} (rep : GraphRep base edges before)
    (frame : PlayerHeight.Frame before after writes) (safe : Protect (graphReads base edges) writes) :
    GraphRep base edges after := by
  refine ⟨(frame _ (safe _ (by simp [graphReads]))).trans rep.pointer,?_⟩
  intro e he
  exact (rep.edges e he).frame frame (fun a ha => safe a (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨e,he,ha⟩)))

theorem GraphRep.sector_step {base edges s} (rep : GraphRep base edges s.memory)
    (safe : Protect (graphReads base edges) (sectorWrites s)) :
    GraphRep base edges (E1M1NoiseAlert.sectorResult s).core.memory := rep.frame (sector_frame s) safe

theorem GraphRep.dispatch_step {base edges s} (rep : GraphRep base edges s.memory)
    (safe : Protect (graphReads base edges) (lineWrites s)) :
    GraphRep base edges (E1M1NoiseIteration.dispatched s).core.memory := rep.frame (dispatch_frame s) safe

theorem GraphRep.traversal {base edges phase s t w} (rep : GraphRep base edges s.core.memory)
    (trace : Trace phase s t w) (safe : Protect (graphReads base edges) w) :
    GraphRep base edges t.core.memory := rep.frame trace.frame safe

/-- Exact front/back selection, including the scratch store made before the
second signed index is read. No abstract graph step substitutes for the code. -/
theorem neighbor_choice {base e s} (rep : EdgeRep base e s.memory)
    (global : load32 s.memory (0x2c118#32)=base) (selected : s.regs 2=e.line) (two : e.two)
    (safe : Protect (edgeReads base e) [s.regs 4]) :
    (E1M1NoiseOpening.neighbor s).core.regs 0=if s.regs 3=e.front then e.back else e.front := by
  have frame : PlayerHeight.Frame s.memory (store32 s.memory (s.regs 4) base) [s.regs 4] := by
    intro a ha
    exact load_store_apart _ _ _ _ (ha _ (by simp))
  have after := rep.frame frame safe
  simp only [E1M1NoiseOpening.neighbor]
  have front := after.front
  have back := after.back two
  have index := after.backIndex
  simp only [sideAddress] at front back
  simp [NoiseOpening.neighborGate,NoiseOpening.neighborInputs,NoiseOpening.backNeighbor,
    NoiseOpening.frontNeighbor,put,write,selected,global,rep.frontIndex,front,index,back,load_store]
  split <;> simp_all [write]

theorem neighbor_closed {table base edges e s} (graph : GraphRep base edges s.memory)
    (closed : Closed table edges) (member : e∈edges) (selected : s.regs 2=e.line) (two : e.two)
    (safe : Protect (edgeReads base e) [s.regs 4]) :
    (E1M1NoiseOpening.neighbor s).core.regs 0∈layout table := by
  rw [neighbor_choice (graph.edges e member) graph.pointer selected two safe]
  split
  · exact (closed e member two).2
  · exact (closed e member two).1

/-- Coverage connects the cursor's actual selected pointer to its graph record. -/
theorem selected_edge {table edges sector s} (covered : Covered table edges)
    (member : sector∈table) (map : E1M1NoiseMap.Rep sector s.memory) (cursor : Cursor sector s) :
    ∃ e∈edges, (NoiseTraversal.lineGate s).core.regs 2=e.line := by
  obtain ⟨e,he,line⟩ := covered sector member _ (List.getElem_mem cursor.live)
  refine ⟨e,he,?_⟩
  change (NoiseTraversal.selected s).regs 2=e.line
  exact (cursor.selected map).trans line.symm

private theorem neighbor_count (s : X86Memory.State) : (E1M1NoiseOpening.neighbor s).core.regs 1=s.regs 1 := by
  simp only [E1M1NoiseOpening.neighbor]
  split <;> simp [NoiseOpening.neighborGate,NoiseOpening.neighborInputs,NoiseOpening.backNeighbor,
    NoiseOpening.frontNeighbor,put,write]

private theorem block_target (s : X86Memory.State) : (NoiseTraversal.blockResult s).core.regs 0=s.regs 0 := by
  simp only [NoiseTraversal.blockResult]
  split
  · simp [NoiseTraversal.recursiveCall,X86Routine.pushWord,put,write]
  · split <;> simp [NoiseTraversal.recursiveCall,X86Routine.pushWord,put,write]

private theorem block_count (s : X86Memory.State) (count : s.regs 1=0 ∨ s.regs 1=1)
    (call : (NoiseTraversal.blockResult s).pc=0x26f60) :
    (NoiseTraversal.blockResult s).core.regs 2=0 ∨ (NoiseTraversal.blockResult s).core.regs 2=1 := by
  simp only [NoiseTraversal.blockResult] at call ⊢
  split
  · simpa [NoiseTraversal.recursiveCall,X86Routine.pushWord,put,write] using count
  · split
    · simp [NoiseTraversal.recursiveCall,X86Routine.pushWord,put,write]
    · simp_all

private theorem edge_protection {base edges writes} (safe : Protect (graphReads base edges) writes)
    {e : Edge} (member : e∈edges) : Protect (edgeReads base e) writes := by
  intro a ha
  exact safe a (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨e,member,ha⟩))

/-- Opening, signed side lookup and the sound-block branch together produce a
represented child and a legal incoming count. Closed openings never enter it. -/
theorem opening_child {table base edges e s f} (graph : GraphRep base edges s.memory)
    (closed : Closed table edges) (member : e∈edges) (selected : s.regs 2=e.line) (two : e.two)
    (safe : Protect (graphReads base edges) (lineWrites s))
    (saved : E1M1NoiseOpeningFrame.CallerSafe s) (count : s.regs 1=0 ∨ s.regs 1=1)
    (call : (E1M1NoiseOpening.blockResult s f).pc=0x26f60) :
    (E1M1NoiseOpening.blockResult s f).core.regs 0∈layout table ∧
    ((E1M1NoiseOpening.blockResult s f).core.regs 2=0 ∨ (E1M1NoiseOpening.blockResult s f).core.regs 2=1) := by
  have opened := E1M1NoiseOpeningFrame.opened s f saved
  have after := graph.frame (opened_frame s f) safe
  by_cases pass : (NoiseTraversal.openingGate (E1M1NoiseOpening.opened s f).core).pc=0x26fc4
  · have neighborPC : (E1M1NoiseOpening.neighbor (E1M1NoiseOpening.opened s f).core).pc=0x26fee := by
      simp only [E1M1NoiseOpening.neighbor]
      split <;> rfl
    have dispatchEq : E1M1NoiseOpening.blockResult s f=
        NoiseTraversal.blockResult (E1M1NoiseOpening.neighbor (E1M1NoiseOpening.opened s f).core).core := by
      simp only [E1M1NoiseOpening.blockResult,E1M1NoiseOpening.lineResult,pass,ite_true]
      change (if (E1M1NoiseOpening.neighbor (E1M1NoiseOpening.opened s f).core).pc=0x26fee then _ else _)=_
      rw [if_pos neighborPC]
      rfl
    rw [dispatchEq] at call ⊢
    constructor
    · rw [block_target]
      apply neighbor_closed after closed member (opened.2.1.trans selected) two
      intro b hb c hc
      have eq : c=s.regs 4 := by simpa only [List.mem_singleton,opened_sp] using hc
      subst c
      exact edge_protection safe member b hb _ (by simp [lineWrites])
    · apply block_count _ _ call
      simpa only [neighbor_count,opened.1] using count
  · have pc : (NoiseTraversal.openingGate (E1M1NoiseOpening.opened s f).core).pc=0x27006 := by
      simp only [NoiseTraversal.openingGate] at pass ⊢
      split <;> simp_all
    have out : (E1M1NoiseOpening.blockResult s f).pc=0x27006 := by
      simp only [E1M1NoiseOpening.blockResult,E1M1NoiseOpening.lineResult,if_neg pass,pc,
        show (0x27006 : Nat)≠0x26fee by decide,show (0x27006 : Nat)≠0x26fc4 by decide,ite_false]
    omega

/-- The complete actual dispatch selects a covered line before performing the
lookup. A one-sided line cannot reach a recursive CALL. -/
theorem dispatch_child {table base edges sector s} (covered : Covered table edges)
    (closed : Closed table edges) (member : sector∈table)
    (map : E1M1NoiseMap.Rep sector s.memory) (cursor : Cursor sector s)
    (graph : GraphRep base edges s.memory)
    (safe : Protect (graphReads base edges) (lineWrites s))
    (saved : E1M1NoiseOpeningFrame.CallerSafe s) (count : s.regs 1=0 ∨ s.regs 1=1)
    (call : (E1M1NoiseIteration.dispatched s).pc=0x26f60) :
    (E1M1NoiseIteration.dispatched s).core.regs 0∈layout table ∧
    ((E1M1NoiseIteration.dispatched s).core.regs 2=0 ∨ (E1M1NoiseIteration.dispatched s).core.regs 2=1) := by
  obtain ⟨e,he,selected⟩ := selected_edge covered member map cursor
  have gateSP : (NoiseTraversal.lineGate s).core.regs 4=s.regs 4 := by
    simp [NoiseTraversal.lineGate,NoiseTraversal.selected,put,write]
  have gateCount : (NoiseTraversal.lineGate s).core.regs 1=s.regs 1 := by
    simp [NoiseTraversal.lineGate,NoiseTraversal.selected,put,write]
  have flag : NoiseTraversal.lineFlags (NoiseTraversal.selected s) (4#8)=e.flags &&& (4#8) := by
    change s.memory ((NoiseTraversal.lineGate s).core.regs 2+(16#32)) &&& (4#8)=_
    rw [selected,(graph.edges e he).flags]
  by_cases two : (NoiseTraversal.lineGate s).pc=0x26fb4
  · have etwo : e.two := by
      change (if NoiseTraversal.lineFlags (NoiseTraversal.selected s) (4#8)=(0#8) then 0x27006 else 0x26fb4)=0x26fb4 at two
      rw [flag] at two
      unfold Edge.two
      intro no
      simp only [no,ite_true] at two
      contradiction
    have cg : (E1M1NoiseOpening.blockResult (NoiseTraversal.lineGate s).core (NoiseTraversal.lineGate s).flags).pc=0x26f60 := by
      simpa only [E1M1NoiseIteration.dispatched,two,ite_true] using call
    have result := opening_child (table:=table) (base:=base) (edges:=edges) (e:=e)
      (s:=(NoiseTraversal.lineGate s).core) (f:=(NoiseTraversal.lineGate s).flags)
      graph closed he selected etwo (by simpa only [lineWrites,gateSP] using safe)
      (by simpa only [E1M1NoiseOpeningFrame.CallerSafe,gateSP] using saved)
      (by simpa only [gateCount] using count) cg
    simpa only [E1M1NoiseIteration.dispatched,two,ite_true] using result
  · have gateCall : (NoiseTraversal.lineGate s).pc=0x26f60 := by
      simpa only [E1M1NoiseIteration.dispatched,if_neg two] using call
    have ends := E1M1NoiseIteration.line_gate_pc s
    omega

/-- Feed graph closure directly into the existing checked child-entry contract.
Graph-word protection is still supplied; it must later follow from allocation
of the line and side tables. No child target or child count is assumed. -/
theorem child_entry {table stack base edges sector s n} (a : E1M1NoiseAllocation.Allocation table stack)
    (reserve : E1M1NoiseStack.Reserve stack .lines n s)
    (covered : Covered table edges) (closed : Closed table edges) (member : sector∈table)
    (map : MapRep table s.core.memory) (cursor : Cursor sector s.core)
    (graph : GraphRep base edges s.core.memory)
    (safe : Protect (graphReads base edges) (lineWrites s.core))
    (count : s.core.regs 1=0 ∨ s.core.regs 1=1) (call : (dispatch s).pc=0x26f60) :
    E1M1NoiseLedger.SectorSafe (layout table) (dispatch s).core ∧
    GraphRep base edges (dispatch s).core.memory ∧ MapRep table (dispatch s).core.memory := by
  have target := dispatch_child covered closed member (map sector member) cursor graph safe
    (E1M1NoiseOpeningFrame.allocation_safe a reserve.room) count call
  exact ⟨a.ledger_sector (reserve.child call).room target.1 target.2,
    graph.dispatch_step safe,map.dispatch_step (a.map_line reserve.room)⟩

end Doom.Proofs.E1M1NoiseGraph
