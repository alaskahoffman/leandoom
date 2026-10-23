import Doom.Proofs.OriginalGroupCount
import Doom.Proofs.E1M1GroupOutput
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalGroupCountScan
open Verification X86 X86Memory X86Control BlockSummary OriginalGroupCount
open OriginalGroupOutput (Line Inputs Linked chosen)

/-- Only actual front and non-null back counters can be written. -/
def SafeWord (a : Word) (es : List Line) : Prop :=
  ∀ e∈es, Apart a (e.front+78) ∧ (e.back≠0 → Apart a (e.back+78))

/-- Static separation, independent of the evolving machine state. -/
structure Layout (es : List Line) : Prop where
  count : SafeWord 0x2c134 es
  fields : ∀ e∈es, SafeWord (e.address+46) es ∧ SafeWord (e.address+50) es

theorem safe_tail {a e es} (h : SafeWord a (e::es)) : SafeWord a es :=
  fun l hl => h l (by simp [hl])
theorem layout_tail {e es} (h : Layout (e::es)) : Layout es :=
  ⟨safe_tail h.count,fun l hl => ⟨safe_tail (h.fields l (by simp [hl])).1,
    safe_tail (h.fields l (by simp [hl])).2⟩⟩

theorem head_reads {e es s} (layout : Layout (e::es))
    (inputs : Inputs (e::es) s.memory) (linked : Linked (e::es) (s.regs 0)) :
    front s=e.front ∧ back s=e.back ∧ again s=e.front := by
  have address := linked.1
  have fs : front s=e.front := by rw [front,←address]; exact (inputs e (by simp)).1
  have hf : Apart (s.regs 0+46) (front s+78) := by
    rw [←address,fs]; exact ((layout.fields e (by simp)).1 e (by simp)).1
  have hb : Apart (s.regs 0+50) (front s+78) := by
    rw [←address,fs]; exact ((layout.fields e (by simp)).2 e (by simp)).1
  obtain ⟨af,bf⟩ := stable_pointers s hf hb
  exact ⟨fs,bf.trans (by rw [←address]; exact (inputs e (by simp)).2),af.trans fs⟩

theorem protected_head {a e es s} (layout : Layout (e::es))
    (inputs : Inputs (e::es) s.memory) (linked : Linked (e::es) (s.regs 0))
    (safe : SafeWord a (e::es)) : Protected a s := by
  obtain ⟨fr,ba,ag⟩ := head_reads layout inputs linked
  refine ⟨by rw [fr]; exact (safe e (by simp)).1,?_⟩
  intro yes
  have nz : e.back≠0 := by
    have both : back s≠0 ∧ back s≠again s := by simpa [second] using yes
    simpa only [ba] using both.1
  rw [ba]; exact (safe e (by simp)).2 nz

theorem inputs_step {e es s} (layout : Layout (e::es))
    (inputs : Inputs (e::es) s.memory) (linked : Linked (e::es) (s.regs 0)) :
    Inputs es (result s).core.memory := by
  have all := inputs_preserved s (e::es) inputs (fun l hl =>
    ⟨protected_head layout inputs linked (layout.fields l hl).1,
     protected_head layout inputs linked (layout.fields l hl).2⟩)
  exact fun l hl => all l (by simp [hl])

theorem linked_step {e es s} (linked : Linked (e::es) (s.regs 0)) :
    Linked es ((result s).core.regs 0) := by rw [(progress s).1]; exact linked.2

def after : List Line → X86Memory.State → X86Memory.State
  | [],s => s
  | _::es,s => after es (result s).core

def references : List Line → Nat
  | [] => 0
  | e::es => (if e.back != 0 && e.back != e.front then 2 else 1)+references es

/-- Every untouched word, including every cached input pointer, survives the loop. -/
theorem after_frame (es : List Line) (s : X86Memory.State) (a : Word)
    (layout : Layout es) (inputs : Inputs es s.memory) (linked : Linked es (s.regs 0))
    (safe : SafeWord a es) : load32 (after es s).memory a=load32 s.memory a := by
  induction es generalizing s with
  | nil => rfl
  | cons e es ih =>
    exact (ih (result s).core (layout_tail layout) (inputs_step layout inputs linked)
      (linked_step linked) (safe_tail safe)).trans
      (frame s a (protected_head layout inputs linked safe))

theorem after_inputs (es : List Line) (s : X86Memory.State)
    (layout : Layout es) (inputs : Inputs es s.memory) (linked : Linked es (s.regs 0)) :
    Inputs es (after es s).memory := by
  intro e he
  exact ⟨(after_frame es s _ layout inputs linked (layout.fields e he).1).trans (inputs e he).1,
    (after_frame es s _ layout inputs linked (layout.fields e he).2).trans (inputs e he).2⟩

/-- Disjoint physical counters for a queried non-null sector. -/
def CounterSafe (q : Word) (es : List Line) : Prop :=
  ∀ e∈es, (q≠e.front → Apart (q+78) (e.front+78)) ∧
    (q≠e.back → Apart (q+78) (e.back+78))

theorem head_sector {e es s q} (layout : Layout (e::es))
    (inputs : Inputs (e::es) s.memory) (linked : Linked (e::es) (s.regs 0))
    (nonzero : q≠(0#32)) (safe : CounterSafe q (e::es)) :
    load32 (result s).core.memory (q+78)=load32 s.memory (q+78)+
      (if OriginalGroupLines.accepts q e.front e.back then 1 else 0) := by
  obtain ⟨fr,ba,ag⟩ := head_reads layout inputs linked
  have address := linked.1
  have hf : Apart (s.regs 0+46) (front s+78) := by
    rw [←address,fr]; exact ((layout.fields e (by simp)).1 e (by simp)).1
  have hb : Apart (s.regs 0+50) (front s+78) := by
    rw [←address,fr]; exact ((layout.fields e (by simp)).2 e (by simp)).1
  have value := sector_count s q nonzero hf hb
    (by rw [fr]; exact (safe e (by simp)).1) (by rw [ba]; exact (safe e (by simp)).2)
  rw [fr,←address,(inputs e (by simp)).2] at value
  exact value

private theorem add_left_comm (a b c : Word) : a+(b+c)=b+(a+c) := by
  rw [←BitVec.add_assoc,BitVec.add_comm a b,BitVec.add_assoc]

theorem after_sector (es : List Line) (s : X86Memory.State) (q : Word)
    (layout : Layout es) (inputs : Inputs es s.memory) (linked : Linked es (s.regs 0))
    (nonzero : q≠(0#32)) (safe : CounterSafe q es) :
    load32 (after es s).memory (q+78)=load32 s.memory (q+78)+BitVec.ofNat 32 (chosen q es).length := by
  induction es generalizing s with
  | nil => simp [after,chosen]
  | cons e es ih =>
    have tail := ih (result s).core (layout_tail layout) (inputs_step layout inputs linked)
      (linked_step linked) (fun l hl => safe l (by simp [hl]))
    rw [after,tail,head_sector layout inputs linked nonzero safe]
    cases hit : OriginalGroupLines.accepts q e.front e.back <;>
      simp [chosen,List.filter,hit,BitVec.ofNat_add,BitVec.add_assoc,BitVec.add_comm,add_left_comm]

theorem after_total (es : List Line) (s : X86Memory.State)
    (layout : Layout es) (inputs : Inputs es s.memory) (linked : Linked es (s.regs 0)) :
    (after es s).regs 2=s.regs 2+BitVec.ofNat 32 (references es) := by
  induction es generalizing s with
  | nil => simp [after,references]
  | cons e es ih =>
    have tail := ih (result s).core (layout_tail layout) (inputs_step layout inputs linked) (linked_step linked)
    obtain ⟨fr,ba,ag⟩ := head_reads layout inputs linked
    rw [after,tail,(progress s).2.2.2]
    simp only [second,fr,ba,ag,references]
    cases yes : (e.back != 0 && e.back != e.front) <;>
      simp [yes,BitVec.ofNat_add,BitVec.add_assoc]



structure Ready (total : Nat) (es : List Line) (s : X86Memory.State) : Prop where
  index : (s.regs 6).toNat+es.length=total
  count : (load32 s.memory 0x2c134).toNat=total
  inputs : Inputs es s.memory
  linked : Linked es (s.regs 0)

theorem result_pc (s : X86Memory.State) :
    (result s).pc=(if (s.regs 6+1).toInt<(load32 (result s).core.memory 0x2c134).toInt then 0x2e602 else 0x2e62b) := by
  by_cases h : second s=true <;> simp [result,advanced,counted,h,put,write]

theorem ready_step {total e es s} (small : total<2147483648)
    (layout : Layout (e::es)) (ready : Ready total (e::es) s) :
    Ready total es (result s).core ∧ (result s).pc=(if es=[] then 0x2e62b else 0x2e602) := by
  have stable := frame s 0x2c134 (protected_head layout ready.inputs ready.linked layout.count)
  have index := ready.index
  simp only [List.length_cons] at index
  have next : (s.regs 6+1).toNat=(s.regs 6).toNat+1 := by
    simp only [BitVec.toNat_add]
    change ((s.regs 6).toNat+1)%4294967296=(s.regs 6).toNat+1
    omega
  have signedNext : (s.regs 6+1).toInt=((s.regs 6).toNat+1 : Nat) := by
    simp only [BitVec.toInt_eq_toNat_cond,next]
    split <;> omega
  have signedCount : (load32 s.memory 0x2c134).toInt=(total : Int) := by
    simp only [BitVec.toInt_eq_toNat_cond,ready.count]
    split <;> omega
  refine ⟨⟨?_,?_,inputs_step layout ready.inputs ready.linked,linked_step ready.linked⟩,?_⟩
  · rw [(progress s).2.1,next]; omega
  · rw [stable,ready.count]
  · rw [result_pc,stable,signedNext,signedCount]
    cases es with
    | nil => simp only [List.length_nil] at index; simp [index]
    | cons e es => simp only [List.length_cons] at index; simp [show ((s.regs 6).toNat+1 : Int)<total by omega]

private theorem active (pc : Nat) (h : program pc≠none) : pc∉[0x2e639] := by
  simp only [List.mem_singleton]
  intro eq; subst pc; exact h (by decide)

/-- Complete path through a nonempty suffix; static separation derives the
loop invariant and every branch, with no supplied trace or termination premise. -/
theorem scan_path (es : List Line) (total : Nat) (s : X86Memory.State) (f : Option Flags)
    (small : total<2147483648) (layout : Layout es) (ready : Ready total es s)
    (nonempty : es≠[]) :
    ∃ n out, n≤17*es.length ∧ X86Routine.Prefix program [0x2e639] n ⟨s,f,0x2e602⟩ out ∧
      out.pc=0x2e62b ∧ out.core=after es s := by
  induction es generalizing s f with
  | nil => contradiction
  | cons e es ih =>
    obtain ⟨n,hn,path⟩ := iteration_path s f
    have path := path.transfer program [0x2e639] (fun _ _ => rfl) active
    obtain ⟨next,pc⟩ := ready_step small layout ready
    by_cases last : es=[]
    · subst es
      exact ⟨n,result s,by simpa using hn,path,by simpa using pc,rfl⟩
    · have atLoop : (result s).pc=0x2e602 := by simpa [last] using pc
      obtain ⟨m,out,hm,tail,done,core⟩ := ih (result s).core (result s).flags (layout_tail layout) next last
      have eta : (⟨(result s).core,(result s).flags,0x2e602⟩ : X86Control.State)=result s := by rw [←atLoop]
      rw [eta] at tail
      exact ⟨n+m,out,by simp only [List.length_cons]; omega,
        OriginalGroupBounds.prefix_join path tail,done,core⟩

/-- Entry constructs the index/total registers itself. -/
theorem entry_ready (es : List Line) (s : X86Memory.State)
    (inputs : Inputs es s.memory) (linked : Linked es (load32 s.memory 0x2c120))
    (count : (load32 s.memory 0x2c134).toNat=es.length) : Ready es.length es (entry s).core := by
  refine ⟨?_,count,inputs,?_⟩
  · simp [entry,put,write]
  · simpa [entry,put,write] using linked

def final (es : List Line) (s : X86Memory.State) : X86Control.State :=
  allocation (after es (entry s).core)

/-- All counting instructions and allocation arguments compose without resetting
memory, registers or flags. The actual allocator CALL is the exit, not assumed. -/
theorem complete (es : List Line) (s : X86Memory.State) (f : Option Flags)
    (small : es.length<2147483648) (layout : Layout es)
    (inputs : Inputs es s.memory) (linked : Linked es (load32 s.memory 0x2c120))
    (count : (load32 s.memory 0x2c134).toNat=es.length) :
    X86Routine.run program [0x2e639] (9+17*es.length) ⟨s,f,0x2e5ef⟩=some (final es s) := by
  obtain ⟨n,hn,path,_⟩ := X86Routine.run_path (entry_execution s f)
  have path := path.transfer program [0x2e639] (fun _ _ => rfl) active
  change (load32 s.memory (0x2c134#32)).toNat=es.length at count
  have signed : (load32 s.memory (0x2c134#32)).toInt=(es.length : Int) := by
    simp only [BitVec.toInt_eq_toNat_cond,count]; split <;> omega
  by_cases empty : es=[]
  · subst es
    have pc : (entry s).pc=0x2e62b := by simp [entry,signed]
    have tail := allocation_execution (entry s).core (entry s).flags
    have eta : (⟨(entry s).core,(entry s).flags,0x2e62b⟩ : X86Control.State)=entry s := by rw [←pc]
    rw [eta] at tail
    exact path.finish tail _ (by simp; omega)
  · have positive : 0<es.length := List.length_pos_iff.mpr empty
    have pc : (entry s).pc=0x2e602 := by simp [entry,signed,empty]
    obtain ⟨m,out,hm,body,done,core⟩ := scan_path es es.length (entry s).core (entry s).flags
      small layout (entry_ready es s inputs linked count) empty
    have eta : (⟨(entry s).core,(entry s).flags,0x2e602⟩ : X86Control.State)=entry s := by rw [←pc]
    rw [eta] at body
    have tail := allocation_execution out.core out.flags
    have eta : (⟨out.core,out.flags,0x2e62b⟩ : X86Control.State)=out := by rw [←done]
    rw [eta,core] at tail
    exact (OriginalGroupBounds.prefix_join path body).finish tail _ (by omega)



theorem after_stack (es : List Line) (s : X86Memory.State) :
    (after es s).regs 4=s.regs 4 := by
  induction es generalizing s with
  | nil => rfl
  | cons e es ih => exact (ih (result s).core).trans (progress s).2.2.1

theorem final_stack (es : List Line) (s : X86Memory.State) :
    (final es s).core.regs 4=s.regs 4 := by
  simpa [final,allocation,put,write,entry] using after_stack es (entry s).core

theorem final_frame (es : List Line) (s : X86Memory.State) (a : Word)
    (layout : Layout es) (inputs : Inputs es s.memory) (linked : Linked es (load32 s.memory 0x2c120))
    (safe : SafeWord a es) : load32 (final es s).core.memory a=load32 s.memory a := by
  have start : Linked es ((entry s).core.regs 0) := by simpa [entry,put,write] using linked
  exact after_frame es (entry s).core a layout inputs start safe

theorem final_sector (es : List Line) (s : X86Memory.State) (q : Word)
    (layout : Layout es) (inputs : Inputs es s.memory) (linked : Linked es (load32 s.memory 0x2c120))
    (nonzero : q≠(0#32)) (safe : CounterSafe q es) :
    load32 (final es s).core.memory (q+78)=load32 s.memory (q+78)+BitVec.ofNat 32 (chosen q es).length := by
  have start : Linked es ((entry s).core.regs 0) := by simpa [entry,put,write] using linked
  exact after_sector es (entry s).core q layout inputs start nonzero safe

theorem final_inputs (es : List Line) (s : X86Memory.State)
    (layout : Layout es) (inputs : Inputs es s.memory) (linked : Linked es (load32 s.memory 0x2c120)) :
    Inputs es (final es s).core.memory := by
  have start : Linked es ((entry s).core.regs 0) := by simpa [entry,put,write] using linked
  exact after_inputs es (entry s).core layout inputs start

theorem final_arguments (es : List Line) (s : X86Memory.State)
    (layout : Layout es) (inputs : Inputs es s.memory) (linked : Linked es (load32 s.memory 0x2c120)) :
    (final es s).core.regs 0=(BitVec.ofNat 32 (references es) <<< 2) ∧
    (final es s).core.regs 2=50 ∧ (final es s).core.regs 3=0 ∧ (final es s).pc=0x2e639 := by
  have start : Linked es ((entry s).core.regs 0) := by simpa [entry,put,write] using linked
  have total := after_total es (entry s).core layout inputs start
  refine ⟨?_,by simp [final,allocation,put,write],by simp [final,allocation,put,write],rfl⟩
  change ((after es (entry s).core).regs 2 <<< 2)=_
  rw [total]
  simp [entry,put,write]

theorem final_global (es : List Line) (s : X86Memory.State)
    (layout : Layout es) (inputs : Inputs es s.memory) (linked : Linked es (load32 s.memory 0x2c120)) :
    load32 (final es s).core.memory 0x2c134=load32 s.memory 0x2c134 := by
  have start : Linked es ((entry s).core.regs 0) := by simpa [entry,put,write] using linked
  exact after_frame es (entry s).core _ layout inputs start layout.count

/-- Zero-initialized sector counters become exactly the lengths required by the
existing grouping proof. Initial zeros and physical storage remain premises. -/
theorem topology_counts (t : E1M1NoiseTopology.Topology) (a : E1M1NoiseTopology.Addresses)
    (s : X86Memory.State)
    (addresses : OriginalGroupLines.SectorAddresses a t.sectors.length)
    (ranges : ∀ e∈t.lines, OriginalGroupLines.InRange e t.sectors.length)
    (grouped : t.Grouped)
    (layout : Layout (t.lines.map (E1M1GroupOutput.physical a)))
    (inputs : Inputs (t.lines.map (E1M1GroupOutput.physical a)) s.memory)
    (linked : Linked (t.lines.map (E1M1GroupOutput.physical a)) (load32 s.memory 0x2c120))
    (zeros : ∀ i : Fin t.sectors.length, load32 s.memory (a.sector i.val+78)=0)
    (counters : ∀ i : Fin t.sectors.length, CounterSafe (a.sector i.val) (t.lines.map (E1M1GroupOutput.physical a))) :
    ∀ i : Fin t.sectors.length,
      load32 (final (t.lines.map (E1M1GroupOutput.physical a)) s).core.memory (a.sector i.val+78)=
        BitVec.ofNat 32 (t.sectors[i.val]).length := by
  intro i
  have value := final_sector _ s (a.sector i.val) layout inputs linked (addresses.nonzero i.val i.isLt) (counters i)
  rw [zeros i,E1M1GroupOutput.ordered_row t a addresses ranges grouped i,List.length_map] at value
  simpa using value



/-- Address-independent reference total, including self-referencing lines. -/
def logicalReferences : List E1M1NoiseTopology.Line → Nat
  | [] => 0
  | e::es => (if e.backIndex != 65535 && e.back != e.front then 2 else 1)+logicalReferences es

theorem physical_references (es : List E1M1NoiseTopology.Line) (a : E1M1NoiseTopology.Addresses)
    (n : Nat) (addresses : OriginalGroupLines.SectorAddresses a n)
    (ranges : ∀ e∈es, OriginalGroupLines.InRange e n) :
    references (es.map (E1M1GroupOutput.physical a))=logicalReferences es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    have range := ranges e (by simp)
    have tail := ih (fun l hl => ranges l (by simp [hl]))
    rw [List.map_cons,references,logicalReferences,tail]
    by_cases absent : e.backIndex=(65535#16)
    · simp [E1M1GroupOutput.physical,OriginalGroupLines.backAddress,absent]
    · have backRange := range.2 absent
      have nz : a.sector e.back≠(0#32) := addresses.nonzero e.back backRange
      have same : a.sector e.back=a.sector e.front ↔ e.back=e.front :=
        ⟨addresses.distinct e.back backRange e.front range.1,fun h => congrArg a.sector h⟩
      simp [E1M1GroupOutput.physical,OriginalGroupLines.backAddress,absent,nz,same]

end Doom.Proofs.OriginalGroupCountScan
