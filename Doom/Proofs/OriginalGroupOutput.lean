import Doom.Proofs.OriginalGroupFrame
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalGroupOutput
open Verification X86 X86Memory X86Control BlockSummary OriginalGroupStep OriginalGroupScan OriginalGroupFrame

structure Line where
  address : Word
  front : Word
  back : Word
  deriving DecidableEq, Repr

def chosen (sector : Word) (lines : List Line) : List Word :=
  (lines.filter fun e => OriginalGroupLines.accepts sector e.front e.back).map Line.address

def Linked : List Line → Word → Prop
  | [],_ => True
  | e::es,p => e.address=p ∧ Linked es (p+62)

def Inputs (lines : List Line) (m : Memory) : Prop :=
  ∀ e∈lines, load32 m (e.address+46)=e.front ∧ load32 m (e.address+50)=e.back

def Stored : List Word → Word → Memory → Prop
  | [],_,_ => True
  | v::vs,base,m => load32 m base=v ∧ Stored vs (base+4) m

structure SafeWord (a sp base : Word) (n : Nat) : Prop where
  stack : StackApart a sp
  output : ∀ j, j<n → Apart a (cursor base j)

/-- Finite separation for the words actually used in selection and output.
Vertex coordinates may alias other data; no geometric invariant is assumed. -/
structure Storage (lines : List Line) (sp base : Word) : Prop where
  outputs : ∀ j, j<lines.length → StackApart (cursor base j) sp
  distinct : ∀ i, i<lines.length → ∀ j, j<lines.length → i≠j → Apart (cursor base i) (cursor base j)
  fronts : ∀ e∈lines, SafeWord (e.address+46) sp base lines.length
  backs : ∀ e∈lines, SafeWord (e.address+50) sp base lines.length

theorem cursor_shift (base : Word) (j : Nat) : cursor (base+4) j=cursor base (j+1) := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [cursor,ih]

theorem safe_tail {a sp base n} (h : SafeWord a sp base (n+1)) : SafeWord a sp base n :=
  ⟨h.stack,fun j hj => h.output j (by omega)⟩
theorem safe_shift {a sp base n} (h : SafeWord a sp base (n+1)) : SafeWord a sp (base+4) n :=
  ⟨h.stack,fun j hj => by rw [cursor_shift]; exact h.output (j+1) (by omega)⟩

theorem storage_tail {e es sp base} (h : Storage (e::es) sp base) : Storage es sp base := by
  refine ⟨fun j hj => h.outputs j (by simpa using Nat.lt_succ_of_lt hj),?_,?_,?_⟩
  · intro i hi j hj ne; exact h.distinct i (by simpa using Nat.lt_succ_of_lt hi) j (by simpa using Nat.lt_succ_of_lt hj) ne
  · intro l hl; exact safe_tail (h.fronts l (by simp [hl]))
  · intro l hl; exact safe_tail (h.backs l (by simp [hl]))
theorem storage_shift {e es sp base} (h : Storage (e::es) sp base) : Storage es sp (base+4) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro j hj; rw [cursor_shift]; exact h.outputs (j+1) (by simpa using Nat.succ_lt_succ hj)
  · intro i hi j hj ne; rw [cursor_shift,cursor_shift]
    exact h.distinct (i+1) (by simpa using Nat.succ_lt_succ hi) (j+1) (by simpa using Nat.succ_lt_succ hj) (by omega)
  · intro l hl; exact safe_shift (h.fronts l (by simp [hl]))
  · intro l hl; exact safe_shift (h.backs l (by simp [hl]))

theorem inputs_step {e es sp base s} (h : Storage (e::es) sp base)
    (inputs : Inputs (e::es) s.memory) (stack : s.regs 4=sp) (output : s.regs 6=base) :
    Inputs es (body s).core.memory := by
  intro l hl
  have member : l∈e::es := by simp [hl]
  have front := h.fronts l member
  have back := h.backs l member
  have ff := iteration_frame s (l.address+46) (by rw [stack]; exact front.stack)
    (by rw [output]; exact front.output 0 (by simp))
  have bf := iteration_frame s (l.address+50) (by rw [stack]; exact back.stack)
    (by rw [output]; exact back.output 0 (by simp))
  exact ⟨ff.trans (inputs l member).1,bf.trans (inputs l member).2⟩

/-- Every emitted pointer is read back in original scan order, and every word
outside the finite write region is preserved. Both conclusions are derived
from execution of the body, including both bounding-box calls. -/
theorem output_and_frame (lines : List Line) (sp base sector : Word)
    (s : X86Memory.State) (storage : Storage lines sp base)
    (inputs : Inputs lines s.memory) (linked : Linked lines (s.regs 1))
    (stack : s.regs 4=sp) (output : s.regs 6=base) (owner : s.regs 5=sector) :
    Stored (chosen sector lines) base (after lines.length s).memory ∧
    (∀ a, SafeWord a sp base lines.length → load32 (after lines.length s).memory a=load32 s.memory a) := by
  induction lines generalizing s base with
  | nil => exact ⟨True.intro,fun _ _ => rfl⟩
  | cons e es ih =>
    obtain ⟨address,rest⟩ := linked
    obtain ⟨ri,rl,rs,rsp,rc⟩ := iteration_registers s
    have nextStack := rsp.trans stack
    have nextOwner := rs.trans owner
    have nextLinked : Linked es ((body s).core.regs 1) := by rw [rl]; exact rest
    have nextInputs := inputs_step storage inputs stack output
    have decision : hit s=OriginalGroupLines.accepts sector e.front e.back := by
      have data := inputs e (by simp)
      simp only [hit,OriginalGroupLines.front,OriginalGroupLines.back,owner,←address,data.1,data.2]
    cases yes : OriginalGroupLines.accepts sector e.front e.back
    · have no : hit s=false := decision.trans yes
      have nextOutput : (body s).core.regs 6=base := by simpa [no,output] using rc
      obtain ⟨stored,frame⟩ := ih base (body s).core (storage_tail storage) nextInputs nextLinked nextStack nextOutput nextOwner
      constructor
      · simpa [after,chosen,yes] using stored
      · intro a safe
        have one := iteration_frame s a (by rw [stack]; exact safe.stack)
          (by rw [output]; exact safe.output 0 (by simp))
        exact (frame a (safe_tail safe)).trans one
    · have hitYes : hit s=true := decision.trans yes
      have nextOutput : (body s).core.regs 6=base+4 := by simpa [hitYes,output] using rc
      obtain ⟨stored,frame⟩ := ih (base+4) (body s).core (storage_shift storage) nextInputs nextLinked nextStack nextOutput nextOwner
      have written : load32 (body s).core.memory base=e.address := by
        have wrote := iteration_written s hitYes (by rw [stack,output]; exact storage.outputs 0 (by simp))
        simpa [output,address] using wrote
      have protect : SafeWord base sp (base+4) es.length := by
        refine ⟨storage.outputs 0 (by simp),?_⟩
        intro j hj; rw [cursor_shift]
        exact storage.distinct 0 (by simp) (j+1) (by simpa using Nat.succ_lt_succ hj) (by omega)
      constructor
      · have kept := (frame base protect).trans written
        change Stored (chosen sector (e::es)) base (after es.length (body s).core).memory
        simpa [chosen,yes,Stored] using And.intro kept stored
      · intro a safe
        have one := iteration_frame s a (by rw [stack]; exact safe.stack)
          (by rw [output]; exact safe.output 0 (by simp))
        exact (frame a (safe_shift safe)).trans one

/-- The readback property now accompanies a successful original machine run. -/
theorem scan_output (lines : List Line) (sp base sector : Word) (s : X86Memory.State) (f : Option Flags)
    (layout : Layout lines.length sp base) (ready : Ready lines.length sp base 0 s)
    (storage : Storage lines sp base) (inputs : Inputs lines s.memory)
    (linked : Linked lines (s.regs 1)) (output : s.regs 6=base) (owner : s.regs 5=sector)
    (nonempty : 0<lines.length) :
    ∃ out, X86Routine.run program [0x2e6af] (43*lines.length) ⟨s,f,0x2e676⟩=some out ∧
      out.pc=0x2e6af ∧ Stored (chosen sector lines) base out.core.memory ∧
      (∀ a, SafeWord a sp base lines.length → load32 out.core.memory a=load32 s.memory a) := by
  obtain ⟨n,out,hn,path,done,final⟩ := scan_after lines.length lines.length sp base layout 0 s f ready (by simp) nonempty
  obtain ⟨stored,frame⟩ := output_and_frame lines sp base sector s storage inputs linked ready.stack output owner
  have stop : X86Routine.run program [0x2e6af] 0 out=some out := by simp [X86Routine.run,done]
  exact ⟨out,path.finish stop _ (by omega),done,by simpa [final] using stored,by simpa [final] using frame⟩


theorem cursor_eq (base : Word) (i : Nat) : cursor base i=base+BitVec.ofNat 32 (4*i) := by
  induction i with
  | zero => simp [cursor]
  | succ i ih => simp [cursor,ih,Nat.mul_add,BitVec.ofNat_add,BitVec.add_assoc]

theorem stored_get (xs : List Word) (base : Word) (m : Memory) (h : Stored xs base m)
    (i : Nat) (hi : i<xs.length) : load32 m (cursor base i)=xs[i] := by
  induction xs generalizing i base with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => exact h.1
    | succ i =>
      rw [←cursor_shift]
      exact ih (base+4) h.2 i (by simpa using hi)

theorem stored_rep (xs : List Word) (base sector : Word) (m : Memory)
    (stored : Stored xs base m)
    (count : load32 m (sector+78)=BitVec.ofNat 32 xs.length)
    (pointer : load32 m (sector+82)=base) : E1M1NoiseMap.Rep ⟨sector,base,xs⟩ m := by
  refine ⟨count,pointer,?_⟩
  intro i
  simpa only [cursor_eq,E1M1NoiseMap.entryAddress] using stored_get xs base m stored i.val i.isLt

theorem header_apart (sector : Word) : Apart (sector+78) (sector+82) := by
  have h := PlayerHeight.slots_apart (sector+78) 0 1 (by decide)
  change Apart (sector+78+(0#32)) (sector+78+(4#32)) at h
  simpa [BitVec.add_assoc] using h

/-- The pointer field and array entries are established by original stores.
The count field still comes from the earlier, separately required counting pass. -/
theorem entry_rep (lines : List Line) (s : X86Memory.State) (f : Option Flags)
    (layout : Layout lines.length (s.regs 4) (s.regs 6))
    (storage : Storage lines (s.regs 4) (s.regs 6))
    (inputs : Inputs lines s.memory)
    (linked : Linked lines (load32 s.memory 0x2c120))
    (count : (load32 s.memory 0x2c134).toNat=lines.length)
    (publishCount : Apart 0x2c134 (s.regs 5+82))
    (publishInputs : ∀ e∈lines, Apart (e.address+46) (s.regs 5+82) ∧ Apart (e.address+50) (s.regs 5+82))
    (countField : load32 s.memory (s.regs 5+78)=BitVec.ofNat 32 (chosen (s.regs 5) lines).length)
    (keepCount : SafeWord (s.regs 5+78) (s.regs 4) (s.regs 6) lines.length)
    (keepPointer : SafeWord (s.regs 5+82) (s.regs 4) (s.regs 6) lines.length)
    (nonempty : 0<lines.length) :
    ∃ out, X86Routine.run program [0x2e6af] (6+43*lines.length) ⟨s,f,0x2e661⟩=some out ∧
      out.pc=0x2e6af ∧ E1M1NoiseMap.Rep ⟨s.regs 5,s.regs 6,chosen (s.regs 5) lines⟩ out.core.memory := by
  let t := OriginalGroupLines.entry s
  have ready := entry_ready lines.length s count publishCount
  have inputNext : Inputs lines t.core.memory := by
    intro e he
    obtain ⟨fa,ba⟩ := publishInputs e he
    exact ⟨(load_store_apart _ _ _ _ fa).trans (inputs e he).1,
      (load_store_apart _ _ _ _ ba).trans (inputs e he).2⟩
  have linkedNext : Linked lines (t.core.regs 1) := by
    simpa [t,OriginalGroupLines.entry,OriginalGroupLines.prepared,put,write] using linked
  have outputNext : t.core.regs 6=s.regs 6 := by simp [t,OriginalGroupLines.entry,OriginalGroupLines.prepared,put,write]
  have ownerNext : t.core.regs 5=s.regs 5 := by simp [t,OriginalGroupLines.entry,OriginalGroupLines.prepared,put,write]
  obtain ⟨out,run,done,stored,frame⟩ := scan_output lines (s.regs 4) (s.regs 6) (s.regs 5) t.core t.flags
    layout ready storage inputNext linkedNext outputNext ownerNext nonempty
  have rep : E1M1NoiseMap.Rep ⟨s.regs 5,s.regs 6,chosen (s.regs 5) lines⟩ out.core.memory := by
    apply stored_rep _ _ _ _ stored
    · exact (frame _ keepCount).trans ((load_store_apart _ _ _ _ (header_apart (s.regs 5))).trans countField)
    · exact (frame _ keepPointer).trans (OriginalGroupLines.entry_pointer s)
  obtain ⟨n,hn,path,pc⟩ := X86Routine.run_path (OriginalGroupLines.entry_execution s f)
  have path := path.transfer program [0x2e6af] selection_agrees (by
    intro pc hp; simp only [List.mem_singleton]; intro eq; subst pc; exact hp (by decide))
  have signed : 0<(load32 s.memory (0x2c134#32)).toInt := by
    change (load32 s.memory (0x2c134#32)).toNat=lines.length at count
    rw [BitVec.toInt_eq_toNat_cond,count]
    have small := layout.small
    split <;> omega
  have loop : t.pc=0x2e676 := by
    have pos : ¬(load32 s.memory (0x2c134#32)).toInt≤0 := by omega
    simp [t,OriginalGroupLines.entry,pos]
  have eta : (⟨t.core,t.flags,0x2e676⟩ : X86Control.State)=t := by rw [←loop]
  rw [eta] at run
  exact ⟨out,path.finish run _ (by omega),done,rep⟩

end Doom.Proofs.OriginalGroupOutput
