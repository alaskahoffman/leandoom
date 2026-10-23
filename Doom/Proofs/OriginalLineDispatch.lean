import Doom.Proofs.E1M1LineCrossing
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.OriginalLineDispatch
open Verification X86 X86Memory X86Control BlockSummary
abbrev program := OriginalLineCrossing.program
abbrev selected (s : X86Memory.State) := (OriginalLineCell.duplicate (OriginalLineCell.header s).core)
def entry (s : X86Memory.State) := OriginalLineCell.callback (selected s).core (selected s).flags
/-- Callback ABI registers, with the initial list-header memory, before either write. -/
def view (s : X86Memory.State) : X86Memory.State := ⟨(entry s).core.regs,s.memory⟩
def pointer (s : X86Memory.State) : Word := OriginalLineCell.itemWord s*(62#32)+load32 s.memory (0x2c120#32)
def stamp (s : X86Memory.State) := pointer s+(54#32)
def Safe (s : X86Memory.State) (a : Word) : Prop :=
  Apart a (stamp s) ∧ Apart a (s.regs 4-(4#32))
def result (s : X86Memory.State) := OriginalLineCrossing.result (entry s).core

structure Fresh (s : X86Memory.State) : Prop where
  item : OriginalLineCell.itemWord s≠(0xffffffff#32)
  unseen : ¬OriginalLineCell.already (OriginalLineCell.header s).core
  target : load32 s.memory (s.regs 4)=(0x2c5f0#32)
  targetSafe : Apart (s.regs 4) (stamp s)
  stampSafe : Apart (stamp s) (s.regs 4-(4#32))

theorem selected_regs (s : X86Memory.State) :
    (selected s).core.regs 0=pointer s ∧ (selected s).core.regs 2=s.regs 2 ∧
    (selected s).core.regs 4=s.regs 4 ∧ (selected s).core.regs 7=load32 s.memory (0x13580#32) ∧
    (selected s).core.memory=s.memory := by
  simp [selected,OriginalLineCell.duplicate,OriginalLineCell.d4,OriginalLineCell.d3,OriginalLineCell.d2,
    OriginalLineCell.d1,OriginalLineCell.header,OriginalLineCell.h1,OriginalLineCell.lineAddress,
    OriginalLineCell.lineBase,OriginalLineCell.epoch,put,write,pointer]

theorem entry_regs (s : X86Memory.State) : (entry s).core.regs 0=pointer s ∧
    (entry s).core.regs 2=s.regs 2 ∧ (entry s).core.regs 4=s.regs 4-(4#32) := by
  have r := selected_regs s
  simpa [entry,OriginalLineCell.callback,X86Routine.pushWord,OriginalLineCell.marked,put,write] using
    And.intro r.1 (And.intro r.2.1 (congrArg (fun x : Word => x-(4#32)) r.2.2.1))

theorem entry_frame (s : X86Memory.State) (a : Word) (safe : Safe s a) :
    load32 (entry s).core.memory a=load32 s.memory a := by
  have r := selected_regs s
  exact (OriginalLineCell.callback_frame (selected s).core (selected s).flags a
    (by rw [r.1]; exact safe.1) (by rw [r.2.2.1]; exact safe.2)).trans (by rw [r.2.2.2.2])

theorem entry_observe (s : X86Memory.State) (h : Fresh s) :
    (entry s).pc=0x2c5f0 ∧
    load32 (entry s).core.memory ((entry s).core.regs 4)=(0x2c578#32) ∧
    load32 (entry s).core.memory (stamp s)=load32 s.memory (0x13580#32) := by
  have r := selected_regs s
  have k := OriginalLineCell.callback_observe (selected s).core (selected s).flags
    (by rw [r.2.2.1,r.1]; exact h.targetSafe) (by rw [r.1,r.2.2.1]; exact h.stampSafe)
  rw [r.1,r.2.2.1,r.2.2.2.1,r.2.2.2.2,h.target] at k
  exact ⟨k.2.2.2.2.2,by rw [(entry_regs s).2.2]; exact k.2.2.2.1,k.2.2.2.2.1⟩

theorem contains_cell (pc : Nat) (h : OriginalLineCell.program pc≠none) :
    program pc=OriginalLineCell.program pc := by
  have a := OriginalLineResume.contains_cell pc h
  have b : OriginalLineResume.program pc≠none := by rw [a]; exact h
  exact (E1M1LineResume.contains_resume pc b).trans a

theorem entry_execution (s : X86Memory.State) (f : Option Flags) (h : Fresh s) :
    ∃ n≤11, X86Routine.Prefix program [] n ⟨s,f,0x2c57f⟩ (entry s) := by
  obtain ⟨n,hn,a⟩ := OriginalLineCell.visit_execution s f
  refine ⟨n,hn,?_⟩
  simpa only [OriginalLineCell.visit,if_neg h.item,if_neg h.unseen,entry,selected] using
    a.transfer program [] contains_cell (by simp)

/-- Transport the entire crossing geometry from memory before stamping. -/
theorem crossing_inputs (s : X86Memory.State) (trace : Collision.Divline) (line : Collision.Line)
    (p v w : Word) (h : OriginalLineCrossing.Inputs (view s) trace line p v w)
    (safe : ∀ a∈OriginalLineSecondPoint.reads p v w, Safe s a) :
    OriginalLineCrossing.Inputs (entry s).core trace line p v w := by
  have keep (a : Word) (ha : a∈OriginalLineSecondPoint.reads p v w) := entry_frame s a (safe a ha)
  refine ⟨?_,?_,h.crosses⟩
  · refine ⟨h.entry.lineArg,?_,?_,?_,?_,?_,?_,?_,h.entry.safeReads⟩
    · rw [keep _ (by simp [OriginalLineSecondPoint.reads])]; exact h.entry.traceX
    · rw [keep _ (by simp [OriginalLineSecondPoint.reads])]; exact h.entry.traceY
    · rw [keep _ (by simp [OriginalLineSecondPoint.reads])]; exact h.entry.traceDX
    · rw [keep _ (by simp [OriginalLineSecondPoint.reads])]; exact h.entry.traceDY
    · rw [keep _ (by simp [OriginalLineSecondPoint.reads])]; exact h.entry.vertex
    · rw [keep _ (by simp [OriginalLineSecondPoint.reads])]; exact h.entry.vertexX
    · rw [keep _ (by simp [OriginalLineSecondPoint.reads])]; exact h.entry.vertexY
  · refine ⟨?_,?_,?_,?_,?_,h.data.safe⟩
    · rw [keep _ (by simp [OriginalLineSecondPoint.reads])]; exact h.data.vertex2
    · rw [keep _ (by simp [OriginalLineSecondPoint.reads])]; exact h.data.x2
    · rw [keep _ (by simp [OriginalLineSecondPoint.reads])]; exact h.data.y2
    · rw [keep _ (by simp [OriginalLineSecondPoint.reads])]; exact h.data.dx
    · rw [keep _ (by simp [OriginalLineSecondPoint.reads])]; exact h.data.dy

/-- All tail facts in pre-dispatch memory; the CALL return word is generated. -/
structure TailData (s : X86Memory.State) (trace : Collision.Divline) (line : Collision.Line)
    (frac : Fixed) (flags : Nat) (p v : Word) : Prop where
  computed : Collision.interceptVector trace ⟨line.x,line.y,line.dx,line.dy⟩=.ok frac
  geometrySafe : ∀ a∈OriginalLineFraction.reads p v, OriginalLineCrossing.ScratchSafe (view s) a
  active : load32 s.memory (0x2c024#32)≠0 ↔ flags &&& 4≠0
  back : load32 s.memory (p+(50#32))=0 ↔ line.back.isNone=true
  activeSafe : OriginalLineCrossing.SideSafe (view s) (0x2c024#32) ∧ OriginalLineCrossing.ScratchSafe (view s) (0x2c024#32)
  backSafe : OriginalLineCrossing.SideSafe (view s) (p+(50#32)) ∧ OriginalLineCrossing.ScratchSafe (view s) (p+(50#32))
  cursor : OriginalLineCrossing.SideSafe (view s) (0x2c028#32) ∧ OriginalLineCrossing.ScratchSafe (view s) (0x2c028#32)
  returnSafe : OriginalLineTail.RecordSafe (view s) ((view s).regs 4)
  dispatchSafe : ∀ a∈[(0x2c024#32),p+(50#32),0x2c028], Safe s a

theorem record_safe (s : X86Memory.State) (a : Word) (cursor : Safe s (0x2c028#32))
    (safe : OriginalLineTail.RecordSafe (view s) a) : OriginalLineTail.RecordSafe (entry s).core a := by
  have eq : OriginalLineFinish.cursor (entry s).core=OriginalLineFinish.cursor (view s) := entry_frame s _ cursor
  simpa only [OriginalLineTail.RecordSafe,eq] using safe

theorem tail_inputs (s : X86Memory.State) (trace : Collision.Divline) (line : Collision.Line)
    (frac : Fixed) (flags : Nat) (p v : Word) (fresh : Fresh s) (h : TailData s trace line frac flags p v) :
    OriginalLineCrossing.TailData (entry s).core trace line frac flags p v := by
  refine ⟨h.computed,h.geometrySafe,?_,?_,h.activeSafe,h.backSafe,h.cursor,(entry_observe s fresh).2.1,?_⟩
  · rw [entry_frame s _ (h.dispatchSafe _ (by simp))]; exact h.active
  · rw [entry_frame s _ (h.dispatchSafe _ (by simp))]; exact h.back
  · exact record_safe s _ (h.dispatchSafe _ (by simp)) h.returnSafe

structure Ready (s : X86Memory.State) (trace : Collision.Divline) (line : Collision.Line)
    (frac : Fixed) (flags : Nat) (p v w : Word) : Prop where
  fresh : Fresh s
  geometry : OriginalLineCrossing.Inputs (view s) trace line p v w
  geometrySafe : ∀ a∈OriginalLineSecondPoint.reads p v w, Safe s a
  tail : TailData s trace line frac flags p v

variable (s : X86Memory.State) (trace : Collision.Divline) (line : Collision.Line)
  (frac : Fixed) (flags : Nat) (p v w : Word) (h : Ready s trace line frac flags p v w)
include h

theorem execution (f : Option Flags) :
    ∃ n≤281, X86Routine.Prefix program [] n ⟨s,f,0x2c57f⟩ (result s) := by
  obtain ⟨n,hn,a⟩ := entry_execution s f h.fresh
  obtain ⟨m,hm,b⟩ := OriginalLineCrossing.execution (entry s).core trace line p v w
    (crossing_inputs s trace line p v w h.geometry h.geometrySafe) frac flags
    (tail_inputs s trace line frac flags p v h.fresh h.tail) (entry s).flags
  rw [OriginalPathXStep.at_pc _ _ (entry_observe s h.fresh).1] at b
  exact ⟨n+m,by omega,OriginalGroupBounds.prefix_join a b⟩

theorem continued (saved : OriginalLineTail.RecordSafe (view s) ((view s).regs 4-(12#32)))
    (keep : frac.raw<0 ∨ (flags &&& 4 != 0 && frac.raw<65536 && line.back.isNone)=false) :
    (result s).pc=0x2c57f ∧ (result s).core.regs 2=s.regs 2+(2#32) ∧ (result s).core.regs 4=s.regs 4 := by
  have k := OriginalLineCrossing.continued (entry s).core trace line p v w
    (crossing_inputs s trace line p v w h.geometry h.geometrySafe) frac flags
    (tail_inputs s trace line frac flags p v h.fresh h.tail)
    (record_safe s _ (h.tail.dispatchSafe _ (by simp)) saved) keep
  refine ⟨k.1,?_,?_⟩
  · rw [result,k.2.1,(entry_regs s).2.1]
  · rw [result,k.2.2,(entry_regs s).2.2]; bv_decide


/-- A protected word survives the callback, including its optional insertion. -/
theorem callback_frame (a : Word) (safe : OriginalLineCrossing.Protected (view s) a) :
    load32 (result s).core.memory a=load32 (entry s).core.memory a := by
  apply OriginalLineCrossing.frame (entry s).core trace line p v w
    (crossing_inputs s trace line p v w h.geometry h.geometrySafe) a
    (tail_inputs s trace line frac flags p v h.fresh h.tail).cursor
  exact ⟨safe.1,safe.2.1,record_safe s a (h.tail.dispatchSafe _ (by simp)) safe.2.2⟩

theorem frame (a : Word) (dispatch : Safe s a) (safe : OriginalLineCrossing.Protected (view s) a) :
    load32 (result s).core.memory a=load32 s.memory a :=
  (callback_frame s trace line frac flags p v w h a safe).trans (entry_frame s a dispatch)

/-- The new line is marked before the callback, and stays seen after it returns.
This is a derived stamp fact, not an assumed post-callback epoch equality. -/
theorem marked_seen
    (dispatch : ∀ a∈[s.regs 2,(0x13580#32),0x2c120], Safe s a)
    (safe : ∀ a∈OriginalLineTail.seenReads s.memory (s.regs 2), OriginalLineCrossing.Protected (view s) a) :
    OriginalLineResume.SeenAt (result s).core.memory (s.regs 2) := by
  have keep (a : Word) (ha : a∈[s.regs 2,(0x13580#32),0x2c120]) :=
    frame s trace line frac flags p v w h a (dispatch a ha) (safe a (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl <;> simp [OriginalLineTail.seenReads]))
  have half := congrArg (fun x : Word => x.extractLsb' 0 16) (keep (s.regs 2) (by simp))
  rw [SectorDispatch.load_half,SectorDispatch.load_half] at half
  have mark : load32 (result s).core.memory (stamp s)=load32 s.memory (0x13580#32) := by
    rw [callback_frame s trace line frac flags p v w h _ (safe _ (by
      simp [stamp,pointer,OriginalLineCell.itemWord,OriginalLineCell.item,OriginalLineTail.seenReads]))]
    exact (entry_observe s h.fresh).2.2
  unfold OriginalLineResume.SeenAt
  rw [half,keep (0x13580#32) (by simp),keep (0x2c120#32) (by simp)]
  refine ⟨?_,mark.symm⟩
  intro eq
  exact h.fresh.item ((OriginalLineCell.sentinel _).mpr eq)

end Doom.Proofs.OriginalLineDispatch
