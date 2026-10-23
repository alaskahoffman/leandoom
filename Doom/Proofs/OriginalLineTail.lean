import Doom.Proofs.E1M1LineResume
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.OriginalLineTail
open Verification X86 X86Memory X86Control BlockSummary
abbrev program := E1M1LineResume.program
abbrev fraction := OriginalLineFraction.result

def stackOffsets : List Word := [0,4,8,12,-4,-8,-12,-16,-20,-24,-28,-32,-36,-40]
def StackSafe (s : X86Memory.State) (a : Word) : Prop :=
  ∀ off∈stackOffsets, Apart a (s.regs 4+off)
def RecordSafe (s : X86Memory.State) (a : Word) : Prop :=
  ∀ w∈[OriginalLineFinish.cursor s,OriginalLineFinish.cursor s+(4#32),OriginalLineFinish.cursor s+(8#32),(0x2c028#32)], Apart a w

def Protected (s : X86Memory.State) (a : Word) : Prop := StackSafe s a ∧ RecordSafe s a

/-- The setup's writes stay in four locals and the helper return word, even
when source addresses alias those locals. Their values need not be assumed. -/
theorem setup_frame (s : X86Memory.State) (a : Word) (safe : StackSafe s a) :
    load32 (OriginalLineFraction.setup s).memory a=load32 s.memory a := by
  have keep (m : Memory) (value off : Word) (ho : off∈stackOffsets) :=
    load_store_apart m (s.regs 4+off) a value (safe off ho)
  have k0 (m : Memory) (value : Word) := keep m value (0#32) (by simp [stackOffsets])
  simp only [BitVec.add_zero] at k0
  unfold OriginalLineFraction.setup OriginalLineFraction.step13
  simp only [X86Routine.pushWord]
  simp only [OriginalLineFraction.step12,OriginalLineFraction.step11,OriginalLineFraction.step10,
    OriginalLineFraction.step9,OriginalLineFraction.step8,OriginalLineFraction.step7,
    OriginalLineFraction.step6,OriginalLineFraction.step5,OriginalLineFraction.step4,
    OriginalLineFraction.step3,OriginalLineFraction.step2,OriginalLineFraction.step1,put,write]
  simp only [show (4 : Fin 8)≠0 by decide,show (4 : Fin 8)≠2 by decide,if_false]
  rw [load_store_apart _ _ _ _ (by simpa only [BitVec.sub_eq_add_neg] using safe (-(4#32)) (by simp [stackOffsets]))]
  rw [keep _ _ (12#32) (by simp [stackOffsets]),keep _ _ (8#32) (by simp [stackOffsets]),keep _ _ (4#32) (by simp [stackOffsets]),keep _ _ (0#32) (by simp [stackOffsets])]

theorem fraction_frame (s : X86Memory.State) (a : Word) (safe : StackSafe s a) :
    load32 (fraction s).core.memory a=load32 s.memory a := by
  have inner : ∀ off∈[(4#32),8,12,16,20,24,28,32,36], Apart a ((OriginalLineFraction.setup s).regs 4-off) := by
    intro off ho
    rw [(OriginalLineFraction.setup_regs s).2.2.1]
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
    rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe _ (by simp [stackOffsets])
  exact (OriginalInterceptVector.frame (OriginalLineFraction.setup s) a inner).trans (setup_frame s a safe)

theorem fraction_cursor (s : X86Memory.State) (safe : StackSafe s (0x2c028#32)) :
    OriginalLineFinish.cursor (fraction s).core=OriginalLineFinish.cursor s :=
  fraction_frame s _ safe

def finished (s : X86Memory.State) := OriginalLineFinish.result (fraction s).core
def result (s : X86Memory.State) := OriginalLineResume.result (finished s).core

/-- One boundary contract for the scratch footprint and the later record writes. -/
structure Layout (s : X86Memory.State) : Prop where
  cursor : StackSafe s (0x2c028#32)
  ret : Protected s (s.regs 4+(36#32))

theorem record_safe (s : X86Memory.State) (a : Word) (cursor : StackSafe s (0x2c028#32))
    (safe : RecordSafe s a) : RecordSafe (fraction s).core a := by
  simpa only [RecordSafe,fraction_cursor s cursor] using safe

theorem finished_frame (s : X86Memory.State) (a : Word) (cursor : StackSafe s (0x2c028#32))
    (safe : Protected s a) : load32 (finished s).core.memory a=load32 s.memory a :=
  (OriginalLineFinish.frame (fraction s).core a (record_safe s a cursor safe.2)).trans
    (fraction_frame s a safe.1)

theorem frame (s : X86Memory.State) (a : Word) (cursor : StackSafe s (0x2c028#32))
    (safe : Protected s a) : load32 (result s).core.memory a=load32 s.memory a := by
  rw [result,OriginalLineResume.memory]
  exact finished_frame s a cursor safe

theorem callback_return (s : X86Memory.State) (layout : Layout s)
    (ret : load32 s.memory (s.regs 4+(36#32))=(0x2c578#32)) :
    (finished s).pc=0x2c578 := by
  have safe : RecordSafe (fraction s).core ((fraction s).core.regs 4+(36#32)) := by
    rw [(OriginalLineFraction.returned s).2.1]
    exact record_safe s _ layout.cursor layout.ret.2
  have pc := OriginalLineFinish.returned (fraction s).core safe
  rw [(OriginalLineFraction.returned s).2.1,fraction_frame s _ layout.ret.1,ret] at pc
  exact pc

theorem contains_fraction (pc : Nat) (h : OriginalLineFraction.program pc≠none) :
    program pc=OriginalLineFraction.program pc := by
  have a := E1M1LineFraction.contains_fraction pc h
  have b : E1M1LineFraction.program pc≠none := by rw [a]; exact h
  exact (E1M1LineFinish.contains_prior pc b).trans a

theorem execution (s : X86Memory.State) (f : Option Flags)
    (arithmetic : OriginalInterceptVector.Safe (OriginalLineFraction.setup s))
    (layout : Layout s) (ret : load32 s.memory (s.regs 4+(36#32))=(0x2c578#32)) :
    ∃ n≤108, X86Routine.Prefix program [] n ⟨s,f,0x2c691⟩ (result s) := by
  obtain ⟨n,hn,a⟩ := OriginalLineFraction.execution s f arithmetic
  have a := a.transfer program [] contains_fraction (by simp)
  obtain ⟨m,hm,b⟩ := OriginalLineFinish.execution (fraction s).core (fraction s).flags
  rw [OriginalPathXStep.at_pc _ _ (OriginalLineFraction.returned s).1] at b
  have b := b.transfer program [] E1M1LineFinish.contains_finish (by simp)
  obtain ⟨k,hk,c⟩ := OriginalLineResume.execution (finished s).core (finished s).flags
  rw [OriginalPathXStep.at_pc _ _ (callback_return s layout ret)] at c
  have c := c.transfer program [] E1M1LineResume.contains_resume (by simp)
  exact ⟨n+m+k,by omega,OriginalGroupBounds.prefix_join (OriginalGroupBounds.prefix_join a b) c⟩

/-- Derive the finish inputs from geometry and global/backsector facts before
fraction evaluation, rather than re-assuming them after the helper returns. -/
theorem finish_inputs (s : X86Memory.State) (trace : Collision.Divline) (line : Collision.Line)
    (frac : Fixed) (flags : Nat) (p v : Word)
    (geometry : OriginalLineFraction.Inputs s trace line p v)
    (computed : Collision.interceptVector trace ⟨line.x,line.y,line.dx,line.dy⟩=.ok frac)
    (active : load32 s.memory (0x2c024#32)≠(0#32) ↔ flags &&& 4≠0)
    (back : load32 s.memory (p+(50#32))=(0#32) ↔ line.back.isNone=true)
    (activeSafe : StackSafe s (0x2c024#32)) (backSafe : StackSafe s (p+(50#32))) :
    OriginalLineFinish.Inputs (fraction s).core frac line flags p := by
  apply E1M1LineFinish.fraction_inputs s trace line frac flags p v geometry computed
  · rw [fraction_frame s _ activeSafe]; exact active
  · rw [fraction_frame s _ backSafe]; exact back

/-- Restore the saved cursor and advance it once, with all preservation supplied
before fraction evaluation. -/
theorem continued (s : X86Memory.State) (layout : Layout s) (list : Word)
    (saved : load32 s.memory (s.regs 4+(24#32))=list)
    (savedSafe : Protected s (s.regs 4+(24#32)))
    (nonzero : (finished s).core.regs 0≠(0#32)) :
    (result s).pc=0x2c57f ∧ (result s).core.regs 2=list+(2#32) ∧
    (result s).core.regs 4=s.regs 4+(40#32) := by
  have cursor := OriginalLineResume.finish_cursor (fraction s).core
  rw [(OriginalLineFraction.returned s).2.1] at cursor
  change (finished s).core.regs 2=load32 (finished s).core.memory _ at cursor
  rw [finished_frame s _ layout.cursor savedSafe,saved] at cursor
  have obs := OriginalLineResume.continued (finished s).core nonzero
  exact ⟨obs.1,by rw [result,obs.2.1,cursor],by rw [result,obs.2.2,finished,OriginalLineFinish.result_sp,(OriginalLineFraction.returned s).2.1]⟩

/-- Addresses needed to transport one existing valid-count/seen fact. -/
def seenReads (m : Memory) (p : Word) : List Word :=
  [p,0x13580,0x2c120,(load16 m p).signExtend 32*(62#32)+load32 m (0x2c120#32)+(54#32)]

theorem preserves_seen (s : X86Memory.State) (p : Word) (cursor : StackSafe s (0x2c028#32))
    (safe : ∀ a∈seenReads s.memory p, Protected s a) :
    OriginalLineResume.SeenAt (result s).core.memory p ↔ OriginalLineResume.SeenAt s.memory p := by
  have keep (a : Word) (ha : a∈seenReads s.memory p) := frame s a cursor (safe a ha)
  have half := congrArg (fun v : Word => v.extractLsb' 0 16) (keep p (by simp [seenReads]))
  rw [SectorDispatch.load_half,SectorDispatch.load_half] at half
  unfold OriginalLineResume.SeenAt
  rw [half,keep (0x13580#32) (by simp [seenReads]),keep (0x2c120#32) (by simp [seenReads]),keep _ (by simp [seenReads])]

/-- Existing records survive the arithmetic helper before a possible append. -/
theorem fraction_encodes (s : X86Memory.State) (base : Word) (resolve : Collision.Intercept → Word)
    (hits : Array Collision.Intercept) (encoded : OriginalLineFinish.Encodes s.memory base resolve hits)
    (safe : ∀ i<hits.size, ∀ off∈[(0#32),4,8], StackSafe s (base+BitVec.ofNat 32 (12*i)+off)) :
    OriginalLineFinish.Encodes (fraction s).core.memory base resolve hits := by
  intro i hi
  have keep (off : Word) (ho : off∈[(0#32),4,8]) := fraction_frame s (base+BitVec.ofNat 32 (12*i)+off) (safe i hi off ho)
  have old := encoded i hi
  unfold OriginalLineFinish.RecordAt at old ⊢
  rw [show load32 (fraction s).core.memory (base+BitVec.ofNat 32 (12*i))=load32 s.memory (base+BitVec.ofNat 32 (12*i)) by simpa using keep 0 (by simp),
    keep (4#32) (by simp),keep (8#32) (by simp)]
  exact old


structure Inputs (s : X86Memory.State) (trace : Collision.Divline) (line : Collision.Line)
    (frac : Fixed) (flags : Nat) (p v : Word) : Prop where
  geometry : OriginalLineFraction.Inputs s trace line p v
  computed : Collision.interceptVector trace ⟨line.x,line.y,line.dx,line.dy⟩=.ok frac
  active : load32 s.memory (0x2c024#32)≠(0#32) ↔ flags &&& 4≠0
  back : load32 s.memory (p+(50#32))=(0#32) ↔ line.back.isNone=true
  activeSafe : StackSafe s (0x2c024#32)
  backSafe : StackSafe s (p+(50#32))

theorem inputs (s : X86Memory.State) (trace : Collision.Divline) (line : Collision.Line)
    (frac : Fixed) (flags : Nat) (p v : Word) (h : Inputs s trace line frac flags p v) :
    OriginalLineFinish.Inputs (fraction s).core frac line flags p :=
  finish_inputs s trace line frac flags p v h.geometry h.computed h.active h.back h.activeSafe h.backSafe

theorem arithmetic (s : X86Memory.State) (trace : Collision.Divline) (line : Collision.Line)
    (frac : Fixed) (flags : Nat) (p v : Word) (h : Inputs s trace line frac flags p v) :
    OriginalInterceptVector.Safe (OriginalLineFraction.setup s) :=
  OriginalInterceptVector.safe_of_success _ trace _ _ _
    (OriginalLineFraction.encoded s trace line p v h.geometry) (by rw [h.computed]; rfl)

theorem live_value (s : X86Memory.State) (trace : Collision.Divline) (line : Collision.Line)
    (frac : Fixed) (flags : Nat) (p v : Word) (h : Inputs s trace line frac flags p v) :
    (finished s).core.regs 0=(if frac.raw<0 then (1#32)
      else if flags &&& 4 != 0 && frac.raw<65536 && line.back.isNone then 0 else 1) :=
  OriginalLineFinish.decision_live _ frac line flags p (inputs s trace line frac flags p v h)

theorem live_continued (s : X86Memory.State) (trace : Collision.Divline) (line : Collision.Line)
    (frac : Fixed) (flags : Nat) (p v list : Word) (h : Inputs s trace line frac flags p v)
    (layout : Layout s) (saved : load32 s.memory (s.regs 4+(24#32))=list)
    (savedSafe : Protected s (s.regs 4+(24#32)))
    (keepGoing : frac.raw<0 ∨ (flags &&& 4 != 0 && frac.raw<65536 && line.back.isNone)=false) :
    (result s).pc=0x2c57f ∧ (result s).core.regs 2=list+(2#32) ∧
    (result s).core.regs 4=s.regs 4+(40#32) := by
  apply continued s layout list saved savedSafe
  rw [live_value s trace line frac flags p v h]
  rcases keepGoing with negative|clear <;> simp [*]

/-- The actual production append, the represented ordered records, and the
next cursor all agree, using only pre-helper memory and separation facts. -/
theorem live_append (s : X86Memory.State) (trace : Collision.Divline) (line : Collision.Line)
    (frac : Fixed) (flags : Nat) (p v base : Word) (h : Inputs s trace line frac flags p v)
    (r : Collision.PathResult) (id : Nat) (resolve : Collision.Intercept → Word)
    (cursorSafe : StackSafe s (0x2c028#32))
    (nonnegative : ¬frac.raw<0) (clear : (flags &&& 4 != 0 && frac.raw<65536 && line.back.isNone)=false)
    (capacity : r.collected.size<128)
    (encoded : OriginalLineFinish.Encodes s.memory base resolve r.collected)
    (atEnd : OriginalLineFinish.cursor s=base+BitVec.ofNat 32 (12*r.collected.size))
    (pointer : resolve ⟨frac,true,id⟩=p)
    (newSafe : ∀ off∈[(0#32),4,8], Apart (OriginalLineFinish.cursor s+off) (0x2c028#32))
    (oldSafe : ∀ i<r.collected.size, ∀ off∈[(0#32),4,8], Protected s (base+BitVec.ofNat 32 (12*i)+off)) :
    Collision.appendIntercept r ⟨frac,true,id⟩=.ok {r with collected:=r.collected.push ⟨frac,true,id⟩} ∧
    OriginalLineFinish.Encodes (result s).core.memory base resolve (r.collected.push ⟨frac,true,id⟩) ∧
    load32 (result s).core.memory (0x2c028#32)=base+BitVec.ofNat 32 (12*(r.collected.size+1)) := by
  have hfinish := inputs s trace line frac flags p v h
  have enabled : OriginalLineFinish.inserts (fraction s).core := by
    constructor
    · simpa [hfinish.fraction,Int32.toInt_toBitVec,Int32.lt_iff_toInt_lt] using nonnegative
    · rw [OriginalLineFinish.early_live _ frac line flags p hfinish,clear]; decide
  refine ⟨OriginalLineFinish.append_live r _ capacity,?_,?_⟩
  · rw [result,OriginalLineResume.memory]
    apply OriginalLineFinish.append_encoded (fraction s).core base resolve r.collected ⟨frac,true,id⟩ enabled
    · exact fraction_encodes s base resolve r.collected encoded (fun i hi off ho => (oldSafe i hi off ho).1)
    · rw [fraction_cursor s cursorSafe]; exact atEnd
    · exact hfinish.fraction
    · rfl
    · exact hfinish.pointer.trans pointer.symm
    · simpa only [fraction_cursor s cursorSafe] using newSafe
    · intro i hi off ho
      exact record_safe s _ cursorSafe (oldSafe i hi off ho).2
  · rw [result,OriginalLineResume.memory,finished,OriginalLineFinish.result_memory,if_pos enabled,
      OriginalLineFinish.written_cursor,fraction_cursor s cursorSafe,atEnd]
    simp [Nat.mul_add,BitVec.ofNat_add,BitVec.add_assoc]

/-- Protected previously-visited entries remain available to the iterator's
existing finite-run theorem after this fresh intersection. -/
theorem following_duplicates (s : X86Memory.State) (n : Nat) (list : Word)
    (cursorSafe : StackSafe s (0x2c028#32))
    (next : (result s).core.regs 2=list+(2#32))
    (window : ∀ i<n, OriginalLineResume.SeenAt s.memory (list+BitVec.ofNat 32 (2*(i+1))))
    (safe : ∀ i<n, ∀ a∈seenReads s.memory (list+BitVec.ofNat 32 (2*(i+1))), Protected s a) :
    OriginalLineResume.Duplicates n (result s) := by
  apply OriginalLineResume.duplicates_from_memory
  intro i hi
  rw [next]
  have address : list+(2#32)+BitVec.ofNat 32 (2*i)=list+BitVec.ofNat 32 (2*(i+1)) := by
    simp only [Nat.mul_add,BitVec.ofNat_add]; bv_decide
  rw [address]
  exact (preserves_seen s _ cursorSafe (safe i hi)).mpr (window i hi)


/-- A crossing line's arithmetic, optional insertion, actual callback return,
following duplicate suffix and sentinel compose from one pre-helper boundary. -/
theorem through_sentinel (s : X86Memory.State) (f : Option Flags)
    (trace : Collision.Divline) (line : Collision.Line) (frac : Fixed) (flags : Nat) (p v list : Word)
    (h : Inputs s trace line frac flags p v) (layout : Layout s)
    (ret : load32 s.memory (s.regs 4+(36#32))=(0x2c578#32))
    (saved : load32 s.memory (s.regs 4+(24#32))=list) (savedSafe : Protected s (s.regs 4+(24#32)))
    (keepGoing : frac.raw<0 ∨ (flags &&& 4 != 0 && frac.raw<65536 && line.back.isNone)=false)
    (count : Nat)
    (window : ∀ i<count, OriginalLineResume.SeenAt s.memory (list+BitVec.ofNat 32 (2*(i+1))))
    (windowSafe : ∀ i<count, ∀ a∈seenReads s.memory (list+BitVec.ofNat 32 (2*(i+1))), Protected s a)
    (last : load16 s.memory (list+BitVec.ofNat 32 (2*(count+1)))=(0xffff#16))
    (lastSafe : Protected s (list+BitVec.ofNat 32 (2*(count+1)))) :
    ∃ steps≤115+10*count, X86Routine.Prefix program [] steps ⟨s,f,0x2c691⟩
      (OriginalLineBounds.returned (OriginalLineCell.header (OriginalLineResume.skipMany count (result s)).core).core) := by
  obtain ⟨n,hn,head⟩ := execution s f (arithmetic s trace line frac flags p v h) layout ret
  have next := live_continued s trace line frac flags p v list h layout saved savedSafe keepGoing
  have seen := following_duplicates s count list layout.cursor next.2.1 window windowSafe
  obtain ⟨m,hm,skips⟩ := OriginalLineResume.skip_execution count (result s) next.1 seen
  have skips := skips.transfer program [] E1M1LineResume.contains_resume (by simp)
  have half := congrArg (fun v : Word => v.extractLsb' 0 16) (frame s _ layout.cursor lastSafe)
  rw [SectorDispatch.load_half,SectorDispatch.load_half] at half
  have lastNow : OriginalLineCell.item (OriginalLineResume.skipMany count (result s)).core=(0xffff#16) := by
    rw [OriginalLineResume.next_item count (result s) seen,next.2.1]
    have addr : list+(2#32)+BitVec.ofNat 32 (2*count)=list+BitVec.ofNat 32 (2*(count+1)) := by
      simp only [Nat.mul_add,BitVec.ofNat_add]; bv_decide
    rw [addr,half,last]
  have tail := OriginalLineResume.sentinel_execution
    (OriginalLineResume.skipMany count (result s)).core
    (OriginalLineResume.skipMany count (result s)).flags lastNow
  rw [OriginalPathXStep.at_pc _ _ (OriginalLineResume.skip_pc count (result s) next.1 seen)] at tail
  have tail := tail.transfer program [] E1M1LineResume.contains_resume (by simp)
  exact ⟨n+m+7,by omega,OriginalGroupBounds.prefix_join (OriginalGroupBounds.prefix_join head skips) tail⟩

end Doom.Proofs.OriginalLineTail
