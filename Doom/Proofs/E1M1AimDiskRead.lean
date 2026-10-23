import Doom.Proofs.E1M1AimReadPrologue
/-! Actual I_BeginRead gate. Nonzero video flag reaches the hardware arm, never
an invented return. Zero flag executes all three POPs and RET. Earlier video
initialization and the active VGA IN/OUT/latch semantics remain open. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1AimDiskRead
open Verification X86 X86Memory X86Control BlockSummary
open OriginalGroupHeap (Separated)
def program := E1M1AimReadPrologue.program
abbrev op := E1M1AimWordFill.op
def listed : X86WordFillRoutine.Program
  | 0x1adb0 => some (op (.push 3),1)
  | 0x1adb1 => some (op (.push 1),1)
  | 0x1adb2 => some (op (.push 2),1)
  | 0x1adb3 => some (op (.control (.cmpImmediate ⟨none,none,0,0x29134⟩ 0)),7)
  | 0x1adba => some (op (.control (.jumpZero true 220)),6)
  | 0x1ae9c => some (op (.pop 2),1)
  | 0x1ae9d => some (op (.pop 1),1)
  | 0x1ae9e => some (op (.pop 3),1)
  | 0x1ae9f => some (op .ret,1)
  | _ => none
theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def writes (s : X86Memory.State) : List (Word × Word) :=
  [(s.regs 4-4,s.regs 3),(s.regs 4-8,s.regs 1),(s.regs 4-12,s.regs 2)]
def saved (s : X86Memory.State) := X86Routine.pushWord
  (X86Routine.pushWord (X86Routine.pushWord s (s.regs 3)) (s.regs 1)) (s.regs 2)
def Safe (s : X86Memory.State) (a : Word) : Prop := ∀ w∈writes s, Apart a w.1
def gate (s : X86Memory.State) (value : Word) : X86WordFillRoutine.State :=
  ⟨saved s,.legacy (some (compare32 value 0)),if value=0 then 0x1ae9c else 0x1adc0⟩
def returned (s : X86Memory.State) : X86WordFillRoutine.State :=
  ⟨{put s 4 (s.regs 4+4) with memory:=(saved s).memory},
   .legacy (some (compare32 0 0)),(load32 s.memory (s.regs 4)).toNat⟩
theorem saved_memory (s : X86Memory.State) : (saved s).memory=HeapWrites.apply (writes s) s.memory := by
  simp [saved,writes,HeapWrites.apply,X86Routine.pushWord,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc]
theorem saved_frame (s : X86Memory.State) (a : Word) (safe : Safe s a) :
    load32 (saved s).memory a=load32 s.memory a := by
  rw [saved_memory]; exact HeapWrites.frame _ _ _ safe

theorem gate_execution (s : X86Memory.State) (f : Option Flags) (value : Word)
    (flag : load32 s.memory 0x29134=value) (safe : Safe s 0x29134) :
    X86WordFillRoutine.Prefix program [] 5 (X86WordFillRoutine.embed ⟨s,f,0x1adb0⟩) (gate s value) := by
  have v := (saved_frame s _ safe).trans flag
  simp only [BitVec.ofNat_eq_ofNat] at v
  have path : X86WordFillRoutine.Prefix listed [] 5 (X86WordFillRoutine.embed ⟨s,f,0x1adb0⟩) (gate s value) := by
    refine .step (by simp [X86WordFillRoutine.embed]) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (middle:=⟨saved s,.legacy (some (compare32 value 0)),0x1adba⟩) (by simp) rfl ?_ ?_
    · simp [X86WordFillRoutine.execute,X86WordFillRoutine.embed,X86FillRoutine.execute,
        X86StartupRoutine.execute,X86ByteRoutine.execute,X86Routine.execute,X86Control.execute,
        X86Block.Address.eval,v,saved,X86Routine.pushWord,put,write] at v ⊢
      exact congrArg (compare32 · 0) v
    refine .step (middle:=gate s value) (by simp) rfl ?_ (.nil _)
    by_cases h : value=0#32 <;>
      simp [gate,X86WordFillRoutine.execute,X86WordFillRoutine.embed,X86FillRoutine.execute,
        X86StartupRoutine.execute,X86ByteRoutine.execute,X86Routine.execute,X86Control.execute,compare32,h]
  exact path.transfer _ [] decoded (by simp)

theorem saved_words (s : X86Memory.State) :
    load32 (saved s).memory (s.regs 4-12)=s.regs 2 ∧
    load32 (saved s).memory (s.regs 4-8)=s.regs 1 ∧
    load32 (saved s).memory (s.regs 4-4)=s.regs 3 ∧
    load32 (saved s).memory (s.regs 4)=load32 s.memory (s.regs 4) := by
  have sep (a b : Fin 8) (h : a≠b) :
      Apart (s.regs 4-12+BitVec.ofNat 32 (4*a.val)) (s.regs 4-12+BitVec.ofNat 32 (4*b.val)) :=
    PlayerHeight.slots_apart _ a b h
  have h10 := sep 1 0 (by decide)
  have h20 := sep 2 0 (by decide)
  have h21 := sep 2 1 (by decide)
  have h30 := sep 3 0 (by decide)
  have h31 := sep 3 1 (by decide)
  have h32 := sep 3 2 (by decide)
  change Apart (s.regs 4-12+12) (s.regs 4-12+0) at h30
  change Apart (s.regs 4-12+12) (s.regs 4-12+4) at h31
  change Apart (s.regs 4-12+12) (s.regs 4-12+8) at h32
  simp [BitVec.sub_eq_add_neg,BitVec.add_assoc] at h10 h20 h21 h30 h31 h32
  simp [saved,X86Routine.pushWord,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,
    load_store_apart _ _ _ _ h10,load_store_apart _ _ _ _ h20,load_store_apart _ _ _ _ h21,
    load_store_apart _ _ _ _ h30,load_store_apart _ _ _ _ h31,load_store_apart _ _ _ _ h32,load_store]

theorem disabled_return (s : X86Memory.State) :
    X86WordFillRoutine.Prefix program [] 4 (gate s 0) (returned s) := by
  have w := saved_words s
  simp only [BitVec.sub_eq_add_neg,BitVec.ofNat_eq_ofNat,BitVec.reduceNeg] at w
  have path : X86WordFillRoutine.Prefix listed [] 4 (gate s 0) (returned s) := by
    refine .step (by simp [gate]) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (middle:=returned s) (by simp) rfl ?_ (.nil _)
    simp [gate,returned,X86WordFillRoutine.execute,X86WordFillRoutine.embed,
      X86FillRoutine.execute,X86StartupRoutine.execute,X86ByteRoutine.execute,X86Routine.execute,
      put,write,show (saved s).regs 4=s.regs 4-12 by simp [saved,X86Routine.pushWord,put,write,
        BitVec.sub_eq_add_neg,BitVec.add_assoc],BitVec.sub_eq_add_neg,BitVec.add_assoc,w]
    funext r
    by_cases h4 : r=4 <;> by_cases h2 : r=2 <;> by_cases h1 : r=1 <;> by_cases h3 : r=3 <;>
      simp [saved,X86Routine.pushWord,put,write,h4,h2,h1,h3]
  exact path.transfer _ [] decoded (by simp)

def result (s : X86Memory.State) (value : Word) := if value=0 then returned s else gate s value
theorem execution (s : X86Memory.State) (f : Option Flags) (value : Word)
    (flag : load32 s.memory 0x29134=value) (safe : Safe s 0x29134) :
    ∃ n≤9, X86WordFillRoutine.Prefix program [] n
      (X86WordFillRoutine.embed ⟨s,f,0x1adb0⟩) (result s value) := by
  have lead := gate_execution s f value flag safe
  by_cases h : value=0#32
  · rw [h] at lead ⊢
    exact ⟨9,by omega,by simpa [result] using lead.trans (disabled_return s)⟩
  · exact ⟨5,by omega,by simpa [result,h] using lead⟩
theorem result_memory (s : X86Memory.State) (value : Word) :
    (result s value).core.memory=HeapWrites.apply (writes s) s.memory := by
  by_cases h : value=0#32 <;> simp [result,h,returned,gate,saved_memory]
theorem result_registers (s : X86Memory.State) (value : Word) (r : Reg) (notSP : r≠4) :
    (result s value).core.regs r=s.regs r := by
  by_cases h : value=0#32 <;> simp [result,h,returned,gate,saved,X86Routine.pushWord,put,write,notSP]
theorem result_observations (s : X86Memory.State) (value : Word) :
    (result s value).pc=(if value=0 then (load32 s.memory (s.regs 4)).toNat else 0x1adc0) ∧
    (result s value).core.regs 4=(if value=0 then s.regs 4+4 else s.regs 4-12) := by
  by_cases h : value=0#32 <;> simp [result,h,returned,gate,saved,X86Routine.pushWord,put,write,
    BitVec.sub_eq_add_neg,BitVec.add_assoc]

def stackAddresses (s : X86Memory.State) : List Word := [s.regs 4-84,s.regs 4-88,s.regs 4-92]
structure Conditions (s : X86Memory.State) (v : OriginalGroupHeap.View)
    (cache nextSize nextNext : Word) : Prop where
  original : E1M1AimReadPrologue.OriginalSafe s v cache nextSize nextNext 0x29134
  prologue : Separated 0x29134 (E1M1AimReadPrologue.stackAddresses s)
  stack : Separated 0x29134 (stackAddresses s)
def boundary (s : X86Memory.State) (h : Nat) (table cache : Word) :=
  result (E1M1AimReadPrologue.entered s h table cache).core (load32 s.memory 0x29134)
theorem stack_writes (s t : X86Memory.State) (sp : t.regs 4=s.regs 4-80) :
    (writes t).map Prod.fst=stackAddresses s := by
  simp [writes,stackAddresses,sp,BitVec.sub_eq_add_neg,BitVec.add_assoc]
theorem entry_execution (s : X86Memory.State) (f : Option Flags) (table cache : Word)
    (initial : E1M1AimSideEntry.Initial s table) (v : OriginalGroupHeap.View)
    (heap : E1M1AimSideAllocate.HeapInitial s v) (frame : E1M1AimSidePublish.AllocationFrame s v)
    (aligned : (v.block+24).extractLsb' 0 8 &&& 3=0) (safe : E1M1AimWordFill.Entry32Safe s v)
    (inputs : E1M1AimCacheDispatch.CacheInitial s v cache) (miss : load32 s.memory (cache+36)=0)
    (pointerSafe : E1M1AimCacheCall.ReadSafe s v 0x74fa4)
    (lengthSafe : E1M1AimCacheCall.ReadSafe s v (180+table+16))
    (nextSize nextNext : Word) (history : E1M1AimCacheHeap.History s v nextSize nextNext)
    (conditions : E1M1AimCacheAllocate.Conditions s v cache nextSize nextNext)
    (readSafe : E1M1AimCacheRead.ReadConditions s v cache nextSize nextNext)
    (bodySafe : E1M1AimReadPrologue.Conditions s v cache nextSize nextNext)
    (iconSafe : Conditions s v cache nextSize nextNext) :
    ∃ h<8, (∃ n≤5428, X86WordFillRoutine.Prefix program [] n
      (X86WordFillRoutine.embed ⟨s,f,0x2e3e0⟩) (boundary s h table cache)) ∧
      (boundary s h table cache).pc=(if load32 s.memory 0x29134=0 then 0x38c2b else 0x1adc0) ∧
      (boundary s h table cache).core.regs 7=9 ∧
      (boundary s h table cache).core.regs 5=(E1M1AimCacheHeap.nextView v nextSize nextNext).block+24 ∧
      (boundary s h table cache).core.regs 1=180+table ∧
      (boundary s h table cache).core.regs 4=
        (if load32 s.memory 0x29134=0 then s.regs 4-76 else s.regs 4-92) := by
  obtain ⟨h,small,⟨n,b,path⟩,pc,idx,raw,dir,sp,ret⟩ := E1M1AimReadPrologue.entry_execution
    s f table cache initial v heap frame aligned safe inputs miss pointerSafe lengthSafe
    nextSize nextNext history conditions readSafe bodySafe
  have readSP : (E1M1AimCacheRead.readCalled s h cache).core.regs 4=s.regs 4-56 := by
    have o := E1M1AimReadPrologue.call_observations (E1M1AimCacheRead.readCalled s h cache).core table
    have osp : (E1M1AimReadPrologue.entered s h table cache).core.regs 4=
        (E1M1AimCacheRead.readCalled s h cache).core.regs 4-24 := o.2.2.2.1
    rw [osp] at sp
    simpa only [BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.ofNat_eq_ofNat,BitVec.reduceNeg,BitVec.reduceAdd,BitVec.add_zero] using congrArg (fun x : Word => x+24) sp
  have orig := E1M1AimReadPrologue.read_frame s f table cache initial v heap frame h small safe
    nextSize nextNext history conditions 0x29134 iconSafe.original
  have kept := (E1M1AimReadPrologue.entry_frame s h table cache 0x29134 readSP iconSafe.prologue).trans orig
  have ss : Safe (E1M1AimReadPrologue.entered s h table cache).core 0x29134 := by
    intro w hw
    apply iconSafe.stack w.1
    rw [←stack_writes s _ sp]
    exact List.mem_map.mpr ⟨w,hw,rfl⟩
  obtain ⟨m,mb,tail⟩ := execution (E1M1AimReadPrologue.entered s h table cache).core none
    (load32 s.memory 0x29134) kept ss
  have seam : X86WordFillRoutine.embed ⟨(E1M1AimReadPrologue.entered s h table cache).core,none,0x1adb0⟩=
      E1M1AimReadPrologue.entered s h table cache := by rfl
  rw [seam] at tail
  have obs := result_observations (E1M1AimReadPrologue.entered s h table cache).core (load32 s.memory 0x29134)
  have rr := result_registers (E1M1AimReadPrologue.entered s h table cache).core (load32 s.memory 0x29134)
  rw [sp,ret] at obs
  refine ⟨h,small,⟨n+m,by omega,path.trans tail⟩,obs.1, (rr 7 (by decide)).trans idx,
    (rr 5 (by decide)).trans raw,(rr 1 (by decide)).trans dir,?_⟩
  simpa [boundary,BitVec.sub_eq_add_neg,BitVec.add_assoc] using obs.2

theorem entry_frame (s : X86Memory.State) (h : Nat) (table cache a : Word)
    (sp : (E1M1AimReadPrologue.entered s h table cache).core.regs 4=s.regs 4-80)
    (safe : Separated a (stackAddresses s)) :
    load32 (boundary s h table cache).core.memory a=
      load32 (E1M1AimReadPrologue.entered s h table cache).core.memory a := by
  unfold boundary
  rw [result_memory]
  apply HeapWrites.frame
  intro w hw
  apply safe w.1
  rw [←stack_writes s _ sp]
  exact List.mem_map.mpr ⟨w,hw,rfl⟩

/-- Byte-level frame, applicable to all 11664 produced zero bytes and arbitrary
raw payload bytes. Neither path writes the payload. -/
theorem byte_frame (s : X86Memory.State) (value a : Word)
    (safe : E1M1AimCacheRead.ByteSafe a ((writes s).map Prod.fst)) :
    (result s value).core.memory a=s.memory a := by
  rw [result_memory]; exact E1M1AimCacheRead.bytes_frame _ _ _ safe
end Doom.Proofs.E1M1AimDiskRead
