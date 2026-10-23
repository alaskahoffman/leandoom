import Doom.Proofs.E1M1AimDiskRead
/-! Real existing-handle seek CALL or reopen CALL after actual disabled-icon RET.
No open/seek result, DOS interrupt or payload input is assumed or performed. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1AimReadRequest
open Verification X86 X86Memory X86Control BlockSummary
open OriginalGroupHeap (Separated)
def program := E1M1AimDiskRead.program
abbrev op := E1M1AimWordFill.op
def listed : X86WordFillRoutine.Program
  | 0x38c2b => some (op (.control (.block (.legacy (.load 3 1 8)))),3)
  | 0x38c2e => some (op (.compareRegister 3 (-1)),3)
  | 0x38c31 => some (op (.control (.jumpZero false 47)),2)
  | 0x38c33 => some (op (.pushImmediate 512),5)
  | 0x38c38 => some (op (.control (.block (.load 6 ⟨none,none,0,0x74f9c⟩))),6)
  | 0x38c3e => some (op (.push 6),1)
  | 0x38c3f => some (op (.call 31309),5)
  | 0x38c62 => some (op (.control (.block (.legacy (.mov 6 3)))),2)
  | 0x38c64 => some (op (.control (.block (.legacy (.mov 0 6)))),2)
  | 0x38c66 => some (op (.control (.block (.legacy (.load 2 1 12)))),3)
  | 0x38c69 => some (op (.xorRegister 3 3),2)
  | 0x38c6b => some (op (.call 31824),5)
  | _ => none
theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def branch (s : X86Memory.State) (handle : Word) : X86WordFillRoutine.State :=
  ⟨put s 3 handle,.legacy (some (compare32 handle (-1))),if handle= -1 then 0x38c33 else 0x38c62⟩
def seekCalled (s : X86Memory.State) (handle offset : Word) : X86WordFillRoutine.State :=
  ⟨X86Routine.pushWord (put (put (put (put s 6 handle) 0 handle) 2 offset) 3 0) 0x38c70,
   .legacy (some (logical32 0)),0x408c0⟩
def openCalled (s : X86Memory.State) (name : Word) : X86WordFillRoutine.State :=
  ⟨X86Routine.pushWord (X86Routine.pushWord (put (X86Routine.pushWord (put s 3 (-1)) 512) 6 name) name) 0x38c44,
   .legacy (some (compare32 (-1) (-1))),0x40691⟩
theorem branch_execution (s : X86Memory.State) (f : Option Flags) (handle : Word)
    (cell : load32 s.memory (s.regs 1+8)=handle) :
    X86WordFillRoutine.Prefix program [] 3 (X86WordFillRoutine.embed ⟨s,f,0x38c2b⟩) (branch s handle) := by
  simp only [BitVec.ofNat_eq_ofNat] at cell
  have path : X86WordFillRoutine.Prefix listed [] 3 (X86WordFillRoutine.embed ⟨s,f,0x38c2b⟩) (branch s handle) := by
    refine .step (by simp [X86WordFillRoutine.embed]) rfl rfl ?_
    refine .step (middle:=⟨put s 3 handle,.legacy (some (compare32 handle (-1))),0x38c31⟩) (by simp) rfl ?_ ?_
    · simp [X86WordFillRoutine.execute,X86WordFillRoutine.embed,X86FillRoutine.execute,
        X86StartupRoutine.execute,X86ByteRoutine.execute,X86Routine.execute,X86Control.execute,
        X86Block.execute,X86Memory.execute,blockPreservesFlags,put,write,cell]
    refine .step (middle:=branch s handle) (by simp) rfl ?_ (.nil _)
    by_cases h : handle=4294967295#32 <;>
      simp [branch,X86WordFillRoutine.execute,X86WordFillRoutine.embed,X86FillRoutine.execute,
        X86StartupRoutine.execute,X86ByteRoutine.execute,X86Routine.execute,X86Control.execute,compare32,BitVec.sub_eq_iff_eq_add,h]
  exact path.transfer _ [] decoded (by simp)
theorem seek_execution (s : X86Memory.State) (f : Option Flags) (handle offset : Word)
    (cell : load32 s.memory (s.regs 1+8)=handle) (opened : handle≠ -1)
    (position : load32 s.memory (s.regs 1+12)=offset) :
    X86WordFillRoutine.Prefix program [] 8 (X86WordFillRoutine.embed ⟨s,f,0x38c2b⟩) (seekCalled s handle offset) := by
  simp only [BitVec.ofNat_eq_ofNat,BitVec.reduceNeg] at opened position
  have path : X86WordFillRoutine.Prefix listed [] 5 (branch s handle) (seekCalled s handle offset) := by
    have start : branch s handle=⟨put s 3 handle,.legacy (some (compare32 handle (-1))),0x38c62⟩ := by
      simp [branch,opened]
    rw [start]
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (middle:=seekCalled s handle offset) (by simp) rfl ?_ (.nil _)
    simp [seekCalled,branch,X86WordFillRoutine.execute,X86WordFillRoutine.embed,X86FillRoutine.execute,
      X86StartupRoutine.execute,X86ByteRoutine.execute,X86Routine.execute,X86Control.execute,
      X86Block.execute,X86Memory.execute,blockPreservesFlags,X86Routine.pushWord,logical32,put,write,position,opened]
    funext r
    by_cases h : r=3 <;> simp [write,h]
  exact (branch_execution s f handle cell).trans (path.transfer _ [] decoded (by simp))
theorem open_execution (s : X86Memory.State) (f : Option Flags) (name : Word)
    (cell : load32 s.memory (s.regs 1+8)= -1) (filename : load32 s.memory 0x74f9c=name)
    (safe : Apart 0x74f9c (s.regs 4-4)) :
    X86WordFillRoutine.Prefix program [] 7 (X86WordFillRoutine.embed ⟨s,f,0x38c2b⟩) (openCalled s name) := by
  have p := (load_store_apart s.memory (s.regs 4-4) 0x74f9c 512 safe).trans filename
  simp only [BitVec.ofNat_eq_ofNat] at p
  have path : X86WordFillRoutine.Prefix listed [] 4 (branch s (-1)) (openCalled s name) := by
    refine .step (by simp [branch]) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (middle:=openCalled s name) (by simp) rfl ?_ (.nil _)
    simp [openCalled,branch,X86WordFillRoutine.execute,X86WordFillRoutine.embed,X86FillRoutine.execute,
      X86StartupRoutine.execute,X86ByteRoutine.execute,X86Routine.execute,X86Control.execute,
      X86Block.execute,X86Memory.execute,X86Block.Address.eval,blockPreservesFlags,
      X86Routine.pushWord,put,write,p]
  exact (branch_execution s f (-1) cell).trans (path.transfer _ [] decoded (by simp))

def requested (s : X86Memory.State) (handle offset name : Word) :=
  if handle= -1 then openCalled s name else seekCalled s handle offset
def requestWrites (s : X86Memory.State) (handle name : Word) : List (Word × Word) :=
  if handle= -1 then [(s.regs 4-4,512),(s.regs 4-8,name),(s.regs 4-12,0x38c44)]
  else [(s.regs 4-4,0x38c70)]
theorem request_memory (s : X86Memory.State) (handle offset name : Word) :
    (requested s handle offset name).core.memory=HeapWrites.apply (requestWrites s handle name) s.memory := by
  by_cases h : handle=4294967295#32 <;>
    simp [requested,requestWrites,openCalled,seekCalled,h,HeapWrites.apply,
      X86Routine.pushWord,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc]
theorem request_frame (s : X86Memory.State) (handle offset name a : Word)
    (safe : ∀ w∈requestWrites s handle name, Apart a w.1) :
    load32 (requested s handle offset name).core.memory a=load32 s.memory a := by
  rw [request_memory]; exact HeapWrites.frame _ _ _ safe
theorem request_byte_frame (s : X86Memory.State) (handle offset name a : Word)
    (safe : E1M1AimCacheRead.ByteSafe a ((requestWrites s handle name).map Prod.fst)) :
    (requested s handle offset name).core.memory a=s.memory a := by
  rw [request_memory]; exact E1M1AimCacheRead.bytes_frame _ _ _ safe
theorem request_registers (s : X86Memory.State) (handle offset name : Word) :
    (requested s handle offset name).core.regs 5=s.regs 5 ∧
    (requested s handle offset name).core.regs 7=s.regs 7 ∧
    (requested s handle offset name).core.regs 1=s.regs 1 ∧
    (requested s handle offset name).pc=(if handle= -1 then 0x40691 else 0x408c0) ∧
    (requested s handle offset name).core.regs 4=(if handle= -1 then s.regs 4-12 else s.regs 4-4) := by
  by_cases h : handle=4294967295#32 <;>
    simp [requested,openCalled,seekCalled,h,X86Routine.pushWord,put,write,
      BitVec.sub_eq_add_neg,BitVec.add_assoc]
theorem execution (s : X86Memory.State) (f : Option Flags) (handle offset name : Word)
    (cell : load32 s.memory (s.regs 1+8)=handle)
    (position : load32 s.memory (s.regs 1+12)=offset)
    (filename : load32 s.memory 0x74f9c=name) (safe : Apart 0x74f9c (s.regs 4-4)) :
    ∃ n≤8, X86WordFillRoutine.Prefix program [] n
      (X86WordFillRoutine.embed ⟨s,f,0x38c2b⟩) (requested s handle offset name) := by
  by_cases h : handle=4294967295#32
  · have c : load32 s.memory (s.regs 1+8)= -1 := cell.trans h
    exact ⟨7,by omega,by simpa [requested,h] using open_execution s f name c filename safe⟩
  · exact ⟨8,by omega,by simpa [requested,h] using seek_execution s f handle offset cell h position⟩

structure Conditions (s : X86Memory.State) (v : OriginalGroupHeap.View)
    (table cache nextSize nextNext : Word) : Prop where
  original : ∀ a∈[180+table+8,180+table+12,0x74f9c],
    E1M1AimReadPrologue.OriginalSafe s v cache nextSize nextNext a
  prologue : ∀ a∈[180+table+8,180+table+12,0x74f9c], Separated a (E1M1AimReadPrologue.stackAddresses s)
  icon : ∀ a∈[180+table+8,180+table+12,0x74f9c], Separated a (E1M1AimDiskRead.stackAddresses s)
  namePush : Apart 0x74f9c (s.regs 4-80)
def boundary (s : X86Memory.State) (h : Nat) (table cache : Word) :=
  requested (E1M1AimDiskRead.boundary s h table cache).core
    (load32 s.memory (180+table+8)) (load32 s.memory (180+table+12)) (load32 s.memory 0x74f9c)
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
    (iconSafe : E1M1AimDiskRead.Conditions s v cache nextSize nextNext)
    (disabled : load32 s.memory 0x29134=0)
    (fileSafe : Conditions s v table cache nextSize nextNext) :
    ∃ h<8, (∃ n≤5436, X86WordFillRoutine.Prefix program [] n
      (X86WordFillRoutine.embed ⟨s,f,0x2e3e0⟩) (boundary s h table cache)) ∧
      (boundary s h table cache).pc=(if load32 s.memory (180+table+8)= -1 then 0x40691 else 0x408c0) ∧
      (boundary s h table cache).core.regs 7=9 ∧
      (boundary s h table cache).core.regs 5=(E1M1AimCacheHeap.nextView v nextSize nextNext).block+24 ∧
      (boundary s h table cache).core.regs 1=180+table ∧
      (boundary s h table cache).core.regs 4=
        (if load32 s.memory (180+table+8)= -1 then s.regs 4-88 else s.regs 4-80) := by
  obtain ⟨h,small,⟨n,b,path⟩,pc,idx,raw,dir,sp⟩ := E1M1AimDiskRead.entry_execution
    s f table cache initial v heap frame aligned safe inputs miss pointerSafe lengthSafe
    nextSize nextNext history conditions readSafe bodySafe iconSafe
  rw [disabled,if_pos rfl] at pc sp
  have isp : (E1M1AimReadPrologue.entered s h table cache).core.regs 4=s.regs 4-80 := by
    have o := (E1M1AimDiskRead.result_observations (E1M1AimReadPrologue.entered s h table cache).core
      (load32 s.memory 0x29134)).2
    change (E1M1AimDiskRead.boundary s h table cache).core.regs 4=_ at o
    rw [disabled,if_pos rfl] at o
    have eq := o.symm.trans sp
    simpa only [BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.ofNat_eq_ofNat,
      BitVec.reduceNeg,BitVec.reduceAdd,BitVec.add_zero] using congrArg (fun x : Word=>x-4) eq
  have rsp : (E1M1AimCacheRead.readCalled s h cache).core.regs 4=s.regs 4-56 := by
    have o := (E1M1AimReadPrologue.call_observations (E1M1AimCacheRead.readCalled s h cache).core table).2.2.2.1
    change (E1M1AimReadPrologue.entered s h table cache).core.regs 4=_ at o
    have eq := o.symm.trans isp
    simpa only [BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.ofNat_eq_ofNat,
      BitVec.reduceNeg,BitVec.reduceAdd,BitVec.add_zero] using congrArg (fun x : Word=>x+24) eq
  have keep (a : Word) (ha : a∈[180+table+8,180+table+12,0x74f9c]) :
      load32 (E1M1AimDiskRead.boundary s h table cache).core.memory a=load32 s.memory a :=
    (E1M1AimDiskRead.entry_frame s h table cache a isp (fileSafe.icon a ha)).trans
      ((E1M1AimReadPrologue.entry_frame s h table cache a rsp (fileSafe.prologue a ha)).trans
        (E1M1AimReadPrologue.read_frame s f table cache initial v heap frame h small safe
          nextSize nextNext history conditions a (fileSafe.original a ha)))
  have cell : load32 (E1M1AimDiskRead.boundary s h table cache).core.memory
      ((E1M1AimDiskRead.boundary s h table cache).core.regs 1+8)=load32 s.memory (180+table+8) := by
    rw [dir]; exact keep _ (by simp)
  have pos : load32 (E1M1AimDiskRead.boundary s h table cache).core.memory
      ((E1M1AimDiskRead.boundary s h table cache).core.regs 1+12)=load32 s.memory (180+table+12) := by
    rw [dir]; exact keep _ (by simp)
  have sep : Apart 0x74f9c ((E1M1AimDiskRead.boundary s h table cache).core.regs 4-4) := by
    rw [sp]; simpa only [BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.ofNat_eq_ofNat,
      BitVec.reduceNeg,BitVec.reduceAdd] using fileSafe.namePush
  obtain ⟨m,mb,tail⟩ := execution (E1M1AimDiskRead.boundary s h table cache).core (some (compare32 0 0))
    _ _ _ cell pos (keep _ (by simp)) sep
  have seam : X86WordFillRoutine.embed ⟨(E1M1AimDiskRead.boundary s h table cache).core,
      some (compare32 0 0),0x38c2b⟩=E1M1AimDiskRead.boundary s h table cache := by
    have flags : (E1M1AimDiskRead.boundary s h table cache).flags=.legacy (some (compare32 0 0)) := by
      simp only [E1M1AimDiskRead.boundary,E1M1AimDiskRead.result,disabled,ite_true,eq_self,E1M1AimDiskRead.returned]
    simp only [X86WordFillRoutine.embed]; rw [←pc,←flags]
  rw [seam] at tail
  have obs := request_registers (E1M1AimDiskRead.boundary s h table cache).core
    (load32 s.memory (180+table+8)) (load32 s.memory (180+table+12)) (load32 s.memory 0x74f9c)
  refine ⟨h,small,⟨n+m,by omega,path.trans tail⟩,obs.2.2.2.1,obs.2.1.trans idx,
    obs.1.trans raw,obs.2.2.1.trans dir,?_⟩
  have out : (boundary s h table cache).core.regs 4=
      (if load32 s.memory (180+table+8)= -1 then
        (E1M1AimDiskRead.boundary s h table cache).core.regs 4-12 else
        (E1M1AimDiskRead.boundary s h table cache).core.regs 4-4) := obs.2.2.2.2
  rw [sp] at out
  simpa only [BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.ofNat_eq_ofNat,
    BitVec.reduceNeg,BitVec.reduceAdd] using out
end Doom.Proofs.E1M1AimReadRequest
