import Doom.Proofs.OriginalGroupMallocEntry
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalGroupMalloc
open Verification X86 X86Memory X86Control BlockSummary
open OriginalGroupMallocEntry (called saved prepared rounded)

def opened (s : X86Memory.State) := prepared (saved (called s))
def candidate (s : X86Memory.State) := OriginalGroupMallocEntry.firstFree (opened s).core
def result (s : X86Memory.State) := OriginalGroupSelected.result (candidate s).core

def program : X86Routine.Program := fun pc =>
  if (0x2e639≤pc ∧ pc<0x2e63e) ∨ (0x39690≤pc ∧ pc<0x396f8)
  then OriginalGroupMallocEntry.program pc else OriginalGroupSelected.program pc

theorem entry_agrees (pc : Nat) (h : OriginalGroupMallocEntry.program pc≠none) :
    program pc=OriginalGroupMallocEntry.program pc := by
  by_cases yes : (0x2e639≤pc ∧ pc<0x2e63e) ∨ (0x39690≤pc ∧ pc<0x396f8)
  · simp [program,yes]
  · have a : ¬(0x2e639≤pc ∧ pc<0x2e63e) := by omega
    have b : ¬(0x39690≤pc ∧ pc<0x396f8) := by omega
    simp [OriginalGroupMallocEntry.program,OriginalGroupMallocEntry.bytesProgram,a,b] at h

theorem selected_agrees (pc : Nat) (h : OriginalGroupSelected.program pc≠none) :
    program pc=OriginalGroupSelected.program pc := by
  by_cases yes : (0x2e639≤pc ∧ pc<0x2e63e) ∨ (0x39690≤pc ∧ pc<0x396f8)
  · have a : ¬(0x396f8≤pc ∧ pc<0x39731) := by omega
    have b : ¬(0x39731≤pc ∧ pc<0x39776) := by omega
    have c : ¬(0x2e63e≤pc ∧ pc<0x2e661) := by omega
    have d : ¬(0x241c0≤pc ∧ pc<0x241dc) := by omega
    simp [OriginalGroupSelected.program,a,OriginalGroupHandoff.program,b,
      OriginalGroupEntry.program,OriginalGroupEntry.bytesProgram,c,d] at h
  · simp [program,yes]

private theorem path {exits n s t}
    (h : X86Routine.run OriginalGroupMallocEntry.program exits n s=some t) :
    ∃ k, k≤n ∧ X86Routine.Prefix OriginalGroupMallocEntry.program [0x396f8] k s t := by
  obtain ⟨k,hk,p,_⟩ := X86Routine.run_path h
  refine ⟨k,hk,p.transfer _ _ (by intros; rfl) ?_⟩
  intro pc h member
  simp only [List.mem_singleton] at member
  subst pc
  exact h (by decide)

/-- First traversal premises describe the computed initial heap reads. -/
structure FirstFree (s : X86Memory.State) : Prop where
  more : (opened s).core.regs 2≠(opened s).core.regs 6
  free : load32 (opened s).core.memory ((opened s).core.regs 2+(4#32))=(0#32)

theorem prefix_execution (s : X86Memory.State) (f : Option Flags) (h : FirstFree s) :
    X86Routine.run OriginalGroupMallocEntry.program [0x396f8] 25 ⟨s,f,0x2e639⟩=some (candidate s) := by
  obtain ⟨a,ha,pa⟩ := path (OriginalGroupMallocEntry.call_execution s f)
  obtain ⟨b,hb,pb⟩ := path (OriginalGroupMallocEntry.save_execution (called s) f)
  obtain ⟨c,hc,pc⟩ := path (OriginalGroupMallocEntry.prepare_execution (saved (called s)) f)
  have tail := OriginalGroupMallocEntry.free_execution (opened s).core (opened s).flags h.more h.free
  have eta : (⟨(opened s).core,(opened s).flags,0x396bd⟩ : X86Control.State)=opened s := rfl
  rw [eta] at tail
  exact pa.finish (pb.finish (pc.finish tail 20 (by omega)) 24 (by omega)) 25 (by omega)

theorem candidate_memory (s : X86Memory.State) : (candidate s).core.memory=(saved (called s)).memory := rfl

theorem candidate_arguments (s : X86Memory.State) :
    (candidate s).core.regs 1=rounded (s.regs 0) ∧
    (candidate s).core.regs 5=s.regs 2 ∧ (candidate s).core.regs 7=s.regs 3 ∧
    (candidate s).core.regs 4=s.regs 4-20 := by
  simp [candidate,opened,OriginalGroupMallocEntry.firstFree,prepared,saved,called,
    X86Routine.pushWord,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc]

theorem saved_top (s : X86Memory.State) : load32 (saved s).memory (s.regs 4)=load32 s.memory (s.regs 4) := by
  apply OriginalGroupMallocEntry.saved_frame
  simp only [OriginalGroupMallocEntry.SafeWord,List.forall_mem_cons,List.not_mem_nil,false_implies,implies_true,and_true]
  refine ⟨?_,?_,?_,?_⟩
  · have h := PlayerHeight.slots_apart (s.regs 4-(16#32)) 4 3 (by decide)
    change Apart ((s.regs 4-(16#32))+(16#32)) ((s.regs 4-(16#32))+(12#32)) at h
    simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using h

  · have h := PlayerHeight.slots_apart (s.regs 4-(16#32)) 4 2 (by decide)
    change Apart ((s.regs 4-(16#32))+(16#32)) ((s.regs 4-(16#32))+(8#32)) at h
    simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using h

  · have h := PlayerHeight.slots_apart (s.regs 4-(16#32)) 4 1 (by decide)
    change Apart ((s.regs 4-(16#32))+(16#32)) ((s.regs 4-(16#32))+(4#32)) at h
    simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using h

  · have h := PlayerHeight.slots_apart (s.regs 4-(16#32)) 4 0 (by decide)
    change Apart ((s.regs 4-(16#32))+(16#32)) ((s.regs 4-(16#32))+(0#32)) at h
    simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using h

/-- The real CALL establishes the return slot; it is no longer supplied by a caller. -/
theorem return_address (s : X86Memory.State) :
    load32 (candidate s).core.memory ((candidate s).core.regs 4+16)=0x2e63e := by
  have sp : (candidate s).core.regs 4+(16#32)=(called s).regs 4 := by
    rw [(candidate_arguments s).2.2.2]
    simp [called,X86Routine.pushWord,write,BitVec.sub_eq_add_neg,BitVec.add_assoc]
  change load32 (candidate s).core.memory ((candidate s).core.regs 4+(16#32))=(0x2e63e#32)
  rw [candidate_memory,sp,saved_top]
  exact load_store s.memory (s.regs 4-(4#32)) (0x2e63e#32)

/-- Free and sufficiently large first candidate, with the remaining write
separation expressed on the explicit prefix state, never an assumed execution. -/
structure Ready (s : X86Memory.State) : Prop extends FirstFree s where
  fits : ((candidate s).core.regs 1).toInt≤(OriginalGroupSplit.candidateSize (candidate s).core).toInt
  safe : OriginalGroupSelected.ReturnSafe (candidate s).core

theorem candidate_free (s : X86Memory.State) (h : FirstFree s) :
    load32 (candidate s).core.memory ((candidate s).core.regs 3+(4#32))=(0#32) := by
  have same : (opened s).core.regs 3=(opened s).core.regs 2 := by simp [opened,prepared,put,write]
  simpa [candidate,OriginalGroupMallocEntry.firstFree,put,write,same] using h.free

theorem execution (s : X86Memory.State) (f : Option Flags) (h : Ready s)
    (user : s.regs 3=(0#32)) (tag : s.regs 2=(50#32)) :
    X86Routine.run program [0x2e661,0x2e791] 78 ⟨s,f,0x2e639⟩=some (result s) := by
  obtain ⟨n,hn,p,_⟩ := X86Routine.run_path (prefix_execution s f h.toFirstFree)
  have p := p.transfer program [0x2e661,0x2e791] entry_agrees (by
    intro pc h member
    simp at member
    rcases member with rfl|rfl <;> exact h (by decide))
  have args := candidate_arguments s
  have tail := OriginalGroupSelected.execution (candidate s).core (candidate s).flags
    (candidate_free s h.toFirstFree) h.fits (args.2.2.1.trans user) (args.2.1.trans tag) h.safe (return_address s)
  have eta : (⟨(candidate s).core,(candidate s).flags,0x396f8⟩ : X86Control.State)=candidate s := rfl
  rw [eta] at tail
  rw [←X86Routine.run_sound program OriginalGroupSelected.program selected_agrees _ _ _ (by rw [tail]; simp)] at tail
  exact p.finish tail 78 (by omega)

def SafeWord (a : Word) (s : X86Memory.State) : Prop :=
  Apart a (s.regs 4-4) ∧ OriginalGroupMallocEntry.SafeWord a (called s) ∧
    OriginalGroupSelected.SafeWord a (candidate s).core

theorem frame (s : X86Memory.State) (a : Word) (safe : SafeWord a s) :
    load32 (result s).core.memory a=load32 s.memory a := by
  have tail := OriginalGroupSelected.frame (candidate s).core a safe.2.2
  rw [candidate_memory] at tail
  exact tail.trans ((OriginalGroupMallocEntry.saved_frame (called s) a safe.2.1).trans
    (load_store_apart _ _ _ _ safe.1))

theorem count_field (s : X86Memory.State) (sector value : Word)
    (before : load32 s.memory (sector+78)=value) (safe : SafeWord (sector+78) s) :
    load32 (result s).core.memory (sector+78)=value := (frame s _ safe).trans before

theorem inputs (es : List OriginalGroupOutput.Line) (s : X86Memory.State)
    (before : OriginalGroupOutput.Inputs es s.memory)
    (safe : ∀ e∈es, SafeWord (e.address+46) s ∧ SafeWord (e.address+50) s) :
    OriginalGroupOutput.Inputs es (result s).core.memory := by
  intro e he
  exact ⟨(frame s _ (safe e he).1).trans (before e he).1,
    (frame s _ (safe e he).2).trans (before e he).2⟩
end Doom.Proofs.OriginalGroupMalloc
