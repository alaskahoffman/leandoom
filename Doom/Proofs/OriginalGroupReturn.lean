import Doom.Proofs.OriginalGroupCacheCall
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000
namespace Doom.Proofs.OriginalGroupReturn
open Verification X86 X86Memory X86Control BlockSummary
open OriginalGroupRemainder (Plan Conditions)

def returned (p : Plan) (s : X86Memory.State) :=
  OriginalGroupRestore.result (p.result s).core (p.result s).flags

def result (p : Plan) (s : X86Memory.State) :=
  OriginalGroupCacheCall.result (returned p s).core (returned p s).flags

/-- All four saved registers and the return word survive metadata writes. -/
def FrameSafe (p : Plan) (s : X86Memory.State) : Prop :=
  ∀ i : Fin 5, ∀ w∈p.writes, Apart (s.regs 4+BitVec.ofNat 32 (4*i.val)) w.1

theorem saved_frame (p : Plan) (s : X86Memory.State) (c : Conditions p s.memory)
    (safe : FrameSafe p s) (i : Fin 5) :
    load32 (p.result s).core.memory (s.regs 4+BitVec.ofNat 32 (4*i.val))=
      load32 s.memory (s.regs 4+BitVec.ofNat 32 (4*i.val)) := by
  rw [OriginalGroupRemainder.result_memory p s c]
  exact HeapWrites.frame _ _ _ (safe i)

theorem metadata_stack (p : Plan) (s : X86Memory.State) : (p.result s).core.regs 4=s.regs 4 := by
  change (OriginalGroupOwned.committed (p.split s).core).regs 4=s.regs 4
  simp only [OriginalGroupOwned.committed,put,write]
  rw [OriginalGroupRemainder.split_register p s 4 (by decide) (by decide)]
  simp [Plan.input,put,write]

theorem return_pc (p : Plan) (s : X86Memory.State) (c : Conditions p s.memory)
    (safe : FrameSafe p s) (ret : load32 s.memory (s.regs 4+16)=0x38d41) :
    (returned p s).pc=0x38d41 := by
  have kept := (saved_frame p s c safe 4).trans ret
  change (load32 (p.result s).core.memory ((p.result s).core.regs 4+16)).toNat=0x38d41
  rw [metadata_stack]
  exact congrArg BitVec.toNat kept

theorem restored_registers (p : Plan) (s : X86Memory.State) (c : Conditions p s.memory)
    (safe : FrameSafe p s) :
    (returned p s).core.regs 4=s.regs 4+20 ∧
    (returned p s).core.regs 5=load32 s.memory (s.regs 4) ∧
    (returned p s).core.regs 7=load32 s.memory (s.regs 4+4) ∧
    (returned p s).core.regs 6=load32 s.memory (s.regs 4+8) ∧
    (returned p s).core.regs 1=load32 s.memory (s.regs 4+12) := by
  have h := OriginalGroupRestore.registers (p.result s).core (p.result s).flags
  rw [metadata_stack] at h
  exact ⟨h.1,h.2.1.trans (by simpa using saved_frame p s c safe 0),
    h.2.2.1.trans (saved_frame p s c safe 1),h.2.2.2.1.trans (saved_frame p s c safe 2),
    h.2.2.2.2.1.trans (saved_frame p s c safe 3)⟩

theorem returned_view (p : Plan) (s : X86Memory.State) (c : Conditions p s.memory) :
    p.view.Holds (returned p s).core.memory := OriginalGroupRemainder.establishes_view p s c

private theorem allocation_agrees (pc : Nat) (h : OriginalGroupRestore.program pc≠none) :
    OriginalGroupRemainder.program pc=OriginalGroupRestore.program pc :=
  (OriginalGroupSelected.handoff_agrees pc (by
    rw [OriginalGroupHandoff.allocation_agrees pc h]; exact h)).trans
    (OriginalGroupHandoff.allocation_agrees pc h)

/-- Split, owner publication, four POPs and actual RET in one machine state. -/
theorem return_execution (p : Plan) (s : X86Memory.State) (f : Option Flags)
    (c : Conditions p s.memory) (safe : FrameSafe p s)
    (ret : load32 s.memory (s.regs 4+16)=0x38d41) :
    X86Routine.run OriginalGroupRemainder.program [0x38d41] 31
      ⟨p.input s,f,0x39704⟩=some (returned p s) := by
  obtain ⟨n,hn,path,_⟩ := X86Routine.run_path (OriginalGroupRemainder.execution p s f c.owner)
  have path := path.transfer OriginalGroupRemainder.program [0x38d41] (by intros; rfl) (by
    intro pc h member
    simp only [List.mem_singleton] at member
    subst pc
    exact h (by decide))
  have preserved : load32 (p.result s).core.memory ((p.result s).core.regs 4+16)=0x38d41 := by
    rw [metadata_stack]
    exact (saved_frame p s c safe 4).trans ret
  have tail := OriginalGroupRestore.execution (p.result s).core (p.result s).flags (0x38d41#32)
    (by decide) preserved
  have eta : (⟨(p.result s).core,(p.result s).flags,0x39771⟩ : X86Control.State)=p.result s := rfl
  rw [eta] at tail
  rw [←X86Routine.run_sound OriginalGroupRemainder.program OriginalGroupRestore.program
    allocation_agrees _ _ _ (by rw [tail]; simp)] at tail
  exact path.finish tail 31 (by omega)

def program : X86Routine.Program := fun pc =>
  if 0x38d41≤pc ∧ pc<0x38d50 then OriginalGroupCacheCall.program pc else OriginalGroupRemainder.program pc

theorem cache_agrees (pc : Nat) (h : OriginalGroupCacheCall.program pc≠none) :
    program pc=OriginalGroupCacheCall.program pc := by
  by_cases yes : 0x38d41≤pc ∧ pc<0x38d50
  · simp [program,yes]
  · simp [OriginalGroupCacheCall.program,OriginalGroupCacheCall.bytesProgram,yes] at h

theorem allocator_agrees (pc : Nat) (h : OriginalGroupRemainder.program pc≠none) :
    program pc=OriginalGroupRemainder.program pc := by
  by_cases yes : 0x38d41≤pc ∧ pc<0x38d50
  · have a : ¬(0x396f8≤pc ∧ pc<0x39731) := by omega
    have b : ¬(0x39731≤pc ∧ pc<0x39776) := by omega
    have d : ¬(0x2e63e≤pc ∧ pc<0x2e661) := by omega
    have e : ¬(0x241c0≤pc ∧ pc<0x241dc) := by omega
    simp [OriginalGroupRemainder.program,OriginalGroupSelected.program,a,
      OriginalGroupHandoff.program,b,OriginalGroupEntry.program,OriginalGroupEntry.bytesProgram,d,e] at h
  · simp [program,yes]

/-- Includes the caller's actual CALL into W_ReadLump; does not execute file I/O. -/
theorem execution (p : Plan) (s : X86Memory.State) (f : Option Flags)
    (c : Conditions p s.memory) (safe : FrameSafe p s)
    (ret : load32 s.memory (s.regs 4+16)=0x38d41) :
    X86Routine.run program [0x38bf0] 35 ⟨p.input s,f,0x39704⟩=some (result p s) := by
  obtain ⟨n,hn,path,_⟩ := X86Routine.run_path (return_execution p s f c safe ret)
  have path := path.transfer program [0x38bf0] allocator_agrees (by
    intro pc h member
    simp only [List.mem_singleton] at member
    subst pc
    exact h (by decide))
  have tail := OriginalGroupCacheCall.execution (returned p s).core (returned p s).flags
  have eta : (⟨(returned p s).core,(returned p s).flags,0x38d41⟩ : X86Control.State)=returned p s := by
    rw [←return_pc p s c safe ret]
  rw [eta] at tail
  rw [←X86Routine.run_sound program OriginalGroupCacheCall.program cache_agrees _ _ _ (by rw [tail]; simp)] at tail
  exact path.finish tail 35 (by omega)

/-- Initial saved index/offset and cache global explain the caller's arguments. -/
theorem read_arguments (p : Plan) (s : X86Memory.State) (c : Conditions p s.memory)
    (safe : FrameSafe p s) (index cache : Word)
    (offset : load32 s.memory (s.regs 4+8)=index*4)
    (savedIndex : load32 s.memory (s.regs 4+12)=index)
    (cacheValue : load32 s.memory 0x74f94=cache)
    (cacheSafe : ∀ w∈p.writes, Apart 0x74f94 w.1)
    (owner : p.owner=index*4+cache) :
    (result p s).core.regs 0=index ∧ (result p s).core.regs 2=p.block+24 ∧
    (result p s).core.regs 4=s.regs 4+16 := by
  have regs := restored_registers p s c safe
  have cg : load32 (returned p s).core.memory 0x74f94=cache := by
    change load32 (p.result s).core.memory 0x74f94=cache
    rw [OriginalGroupRemainder.result_memory p s c]
    exact (HeapWrites.frame _ _ _ cacheSafe).trans cacheValue
  have cell : OriginalGroupCacheCall.cell (returned p s).core=p.owner := by
    unfold OriginalGroupCacheCall.cell
    rw [regs.2.2.2.1,offset,cg,←owner]
  have payload : OriginalGroupCacheCall.payload (returned p s).core=p.block+24 := by
    unfold OriginalGroupCacheCall.payload
    rw [cell]
    exact OriginalGroupRemainder.owner_published p s c
  have args := OriginalGroupCacheCall.arguments (returned p s).core (returned p s).flags
  refine ⟨args.1.trans (regs.2.2.2.2.trans savedIndex),args.2.1.trans payload,?_⟩
  unfold result
  rw [args.2.2,regs.1]
  simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]

theorem read_return (p : Plan) (s : X86Memory.State) :
    load32 (result p s).core.memory ((result p s).core.regs 4)=0x38d50 :=
  OriginalGroupCacheCall.return_address _ _

theorem read_view (p : Plan) (s : X86Memory.State) (c : Conditions p s.memory)
    (safe : FrameSafe p s)
    (stack : ∀ w∈p.view.words, Apart w.1 (s.regs 4+16)) :
    p.view.Holds (result p s).core.memory := by
  apply p.view.transport _ _ (returned_view p s c)
  intro w hw
  apply OriginalGroupCacheCall.frame
  rw [(restored_registers p s c safe).1]
  simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using stack w hw
end Doom.Proofs.OriginalGroupReturn
