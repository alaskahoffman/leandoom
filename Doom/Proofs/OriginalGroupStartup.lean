import Doom.Proofs.OriginalGroupMalloc
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000
namespace Doom.Proofs.OriginalGroupStartup
open Verification X86 X86Memory X86Control
open OriginalGroupOutput (Line Inputs Linked)

def program : X86Routine.Program := fun pc =>
  if 0x2e5ef≤pc ∧ pc<0x2e639 then OriginalGroupCount.program pc else OriginalGroupMalloc.program pc

def result (es : List Line) (s : X86Memory.State) :=
  OriginalGroupMalloc.result (OriginalGroupCountScan.final es s).core

theorem count_agrees (pc : Nat) (h : OriginalGroupCount.program pc≠none) :
    program pc=OriginalGroupCount.program pc := by
  by_cases yes : 0x2e5ef≤pc ∧ pc<0x2e639
  · simp [program,yes]
  · simp [OriginalGroupCount.program,OriginalGroupCount.bytesProgram,yes] at h

theorem malloc_agrees (pc : Nat) (h : OriginalGroupMalloc.program pc≠none) :
    program pc=OriginalGroupMalloc.program pc := by
  by_cases yes : 0x2e5ef≤pc ∧ pc<0x2e639
  · have a : ¬((0x2e639≤pc ∧ pc<0x2e63e) ∨ (0x39690≤pc ∧ pc<0x396f8)) := by omega
    have b : ¬(0x396f8≤pc ∧ pc<0x39731) := by omega
    have c : ¬(0x39731≤pc ∧ pc<0x39776) := by omega
    have d : ¬(0x2e63e≤pc ∧ pc<0x2e661) := by omega
    have e : ¬(0x241c0≤pc ∧ pc<0x241dc) := by omega
    simp [OriginalGroupMalloc.program,a,OriginalGroupSelected.program,b,OriginalGroupHandoff.program,c,
      OriginalGroupEntry.program,OriginalGroupEntry.bytesProgram,d,e] at h
  · simp [program,yes]

/-- Count every line, execute the allocator CALL and suitable-first-free path,
then return through grouping entry. No state resets at any seam. -/
theorem execution (es : List Line) (s : X86Memory.State) (f : Option Flags)
    (small : es.length<2147483648) (layout : OriginalGroupCountScan.Layout es)
    (inputs : Inputs es s.memory) (linked : Linked es (load32 s.memory 0x2c120))
    (count : (load32 s.memory 0x2c134).toNat=es.length)
    (heap : OriginalGroupMalloc.Ready (OriginalGroupCountScan.final es s).core) :
    X86Routine.run program [0x2e661,0x2e791] (87+17*es.length) ⟨s,f,0x2e5ef⟩=some (result es s) := by
  obtain ⟨n,hn,p,_⟩ := X86Routine.run_path (OriginalGroupCountScan.complete es s f small layout inputs linked count)
  have p := p.transfer program [0x2e661,0x2e791] count_agrees (by
    intro pc h member
    simp at member
    rcases member with rfl|rfl <;> exact h (by decide))
  have args := OriginalGroupCountScan.final_arguments es s layout inputs linked
  have tail := OriginalGroupMalloc.execution (OriginalGroupCountScan.final es s).core
    (OriginalGroupCountScan.final es s).flags heap args.2.2.1 args.2.1
  have eta : (⟨(OriginalGroupCountScan.final es s).core,(OriginalGroupCountScan.final es s).flags,0x2e639⟩ : X86Control.State)=OriginalGroupCountScan.final es s := by
    rw [←args.2.2.2]
  rw [eta] at tail
  rw [←X86Routine.run_sound program OriginalGroupMalloc.program malloc_agrees _ _ _ (by rw [tail]; simp)] at tail
  exact p.finish tail _ (by omega)

theorem sector_count (es : List Line) (s : X86Memory.State) (q : Word)
    (layout : OriginalGroupCountScan.Layout es) (inputs : Inputs es s.memory)
    (linked : Linked es (load32 s.memory 0x2c120)) (nonzero : q≠(0#32))
    (counterSafe : OriginalGroupCountScan.CounterSafe q es)
    (allocationSafe : OriginalGroupMalloc.SafeWord (q+78) (OriginalGroupCountScan.final es s).core) :
    load32 (result es s).core.memory (q+78)=
      load32 s.memory (q+78)+BitVec.ofNat 32 (OriginalGroupOutput.chosen q es).length :=
  (OriginalGroupMalloc.frame _ _ allocationSafe).trans
    (OriginalGroupCountScan.final_sector es s q layout inputs linked nonzero counterSafe)

theorem cached_inputs (es : List Line) (s : X86Memory.State)
    (layout : OriginalGroupCountScan.Layout es) (inputs : Inputs es s.memory)
    (linked : Linked es (load32 s.memory 0x2c120))
    (safe : ∀ e∈es, OriginalGroupMalloc.SafeWord (e.address+46) (OriginalGroupCountScan.final es s).core ∧
      OriginalGroupMalloc.SafeWord (e.address+50) (OriginalGroupCountScan.final es s).core) :
    Inputs es (result es s).core.memory :=
  OriginalGroupMalloc.inputs es _ (OriginalGroupCountScan.final_inputs es s layout inputs linked) safe
end Doom.Proofs.OriginalGroupStartup
