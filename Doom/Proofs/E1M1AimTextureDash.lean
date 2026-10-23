import Doom.Proofs.OriginalTextureDash
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1AimTextureDash
open Verification X86 X86Memory X86Control BlockSummary
open OriginalTextureDash (prepared nameByte gate zeroed returned stackMemory)

/-- The dash case executes the actual inner function, without a search oracle.
The byte condition is on the post-push memory, just as in the executable. -/
theorem inner_path (q : X86Routine.Program)
    (agree : ∀ pc, OriginalTextureDash.program pc≠none → q pc=OriginalTextureDash.program pc)
    (s : X86Memory.State) (f : Option Flags) (dash : nameByte s=(0x2d#8))
    (dest : Word) (outside : dest.toNat<0x34741 ∨ 0x34747≤dest.toNat)
    (ret : load32 s.memory (s.regs 4)=dest) :
    ∃ n≤16, X86Routine.Prefix q [] n ⟨s,f,0x346f0⟩ (returned s) := by
  obtain ⟨a,ha,pa,_⟩ := X86Routine.run_path (OriginalTextureDash.entry_execution s f)
  have endpoint : gate s=⟨prepared s,(gate s).flags,0x346fc⟩ := by simp [gate,dash]
  rw [endpoint] at pa
  obtain ⟨b,hb,pb,_⟩ := X86Routine.run_path (OriginalTextureDash.zero_execution (prepared s) (gate s).flags)
  have word : load32 (zeroed (prepared s)).core.memory ((zeroed (prepared s)).core.regs 4+20)=dest := by
    have h := OriginalTextureDash.stack_above s 0 (by simp)
    have h' : load32 (stackMemory s) (s.regs 4)=load32 s.memory (s.regs 4) := by simpa using h
    simpa [zeroed,prepared,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc] using h'.trans ret
  obtain ⟨c,hc,pc,_⟩ := X86Routine.run_path (OriginalTextureDash.return_execution
    (zeroed (prepared s)).core (zeroed (prepared s)).flags dest outside word)
  have pa := pa.transfer q [] agree (by simp)
  have pb := pb.transfer q [] agree (by simp)
  have pc := pc.transfer q [] agree (by simp)
  rw [OriginalTextureDash.restored_prepared] at pc
  exact ⟨a+b+c,by omega,OriginalGroupBounds.prefix_join (OriginalGroupBounds.prefix_join pa pb) pc⟩

theorem inner_registers (s : X86Memory.State) :
    (returned s).core.regs 0=0 ∧ (returned s).core.regs 4=s.regs 4+4 ∧
    (∀ r, r≠0 → r≠4 → (returned s).core.regs r=s.regs r) := by
  simp [returned,put,write]
  intro r h0 h4
  simp [h0,h4]

theorem inner_frame (s : X86Memory.State) (a : Word)
    (safe : ∀ off∈[(4#32),8,12,16,20], Apart a (s.regs 4-off)) :
    load32 (returned s).core.memory a=load32 s.memory a := by
  exact OriginalTextureDash.stack_frame s a safe

def inner (s : X86Memory.State) (f : Option Flags) :=
  returned (OriginalTextureWrapper.search s f).core

def completed (s : X86Memory.State) (f : Option Flags) :=
  OriginalTextureWrapper.result (OriginalTextureWrapper.choice (inner s f).core).core
    (OriginalTextureWrapper.choice (inner s f).core).flags

/-- The previously conditional wrapper receives an actual original inner path.
Only the dash byte and the caller's return word are inputs, not helper executions. -/
theorem wrapper_path (q : X86Routine.Program)
    (agree : ∀ pc, OriginalTextureDash.program pc≠none → q pc=OriginalTextureDash.program pc)
    (wrapper : ∀ pc, OriginalTextureWrapper.program pc≠none → q pc=OriginalTextureWrapper.program pc)
    (s : X86Memory.State) (f : Option Flags)
    (dash : nameByte (OriginalTextureWrapper.search s f).core=(0x2d#8))
    (dest : Word) (outside : dest.toNat<0x3476e ∨ 0x34773≤dest.toNat)
    (ret : load32 s.memory (s.regs 4)=dest) :
    ∃ n≤27, X86Routine.Prefix q [] n ⟨s,f,0x34750⟩
      ⟨(completed s f).core,(completed s f).flags,dest.toNat⟩ := by
  have args := OriginalTextureWrapper.entry_arguments s f
  obtain ⟨n,hn,path⟩ := inner_path q agree (OriginalTextureWrapper.search s f).core f dash
    0x34759 (by decide) args.2.2.2
  have ipc : (inner s f).pc=0x34759 := by
    change (load32 (OriginalTextureWrapper.search s f).core.memory
      ((OriginalTextureWrapper.search s f).core.regs 4)).toNat=0x34759
    rw [args.2.2.2]; rfl
  have ieq : inner s f=⟨(inner s f).core,(inner s f).flags,0x34759⟩ := by
    cases h : inner s f
    simp_all
  change X86Routine.Prefix q [] n (OriginalTextureWrapper.search s f) (inner s f) at path
  rw [ieq] at path
  have found : (inner s f).core.regs 0≠(0xffffffff#32) := by simp [inner,returned,put,write]
  have callerWord := OriginalTextureWrapper.saved_slots s f
  have protect := OriginalTextureDash.stack_above (OriginalTextureWrapper.search s f).core 12 (by simp)
  have returnWord : load32 (inner s f).core.memory ((inner s f).core.regs 4+8)=dest := by
    change load32 (stackMemory (OriginalTextureWrapper.search s f).core)
      ((OriginalTextureWrapper.search s f).core.regs 4+4+8)=dest
    have offset : (OriginalTextureWrapper.search s f).core.regs 4+12=s.regs 4 := by
      rw [args.2.2.1]; simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    calc
      _ = load32 (OriginalTextureWrapper.search s f).core.memory
          ((OriginalTextureWrapper.search s f).core.regs 4+12) := by
        simpa [BitVec.add_assoc] using protect
      _ = dest := by rw [offset]; exact callerWord.2.2.trans ret
  obtain ⟨k,hk,pk⟩ := E1M1AimTextureWrapper.caller_path q wrapper s (inner s f).core
    f (inner s f).flags n path found dest outside returnWord
  exact ⟨k,by omega,pk⟩

/-- Both levels of saved-register restoration are discharged for the dash case. -/
theorem wrapper_registers (s : X86Memory.State) (f : Option Flags) :
    (completed s f).core.regs 0=0 ∧ (completed s f).core.regs 4=s.regs 4+4 ∧
    (∀ r, r≠0 → r≠4 → (completed s f).core.regs r=s.regs r) := by
  have args := OriginalTextureWrapper.entry_arguments s f
  have frame (off : Word) (member : off∈[(4#32),8]) :
      load32 (inner s f).core.memory ((OriginalTextureWrapper.search s f).core.regs 4+off)=
      load32 (OriginalTextureWrapper.search s f).core.memory ((OriginalTextureWrapper.search s f).core.regs 4+off) := by
    apply OriginalTextureDash.stack_above
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl <;> simp
  have edx := frame 4 (by simp)
  have ebx := frame 8 (by simp)
  have off4 : (OriginalTextureWrapper.search s f).core.regs 4+4=s.regs 4-8 := by
    rw [args.2.2.1]; simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  have off8 : (OriginalTextureWrapper.search s f).core.regs 4+8=s.regs 4-4 := by
    rw [args.2.2.1]; simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  rw [off4] at edx
  rw [off8] at ebx
  have stack : (inner s f).core.regs 4=s.regs 4-8 := by
    simp [inner,returned,put,write,args.2.2.1,BitVec.sub_eq_add_neg,BitVec.add_assoc]
  have h := E1M1AimTextureWrapper.saved_registers s (inner s f).core f stack edx ebx
  refine ⟨?_,h.2.2.2,?_⟩
  · exact h.1.trans (inner_registers _).1
  · intro r r0 r4
    by_cases r2 : r=2
    · subst r; exact h.2.1
    by_cases r3 : r=3
    · subst r; exact h.2.2.1
    simp [completed,OriginalTextureWrapper.result,OriginalTextureWrapper.restored,
      OriginalTextureWrapper.choice,inner,returned,OriginalTextureWrapper.search,
      OriginalTextureWrapper.saved,X86Routine.pushWord,put,write,r0,r4,r2,r3]

/-- There is no remaining helper-memory premise for this branch: only separation
from the eight concrete stack writes in the two functions. -/
theorem wrapper_frame (s : X86Memory.State) (f : Option Flags) (a : Word)
    (safe : ∀ off∈[(4#32),8,12,16,20,24,28,32], Apart a (s.regs 4-off)) :
    load32 (completed s f).core.memory a=load32 s.memory a := by
  apply E1M1AimTextureWrapper.wrapper_frame s (inner s f).core f a
    (safe 4 (by simp)) (safe 8 (by simp)) (safe 12 (by simp))
  apply inner_frame
  intro off member
  have args := OriginalTextureWrapper.entry_arguments s f
  rw [args.2.2.1]
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl
  all_goals simpa [BitVec.sub_sub] using safe _ (by simp)

end Doom.Proofs.E1M1AimTextureDash
