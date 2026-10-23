import Doom.Proofs.OriginalTextureWrapper
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1AimTextureWrapper
open Verification X86 X86Memory X86Control BlockSummary
open OriginalTextureWrapper (search choice result)

/-- The full wrapper success path. Only the inner search execution remains a
premise; the wrapper prologue, result test and restoring return execute here. -/
theorem success_path (q : X86Routine.Program)
    (agree : ∀ pc, OriginalTextureWrapper.program pc≠none → q pc=OriginalTextureWrapper.program pc)
    (s t : X86Memory.State) (f g : Option Flags) (n : Nat)
    (inner : X86Routine.Prefix q [] n (search s f) ⟨t,g,0x34759⟩)
    (found : t.regs 0≠(0xffffffff#32)) (dest : Word)
    (outside : dest.toNat<0x3476e ∨ 0x34773≤dest.toNat)
    (ret : load32 t.memory (t.regs 4+8)=dest) :
    ∃ k≤n+11, X86Routine.Prefix q [] k ⟨s,f,0x34750⟩
      (result (choice t).core (choice t).flags) := by
  obtain ⟨a,ha,pa,_⟩ := X86Routine.run_path (OriginalTextureWrapper.entry_execution s f)
  obtain ⟨b,hb,pb,_⟩ := X86Routine.run_path (OriginalTextureWrapper.gate_execution t g)
  have endpoint : choice t=⟨(choice t).core,(choice t).flags,0x3476e⟩ := by simp [choice,found]
  have returns : load32 (choice t).core.memory ((choice t).core.regs 4+8)=dest := by
    simpa [choice,put,write] using ret
  obtain ⟨c,hc,pc,_⟩ := X86Routine.run_path
    (OriginalTextureWrapper.return_execution (choice t).core (choice t).flags dest outside returns)
  have pa := pa.transfer q [] agree (by simp)
  have pb := pb.transfer q [] agree (by simp)
  have pc := pc.transfer q [] agree (by simp)
  rw [← endpoint] at pc
  exact ⟨a+n+b+c,by omega,OriginalGroupBounds.prefix_join
    (OriginalGroupBounds.prefix_join (OriginalGroupBounds.prefix_join pa inner) pb) pc⟩

/-- A failed search branches into the original error path; it is not silently
turned into a texture ID or a successful return. I_Error itself is not modeled. -/
theorem missing_path (q : X86Routine.Program)
    (agree : ∀ pc, OriginalTextureWrapper.program pc≠none → q pc=OriginalTextureWrapper.program pc)
    (s t : X86Memory.State) (f g : Option Flags) (n : Nat)
    (inner : X86Routine.Prefix q [] n (search s f) ⟨t,g,0x34759⟩)
    (missing : t.regs 0=(0xffffffff#32)) :
    ∃ k≤n+7, X86Routine.Prefix q [] k ⟨s,f,0x34750⟩
      ⟨(choice t).core,(choice t).flags,0x34760⟩ := by
  obtain ⟨a,ha,pa,_⟩ := X86Routine.run_path (OriginalTextureWrapper.entry_execution s f)
  obtain ⟨b,hb,pb,_⟩ := X86Routine.run_path (OriginalTextureWrapper.gate_execution t g)
  have pa := pa.transfer q [] agree (by simp)
  have pb := pb.transfer q [] agree (by simp)
  have endpoint : choice t=⟨(choice t).core,(choice t).flags,0x34760⟩ := by simp [choice,missing]
  rw [endpoint] at pb
  exact ⟨a+n+b,by omega,OriginalGroupBounds.prefix_join (OriginalGroupBounds.prefix_join pa inner) pb⟩

/-- Saved words are explicit obligations on the inner search's returned memory.
No preservation is inferred merely because a helper is called a lookup. -/
theorem caller_registers (s t : X86Memory.State)
    (stack : t.regs 4=s.regs 4-8)
    (edx : load32 t.memory (t.regs 4)=s.regs 2)
    (ebx : load32 t.memory (t.regs 4+4)=s.regs 3) :
    (result (choice t).core (choice t).flags).core.regs 0=t.regs 0 ∧
    (result (choice t).core (choice t).flags).core.regs 2=s.regs 2 ∧
    (result (choice t).core (choice t).flags).core.regs 3=s.regs 3 ∧
    (result (choice t).core (choice t).flags).core.regs 4=s.regs 4+4 := by
  change load32 t.memory (t.regs 4+(4#32))=s.regs 3 at ebx
  simp [result,OriginalTextureWrapper.restored,choice,put,write,edx,ebx]
  rw [stack]
  simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]

theorem wrapper_frame (s t : X86Memory.State) (f : Option Flags) (a : Word)
    (ebx : Apart a (s.regs 4-4)) (edx : Apart a (s.regs 4-8))
    (call : Apart a (s.regs 4-12))
    (inner : load32 t.memory a=load32 (search s f).core.memory a) :
    load32 (result (choice t).core (choice t).flags).core.memory a=load32 s.memory a := by
  exact inner.trans (OriginalTextureWrapper.entry_frame s f a ebx edx call)
/-- The endpoint has the exact continuation PC expected by the side caller. -/
theorem caller_path (q : X86Routine.Program)
    (agree : ∀ pc, OriginalTextureWrapper.program pc≠none → q pc=OriginalTextureWrapper.program pc)
    (s t : X86Memory.State) (f g : Option Flags) (n : Nat)
    (inner : X86Routine.Prefix q [] n (search s f) ⟨t,g,0x34759⟩)
    (found : t.regs 0≠(0xffffffff#32)) (dest : Word)
    (outside : dest.toNat<0x3476e ∨ 0x34773≤dest.toNat)
    (ret : load32 t.memory (t.regs 4+8)=dest) :
    ∃ k≤n+11, X86Routine.Prefix q [] k ⟨s,f,0x34750⟩
      ⟨(result (choice t).core (choice t).flags).core,(choice t).flags,dest.toNat⟩ := by
  have path := success_path q agree s t f g n inner found dest outside ret
  have endpoint : result (choice t).core (choice t).flags=
      ⟨(result (choice t).core (choice t).flags).core,(choice t).flags,dest.toNat⟩ := by
    change load32 t.memory (t.regs 4+(8#32))=dest at ret
    simp [result,choice,put,write,ret]
  rwa [endpoint] at path

/-- Reduce restored-register values to preservation of two concrete saved words
by the inner search. The wrapper's own stack stores are already discharged. -/
theorem saved_registers (s t : X86Memory.State) (f : Option Flags)
    (stack : t.regs 4=s.regs 4-8)
    (edx : load32 t.memory (s.regs 4-8)=load32 (search s f).core.memory (s.regs 4-8))
    (ebx : load32 t.memory (s.regs 4-4)=load32 (search s f).core.memory (s.regs 4-4)) :
    (result (choice t).core (choice t).flags).core.regs 0=t.regs 0 ∧
    (result (choice t).core (choice t).flags).core.regs 2=s.regs 2 ∧
    (result (choice t).core (choice t).flags).core.regs 3=s.regs 3 ∧
    (result (choice t).core (choice t).flags).core.regs 4=s.regs 4+4 := by
  have slots := OriginalTextureWrapper.saved_slots s f
  apply caller_registers s t stack
  · rw [stack]; exact edx.trans slots.1
  · have offset : t.regs 4+4=s.regs 4-4 := by
      rw [stack]; simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rw [offset]; exact ebx.trans slots.2.1
end Doom.Proofs.E1M1AimTextureWrapper
