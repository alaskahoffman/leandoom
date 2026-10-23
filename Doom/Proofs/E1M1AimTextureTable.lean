import Doom.Proofs.OriginalTextureTable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1AimTextureTable
open Verification X86 X86Memory X86Control BlockSummary
open OriginalTextureDash (prepared nameByte stackMemory)
open OriginalTextureTable (count tested missing comparison)

def emptyResult (s : X86Memory.State) : X86Control.State :=
  ⟨{put (put s 0 0xffffffff) 4 (s.regs 4+4) with memory:=stackMemory s},
    some (logical32 (count (prepared s))),(load32 s.memory (s.regs 4)).toNat⟩

theorem empty_restoration (s : X86Memory.State) :
    OriginalTextureDash.result (missing (tested (prepared s)).core (tested (prepared s)).flags).core
      (missing (tested (prepared s)).core (tested (prepared s)).flags).flags=emptyResult s := by
  obtain ⟨a,b,c,d,e⟩ := OriginalTextureDash.saved_slots s
  have ret := OriginalTextureDash.stack_above s 0 (by simp)
  simp [OriginalTextureDash.result,OriginalTextureDash.restored,missing,tested,prepared,emptyResult,
    put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc] at a b c d e ret ⊢
  simp [a,b,c,d,e,ret]
  funext r
  by_cases r0 : r=0 <;> by_cases r4 : r=4 <;> by_cases r3 : r=3 <;>
    by_cases r1 : r=1 <;> by_cases r2 : r=2 <;> by_cases r6 : r=6 <;>
    by_cases r7 : r=7 <;> simp_all [write]

/-- The signed nonpositive-count branch returns -1 through original instructions.
Both the name byte and count describe reads after the original prologue writes. -/
theorem empty_path (q : X86Routine.Program)
    (dashCode : ∀ pc, OriginalTextureDash.program pc≠none → q pc=OriginalTextureDash.program pc)
    (tableCode : ∀ pc, OriginalTextureTable.program pc≠none → q pc=OriginalTextureTable.program pc)
    (s : X86Memory.State) (f : Option Flags)
    (named : nameByte s≠(0x2d#8)) (empty : (count (prepared s)).toInt≤0)
    (dest : Word) (outside : dest.toNat<0x34741 ∨ 0x34747≤dest.toNat)
    (ret : load32 s.memory (s.regs 4)=dest) :
    ∃ n≤19, X86Routine.Prefix q [] n ⟨s,f,0x346f0⟩ (emptyResult s) := by
  obtain ⟨a,ha,pa,_⟩ := X86Routine.run_path (OriginalTextureDash.entry_execution s f)
  have entry : OriginalTextureDash.gate s=⟨prepared s,(OriginalTextureDash.gate s).flags,0x34700⟩ := by
    simp [OriginalTextureDash.gate,named]
  rw [entry] at pa
  obtain ⟨b,hb,pb,_⟩ := X86Routine.run_path (OriginalTextureTable.gate_execution (prepared s) (OriginalTextureDash.gate s).flags)
  have gate : tested (prepared s)=⟨(tested (prepared s)).core,(tested (prepared s)).flags,0x3473c⟩ := by
    simp [tested,empty]
  rw [gate] at pb
  obtain ⟨c,hc,pc,_⟩ := X86Routine.run_path (OriginalTextureTable.missing_execution
    (tested (prepared s)).core (tested (prepared s)).flags)
  have word : load32 (missing (tested (prepared s)).core (tested (prepared s)).flags).core.memory
      ((missing (tested (prepared s)).core (tested (prepared s)).flags).core.regs 4+20)=dest := by
    have h : load32 (stackMemory s) (s.regs 4)=load32 s.memory (s.regs 4) := by
      simpa using OriginalTextureDash.stack_above s 0 (by simp)
    simpa [missing,tested,prepared,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc] using h.trans ret
  obtain ⟨d,hd,pd,_⟩ := X86Routine.run_path (OriginalTextureDash.return_execution
    (missing (tested (prepared s)).core (tested (prepared s)).flags).core
    (missing (tested (prepared s)).core (tested (prepared s)).flags).flags dest outside word)
  have pa := pa.transfer q [] dashCode (by simp)
  have pb := pb.transfer q [] tableCode (by simp)
  have pc := pc.transfer q [] tableCode (by simp)
  have pd := pd.transfer q [] dashCode (by simp)
  rw [empty_restoration] at pd
  exact ⟨a+b+c+d,by omega,OriginalGroupBounds.prefix_join
    (OriginalGroupBounds.prefix_join (OriginalGroupBounds.prefix_join pa pb) pc) pd⟩

/-- Positive counts reach the real bounded-comparison CALL with table index zero.
The comparison body is not supplied by an oracle and is not executed here. -/
theorem first_comparison_path (q : X86Routine.Program)
    (dashCode : ∀ pc, OriginalTextureDash.program pc≠none → q pc=OriginalTextureDash.program pc)
    (tableCode : ∀ pc, OriginalTextureTable.program pc≠none → q pc=OriginalTextureTable.program pc)
    (s : X86Memory.State) (f : Option Flags)
    (named : nameByte s≠(0x2d#8)) (positive : 0<(count (prepared s)).toInt) :
    ∃ n≤18, X86Routine.Prefix q [] n ⟨s,f,0x346f0⟩ (comparison (tested (prepared s)).core) := by
  obtain ⟨a,ha,pa,_⟩ := X86Routine.run_path (OriginalTextureDash.entry_execution s f)
  have entry : OriginalTextureDash.gate s=⟨prepared s,(OriginalTextureDash.gate s).flags,0x34700⟩ := by
    simp [OriginalTextureDash.gate,named]
  rw [entry] at pa
  obtain ⟨b,hb,pb,_⟩ := X86Routine.run_path (OriginalTextureTable.gate_execution (prepared s) (OriginalTextureDash.gate s).flags)
  have gate : tested (prepared s)=⟨(tested (prepared s)).core,(tested (prepared s)).flags,0x3470c⟩ := by
    simp [tested,show ¬(count (prepared s)).toInt≤0 by omega]
  rw [gate] at pb
  obtain ⟨c,hc,pc,_⟩ := X86Routine.run_path (OriginalTextureTable.comparison_execution
    (tested (prepared s)).core (tested (prepared s)).flags)
  have pa := pa.transfer q [] dashCode (by simp)
  have pb := pb.transfer q [] tableCode (by simp)
  have pc := pc.transfer q [] tableCode (by simp)
  exact ⟨a+b+c,by omega,OriginalGroupBounds.prefix_join (OriginalGroupBounds.prefix_join pa pb) pc⟩

theorem first_arguments (s : X86Memory.State) :
    (comparison (tested (prepared s)).core).core.regs 0=
      load32 (stackMemory s) (load32 (stackMemory s) 0x300e0) ∧
    (comparison (tested (prepared s)).core).core.regs 2=s.regs 0 ∧
    (comparison (tested (prepared s)).core).core.regs 3=8 ∧
    (comparison (tested (prepared s)).core).core.regs 1=0 ∧
    (comparison (tested (prepared s)).core).core.regs 6=0 ∧
    (comparison (tested (prepared s)).core).core.regs 4=s.regs 4-24 := by
  simp [comparison,OriginalTextureTable.firstTexture,tested,prepared,X86Routine.pushWord,put,write,BitVec.sub_sub]

theorem empty_registers (s : X86Memory.State) :
    (emptyResult s).core.regs 0=0xffffffff ∧ (emptyResult s).core.regs 4=s.regs 4+4 ∧
    (∀ r, r≠0 → r≠4 → (emptyResult s).core.regs r=s.regs r) := by
  simp [emptyResult,put,write]
  intro r h0 h4
  simp [h0,h4]

theorem empty_frame (s : X86Memory.State) (a : Word)
    (safe : ∀ off∈[(4#32),8,12,16,20], Apart a (s.regs 4-off)) :
    load32 (emptyResult s).core.memory a=load32 s.memory a := by
  exact OriginalTextureDash.stack_frame s a safe

/-- A real nonpositive-count lookup reaches the wrapper's error-path entry;
there is no assumed inner execution, and no claim about I_Error's body. -/
theorem wrapper_empty_path (q : X86Routine.Program)
    (dashCode : ∀ pc, OriginalTextureDash.program pc≠none → q pc=OriginalTextureDash.program pc)
    (tableCode : ∀ pc, OriginalTextureTable.program pc≠none → q pc=OriginalTextureTable.program pc)
    (wrapper : ∀ pc, OriginalTextureWrapper.program pc≠none → q pc=OriginalTextureWrapper.program pc)
    (s : X86Memory.State) (f : Option Flags)
    (named : nameByte (OriginalTextureWrapper.search s f).core≠(0x2d#8))
    (empty : (count (prepared (OriginalTextureWrapper.search s f).core)).toInt≤0) :
    ∃ n≤26, X86Routine.Prefix q [] n ⟨s,f,0x34750⟩
      ⟨(OriginalTextureWrapper.choice (emptyResult (OriginalTextureWrapper.search s f).core).core).core,
        (OriginalTextureWrapper.choice (emptyResult (OriginalTextureWrapper.search s f).core).core).flags,0x34760⟩ := by
  have args := OriginalTextureWrapper.entry_arguments s f
  obtain ⟨n,hn,path⟩ := empty_path q dashCode tableCode (OriginalTextureWrapper.search s f).core f
    named empty 0x34759 (by decide) args.2.2.2
  have ipc : (emptyResult (OriginalTextureWrapper.search s f).core).pc=0x34759 := by
    change (load32 (OriginalTextureWrapper.search s f).core.memory
      ((OriginalTextureWrapper.search s f).core.regs 4)).toNat=0x34759
    rw [args.2.2.2]; rfl
  have ieq : emptyResult (OriginalTextureWrapper.search s f).core=
      ⟨(emptyResult (OriginalTextureWrapper.search s f).core).core,
        (emptyResult (OriginalTextureWrapper.search s f).core).flags,0x34759⟩ := by
    cases h : emptyResult (OriginalTextureWrapper.search s f).core
    simp_all
  rw [ieq] at path
  obtain ⟨k,hk,pk⟩ := E1M1AimTextureWrapper.missing_path q wrapper s
    (emptyResult (OriginalTextureWrapper.search s f).core).core f
    (emptyResult (OriginalTextureWrapper.search s f).core).flags n path
    (by simp [emptyResult,put,write])
  exact ⟨k,by omega,pk⟩
end Doom.Proofs.E1M1AimTextureTable
