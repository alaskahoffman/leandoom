import Doom.Proofs.E1M1AimTextureSearch
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1AimTextureLookup
open Verification X86 X86Memory X86Control BlockSummary
open E1M1AimTextureSearch (joined lift_run dash_agreement table_agreement wrapper_agreement)

/-- Dispatch uses the actual post-save byte and count, not pristine names. -/
def lookup (s : X86Memory.State) : X86Control.State :=
  if OriginalTextureDash.nameByte s=(0x2d#8) then OriginalTextureDash.returned s
  else if (OriginalTextureTable.count (OriginalTextureDash.prepared s)).toInt≤0 then
    E1M1AimTextureTable.emptyResult s
  else E1M1AimTextureSearch.namedResult s

theorem lookup_execution (s : X86Memory.State) (f : Option Flags) (dest : Word)
    (outside : dest.toNat<0x34741 ∨ 0x34747≤dest.toNat)
    (ret : load32 s.memory (s.regs 4)=dest) :
    ∃ k≤202*2147483647+19, X86ByteRoutine.Prefix joined [] k
      ⟨s,f,0x346f0⟩ (lookup s) := by
  by_cases dash : OriginalTextureDash.nameByte s=(0x2d#8)
  · obtain ⟨a,ha,pa⟩ := lift_run _ _ _ _ _ (OriginalTextureDash.entry_execution s f) dash_agreement
    have gate : OriginalTextureDash.gate s=⟨OriginalTextureDash.prepared s,(OriginalTextureDash.gate s).flags,0x346fc⟩ := by
      simp [OriginalTextureDash.gate,dash]
    rw [gate] at pa
    obtain ⟨b,hb,pb⟩ := lift_run _ _ _ _ _ (OriginalTextureDash.zero_execution (OriginalTextureDash.prepared s) (OriginalTextureDash.gate s).flags) dash_agreement
    have word : load32 (OriginalTextureDash.zeroed (OriginalTextureDash.prepared s)).core.memory
        ((OriginalTextureDash.zeroed (OriginalTextureDash.prepared s)).core.regs 4+20)=dest := by
      have h := OriginalTextureDash.stack_above s 0 (by simp)
      simpa [OriginalTextureDash.zeroed,OriginalTextureDash.prepared,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc] using h.trans (by simpa using ret)
    obtain ⟨c,hc,pc⟩ := lift_run _ _ _ _ _ (OriginalTextureDash.return_execution
      (OriginalTextureDash.zeroed (OriginalTextureDash.prepared s)).core
      (OriginalTextureDash.zeroed (OriginalTextureDash.prepared s)).flags dest outside word) dash_agreement
    rw [OriginalTextureDash.restored_prepared] at pc
    exact ⟨a+b+c,by omega,by simpa only [lookup,dash,↓reduceIte] using (pa.trans pb).trans pc⟩
  · by_cases empty : (OriginalTextureTable.count (OriginalTextureDash.prepared s)).toInt≤0
    · obtain ⟨a,ha,pa⟩ := lift_run _ _ _ _ _ (OriginalTextureDash.entry_execution s f) dash_agreement
      have entry : OriginalTextureDash.gate s=⟨OriginalTextureDash.prepared s,(OriginalTextureDash.gate s).flags,0x34700⟩ := by
        simp [OriginalTextureDash.gate,dash]
      rw [entry] at pa
      obtain ⟨b,hb,pb⟩ := lift_run _ _ _ _ _ (OriginalTextureTable.gate_execution (OriginalTextureDash.prepared s) (OriginalTextureDash.gate s).flags) table_agreement
      have gate : OriginalTextureTable.tested (OriginalTextureDash.prepared s)=
          ⟨(OriginalTextureTable.tested (OriginalTextureDash.prepared s)).core,(OriginalTextureTable.tested (OriginalTextureDash.prepared s)).flags,0x3473c⟩ := by
        simp [OriginalTextureTable.tested,empty]
      rw [gate] at pb
      obtain ⟨c,hc,pc⟩ := lift_run _ _ _ _ _ (OriginalTextureTable.missing_execution
        (OriginalTextureTable.tested (OriginalTextureDash.prepared s)).core (OriginalTextureTable.tested (OriginalTextureDash.prepared s)).flags) table_agreement
      have word : load32 (OriginalTextureTable.missing (OriginalTextureTable.tested (OriginalTextureDash.prepared s)).core (OriginalTextureTable.tested (OriginalTextureDash.prepared s)).flags).core.memory
          ((OriginalTextureTable.missing (OriginalTextureTable.tested (OriginalTextureDash.prepared s)).core (OriginalTextureTable.tested (OriginalTextureDash.prepared s)).flags).core.regs 4+20)=dest := by
        have h := OriginalTextureDash.stack_above s 0 (by simp)
        simpa [OriginalTextureTable.missing,OriginalTextureTable.tested,OriginalTextureDash.prepared,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc] using h.trans (by simpa using ret)
      obtain ⟨d,hd,pd⟩ := lift_run _ _ _ _ _ (OriginalTextureDash.return_execution
        (OriginalTextureTable.missing (OriginalTextureTable.tested (OriginalTextureDash.prepared s)).core (OriginalTextureTable.tested (OriginalTextureDash.prepared s)).flags).core
        (OriginalTextureTable.missing (OriginalTextureTable.tested (OriginalTextureDash.prepared s)).core (OriginalTextureTable.tested (OriginalTextureDash.prepared s)).flags).flags dest outside word) dash_agreement
      rw [E1M1AimTextureTable.empty_restoration] at pd
      exact ⟨a+b+c+d,by omega,by simpa only [lookup,dash,empty,↓reduceIte] using ((pa.trans pb).trans pc).trans pd⟩
    · obtain ⟨k,hk,hp⟩ := E1M1AimTextureSearch.named_execution s f dash (by omega)
      exact ⟨k,by omega,by simpa only [lookup,dash,empty,↓reduceIte] using hp⟩

theorem lookup_return (s : X86Memory.State) :
    (lookup s).pc=(load32 s.memory (s.regs 4)).toNat ∧
    (lookup s).core.regs 4=s.regs 4+4 := by
  unfold lookup
  split
  · simp [OriginalTextureDash.returned,put,write]
  · split
    · simp [E1M1AimTextureTable.emptyResult,put,write]
    · exact E1M1AimTextureSearch.named_return s

theorem lookup_registers (s : X86Memory.State) (r : Reg) (h0 : r≠0) (h4 : r≠4) :
    (lookup s).core.regs r=s.regs r := by
  unfold lookup
  split
  · simp [OriginalTextureDash.returned,put,write,h0,h4]
  · split
    · exact (E1M1AimTextureTable.empty_registers s).2.2 r h0 h4
    · exact E1M1AimTextureSearch.named_registers s r h0 h4
theorem lookup_above (s : X86Memory.State) (off : Word) (member : off∈[(0#32),4,8,12]) :
    load32 (lookup s).core.memory (s.regs 4+off)=load32 s.memory (s.regs 4+off) := by
  unfold lookup
  split
  · exact OriginalTextureDash.stack_above s off member
  · split
    · exact OriginalTextureDash.stack_above s off member
    · exact E1M1AimTextureSearch.named_above s off member

theorem lookup_frame (s : X86Memory.State) (a : Word)
    (safe : ∀ off∈[(4#32),8,12,16,20,24,28], Apart a (s.regs 4-off)) :
    load32 (lookup s).core.memory a=load32 s.memory a := by
  have saves : ∀ off∈[(4#32),8,12,16,20], Apart a (s.regs 4-off) := by
    intro off mem
    apply safe off
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl <;> simp
  have frame := OriginalTextureDash.stack_frame s a saves
  unfold lookup
  split
  · exact frame
  · split
    · exact frame
    · have callSafe : Apart a ((E1M1AimTextureSearch.namedStart s).regs 4-4) := by
        simpa [E1M1AimTextureSearch.namedStart,OriginalTextureTable.tested,OriginalTextureDash.prepared,put,write,BitVec.sub_sub] using safe 24 (by simp)
      have pushSafe : Apart a ((E1M1AimTextureSearch.namedStart s).regs 4-8) := by
        simpa [E1M1AimTextureSearch.namedStart,OriginalTextureTable.tested,OriginalTextureDash.prepared,put,write,BitVec.sub_sub] using safe 28 (by simp)
      exact (OriginalTextureSearch.search_frame 2147483647 (E1M1AimTextureSearch.namedStart s) (some (logical32 0)) a callSafe pushSafe).trans frame

def inner (s : X86Memory.State) (f : Option Flags) := lookup (OriginalTextureWrapper.search s f).core
def wrapped (s : X86Memory.State) (f : Option Flags) :=
  let t := inner s f
  let u := OriginalTextureWrapper.choice t.core
  if t.core.regs 0=(0xffffffff#32) then u else OriginalTextureWrapper.result u.core u.flags

theorem inner_return (s : X86Memory.State) (f : Option Flags) :
    (inner s f).pc=0x34759 ∧ (inner s f).core.regs 4=s.regs 4-8 := by
  have h := lookup_return (OriginalTextureWrapper.search s f).core
  simpa [inner,OriginalTextureWrapper.search,OriginalTextureWrapper.saved,X86Routine.pushWord,put,write,load_store,BitVec.sub_eq_add_neg,BitVec.add_assoc] using h

theorem wrapper_words (s : X86Memory.State) (f : Option Flags) :
    load32 (inner s f).core.memory ((inner s f).core.regs 4)=s.regs 2 ∧
    load32 (inner s f).core.memory ((inner s f).core.regs 4+4)=s.regs 3 ∧
    load32 (inner s f).core.memory ((inner s f).core.regs 4+8)=load32 s.memory (s.regs 4) := by
  have a := lookup_above (OriginalTextureWrapper.search s f).core 4 (by simp)
  have b := lookup_above (OriginalTextureWrapper.search s f).core 8 (by simp)
  have c := lookup_above (OriginalTextureWrapper.search s f).core 12 (by simp)
  have sp : (OriginalTextureWrapper.search s f).core.regs 4=s.regs 4-12 := by
    simp [OriginalTextureWrapper.search,OriginalTextureWrapper.saved,X86Routine.pushWord,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc]
  rw [sp] at a b c
  have saved := OriginalTextureWrapper.saved_slots s f
  simp [BitVec.sub_eq_add_neg,BitVec.add_assoc] at a b c saved
  rw [(inner_return s f).2]
  simpa [inner,BitVec.sub_eq_add_neg,BitVec.add_assoc] using
    And.intro (a.trans saved.1) (And.intro (b.trans saved.2.1) (c.trans saved.2.2))

/-- Every name/count branch executes; failure reaches the error arm, not I_Error. -/
theorem wrapper_execution (s : X86Memory.State) (f : Option Flags)
    (dest : Word) (outside : dest.toNat<0x3476e ∨ 0x34773≤dest.toNat)
    (ret : load32 s.memory (s.regs 4)=dest) :
    ∃ k≤202*2147483647+30, X86ByteRoutine.Prefix joined [] k ⟨s,f,0x34750⟩ (wrapped s f) := by
  obtain ⟨a,ha,pa⟩ := lift_run _ _ _ _ _ (OriginalTextureWrapper.entry_execution s f) wrapper_agreement
  obtain ⟨b,hb,pb⟩ := lookup_execution (OriginalTextureWrapper.search s f).core f 0x34759 (by decide)
    (OriginalTextureWrapper.entry_arguments s f).2.2.2
  have middle : ⟨(OriginalTextureWrapper.search s f).core,f,0x346f0⟩=OriginalTextureWrapper.search s f := rfl
  rw [middle] at pb
  change X86ByteRoutine.Prefix joined [] b (OriginalTextureWrapper.search s f) (inner s f) at pb
  obtain ⟨c,hc,pc⟩ := lift_run _ _ _ _ _ (OriginalTextureWrapper.gate_execution (inner s f).core (inner s f).flags) wrapper_agreement
  have seam : ⟨(inner s f).core,(inner s f).flags,0x34759⟩=inner s f := by
    have h := (inner_return s f).1
    cases e : inner s f
    simp_all
  rw [seam] at pc
  have path := (pa.trans pb).trans pc
  by_cases missing : (inner s f).core.regs 0=(0xffffffff#32)
  · exact ⟨a+b+c,by omega,by simpa only [wrapped,missing,↓reduceIte] using path⟩
  · have returns : load32 (OriginalTextureWrapper.choice (inner s f).core).core.memory
        ((OriginalTextureWrapper.choice (inner s f).core).core.regs 4+8)=dest := by
      simpa [OriginalTextureWrapper.choice,put,write] using (wrapper_words s f).2.2.trans ret
    obtain ⟨d,hd,pd⟩ := lift_run _ _ _ _ _
      (OriginalTextureWrapper.return_execution (OriginalTextureWrapper.choice (inner s f).core).core
        (OriginalTextureWrapper.choice (inner s f).core).flags dest outside returns) wrapper_agreement
    have seam : ⟨(OriginalTextureWrapper.choice (inner s f).core).core,
        (OriginalTextureWrapper.choice (inner s f).core).flags,0x3476e⟩=OriginalTextureWrapper.choice (inner s f).core := by
      simp [OriginalTextureWrapper.choice,missing]
    rw [seam] at pd
    exact ⟨a+b+c+d,by omega,by simpa only [wrapped,missing,↓reduceIte] using path.trans pd⟩

theorem wrapper_outcomes (s : X86Memory.State) (f : Option Flags) :
    ((inner s f).core.regs 0=0xffffffff → (wrapped s f).pc=0x34760) ∧
    ((inner s f).core.regs 0≠0xffffffff →
      (wrapped s f).pc=(load32 s.memory (s.regs 4)).toNat ∧
      (wrapped s f).core.regs 0=(inner s f).core.regs 0 ∧
      (wrapped s f).core.regs 2=s.regs 2 ∧
      (wrapped s f).core.regs 3=s.regs 3 ∧
      (wrapped s f).core.regs 4=s.regs 4+4) := by
  constructor
  · intro h
    have h : (inner s f).core.regs 0=(0xffffffff#32) := h
    simp [wrapped,h,OriginalTextureWrapper.choice]
  · intro h
    have h : (inner s f).core.regs 0≠(0xffffffff#32) := h
    have words := wrapper_words s f
    have sp := (inner_return s f).2
    simp only [wrapped,h,↓reduceIte]
    have regs := E1M1AimTextureWrapper.caller_registers s (inner s f).core sp words.1 words.2.1
    refine ⟨?_,regs⟩
    simpa [OriginalTextureWrapper.result,OriginalTextureWrapper.choice,put,write] using congrArg BitVec.toNat words.2.2

theorem wrapper_registers (s : X86Memory.State) (f : Option Flags)
    (success : (inner s f).core.regs 0≠0xffffffff) (r : Reg) (h0 : r≠0) (h4 : r≠4) :
    (wrapped s f).core.regs r=s.regs r := by
  have outcome := (wrapper_outcomes s f).2 success
  by_cases h2 : r=2
  · subst r; exact outcome.2.2.1
  by_cases h3 : r=3
  · subst r; exact outcome.2.2.2.1
  have h := lookup_registers (OriginalTextureWrapper.search s f).core r h0 h4
  have success : (inner s f).core.regs 0≠(0xffffffff#32) := success
  simp only [wrapped,success,↓reduceIte]
  simpa [OriginalTextureWrapper.result,OriginalTextureWrapper.restored,OriginalTextureWrapper.choice,
    inner,OriginalTextureWrapper.search,OriginalTextureWrapper.saved,X86Routine.pushWord,put,write,h0,h2,h3,h4] using h

theorem wrapper_frame (s : X86Memory.State) (f : Option Flags) (a : Word)
    (safe : ∀ off∈[(4#32),8,12,16,20,24,28,32,36,40], Apart a (s.regs 4-off)) :
    load32 (wrapped s f).core.memory a=load32 s.memory a := by
  have frame := lookup_frame (OriginalTextureWrapper.search s f).core a (by
    intro off member
    have mem : 12+off∈[(4#32),8,12,16,20,24,28,32,36,40] := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    simpa [OriginalTextureWrapper.search,OriginalTextureWrapper.saved,X86Routine.pushWord,put,write,BitVec.sub_sub] using safe (12+off) mem)
  have pre : load32 (OriginalTextureWrapper.search s f).core.memory a=load32 s.memory a := by
    have eq : (OriginalTextureWrapper.search s f).core.memory=
        store32 (store32 (store32 s.memory (s.regs 4-4) (s.regs 3)) (s.regs 4-8) (s.regs 2)) (s.regs 4-12) 0x34759 := by
      simp [OriginalTextureWrapper.search,OriginalTextureWrapper.saved,X86Routine.pushWord,put,write,BitVec.sub_sub]
    rw [eq,load_store_apart _ _ _ _ (safe 12 (by simp)),load_store_apart _ _ _ _ (safe 8 (by simp)),load_store_apart _ _ _ _ (safe 4 (by simp))]
  have mem : (wrapped s f).core.memory=(inner s f).core.memory := by
    dsimp only [wrapped]
    split <;> rfl
  rw [mem]
  exact frame.trans pre
end Doom.Proofs.E1M1AimTextureLookup
