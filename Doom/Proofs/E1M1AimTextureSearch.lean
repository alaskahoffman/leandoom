import Doom.Proofs.OriginalTextureSearch
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1AimTextureSearch
open Verification X86 X86Memory X86Control BlockSummary

def joined : X86ByteRoutine.Program := fun pc =>
  if 0x346f0≤pc ∧ pc<0x34700 then X86ByteRoutine.liftProgram OriginalTextureDash.program pc
  else if 0x34750≤pc ∧ pc<0x34773 then X86ByteRoutine.liftProgram OriginalTextureWrapper.program pc
  else OriginalTextureSearch.program pc

theorem search_agreement (pc : Nat) (h : OriginalTextureSearch.program pc≠none) :
    joined pc=OriginalTextureSearch.program pc := by
  have outside : ¬(0x346f0≤pc ∧ pc<0x34700) ∧ ¬(0x34750≤pc ∧ pc<0x34773) := by
    by_cases inside : (0x346f0≤pc ∧ pc<0x34700) ∨ (0x34750≤pc ∧ pc<0x34773)
    · have b1 : ¬(0x4198c≤pc ∧ pc<0x41999) := by omega
      have b2 : ¬(0x419b5≤pc ∧ pc<0x419ce) := by omega
      have b3 : ¬(0x41999≤pc ∧ pc<0x419b5) := by omega
      have b4 : ¬(0x34700≤pc ∧ pc<0x34722) := by omega
      have b5 : ¬(0x3473c≤pc ∧ pc<0x34741) := by omega
      have b6 : ¬(0x34722≤pc ∧ pc<0x3473c) := by omega
      have b7 : ¬(0x34741≤pc ∧ pc<0x34747) := by omega
      simp [OriginalTextureSearch.program,OriginalTextureSearch.bytesProgram,
        OriginalTextureComparator.joined,OriginalTextureComparator.combine,
        OriginalTextureIteration.program,OriginalTextureIteration.bytesProgram,
        OriginalTextureFold.bytesProgram,OriginalTextureTable.program,
        OriginalTextureTable.bytesProgram,X86ByteRoutine.liftProgram,b1,b2,b3,b4,b5,b6,b7] at h
    · omega
  simp [joined,outside.1,outside.2]

theorem dash_agreement (pc : Nat) (h : (X86ByteRoutine.liftProgram OriginalTextureDash.program) pc≠none) :
    joined pc=(X86ByteRoutine.liftProgram OriginalTextureDash.program) pc := by
  by_cases entry : 0x346f0≤pc ∧ pc<0x34700
  · simp [joined,entry]
  · have restore : 0x34741≤pc ∧ pc<0x34747 := by
      by_cases r : 0x34741≤pc ∧ pc<0x34747
      · exact r
      · simp [X86ByteRoutine.liftProgram,OriginalTextureDash.program,OriginalTextureDash.bytesProgram,entry,r] at h
    have cases : pc=0x34741 ∨ pc=0x34742 ∨ pc=0x34743 ∨ pc=0x34744 ∨ pc=0x34745 ∨ pc=0x34746 := by omega
    rcases cases with rfl|rfl|rfl|rfl|rfl|rfl <;> decide

theorem table_agreement (pc : Nat) (h : (X86ByteRoutine.liftProgram OriginalTextureTable.program) pc≠none) :
    joined pc=(X86ByteRoutine.liftProgram OriginalTextureTable.program) pc := by
  have a := OriginalTextureComparator.joined_table pc h
  have b := OriginalTextureSearch.prior_agreement pc (by rw [a]; exact h)
  exact (search_agreement pc (by rw [b,a]; exact h)).trans (b.trans a)

theorem wrapper_agreement (pc : Nat) (h : (X86ByteRoutine.liftProgram OriginalTextureWrapper.program) pc≠none) :
    joined pc=(X86ByteRoutine.liftProgram OriginalTextureWrapper.program) pc := by
  have range : 0x34750≤pc ∧ pc<0x34773 := by
    by_cases r : 0x34750≤pc ∧ pc<0x34773
    · exact r
    · simp [X86ByteRoutine.liftProgram,OriginalTextureWrapper.program,OriginalTextureWrapper.bytesProgram,r] at h
  have no : ¬(0x346f0≤pc ∧ pc<0x34700) := by omega
  simp [joined,no,range]

/-- Reuse old executed paths without changing the old instruction semantics. -/
theorem lift_run (p : X86Routine.Program) (exits : List Nat) (n : Nat) (s t : X86Control.State)
    (run : X86Routine.run p exits n s=some t)
    (agree : ∀ pc, (X86ByteRoutine.liftProgram p) pc≠none → joined pc=(X86ByteRoutine.liftProgram p) pc) :
    ∃ k≤n, X86ByteRoutine.Prefix joined [] k s t := by
  have h : X86ByteRoutine.run (X86ByteRoutine.liftProgram p) exits n s=some t := by
    rw [X86ByteRoutine.run_lift]; exact run
  obtain ⟨k,hk,hp,_⟩ := X86ByteRoutine.run_path h
  exact ⟨k,hk,hp.transfer joined [] agree (by simp)⟩

def namedStart (s : X86Memory.State) := put (OriginalTextureTable.tested (OriginalTextureDash.prepared s)).core 6 0
def namedResult (s : X86Memory.State) := OriginalTextureSearch.search 2147483647 (namedStart s) (some (logical32 0))

theorem named_execution (s : X86Memory.State) (f : Option Flags)
    (named : OriginalTextureDash.nameByte s≠0x2d)
    (positive : 0<(OriginalTextureTable.count (OriginalTextureDash.prepared s)).toInt) :
    ∃ k≤202*2147483647+13, X86ByteRoutine.Prefix joined [] k ⟨s,f,0x346f0⟩ (namedResult s) := by
  obtain ⟨a,ha,pa⟩ := lift_run _ _ _ _ _ (OriginalTextureDash.entry_execution s f) dash_agreement
  have gate : OriginalTextureDash.gate s=⟨OriginalTextureDash.prepared s,(OriginalTextureDash.gate s).flags,0x34700⟩ := by
    have h : OriginalTextureDash.nameByte s≠(0x2d#8) := named
    simp [OriginalTextureDash.gate,h]
  rw [gate] at pa
  obtain ⟨b,hb,pb⟩ := lift_run _ _ _ _ _ (OriginalTextureTable.gate_execution (OriginalTextureDash.prepared s) (OriginalTextureDash.gate s).flags) table_agreement
  have tested : OriginalTextureTable.tested (OriginalTextureDash.prepared s)=
      ⟨(OriginalTextureTable.tested (OriginalTextureDash.prepared s)).core,(OriginalTextureTable.tested (OriginalTextureDash.prepared s)).flags,0x3470c⟩ := by
    simp only [OriginalTextureTable.tested]
    rw [if_neg (by omega)]
  rw [tested] at pb
  have init : X86ByteRoutine.Prefix joined [] 1
      ⟨(OriginalTextureTable.tested (OriginalTextureDash.prepared s)).core,(OriginalTextureTable.tested (OriginalTextureDash.prepared s)).flags,0x3470c⟩
      ⟨namedStart s,some (logical32 0),0x3470e⟩ := by
    apply X86ByteRoutine.Prefix.step (middle := ⟨namedStart s,some (logical32 0),0x3470e⟩) (by simp) (show joined 0x3470c=some (.base (.xorRegister 6 6),2) by decide) (by simp [namedStart,X86ByteRoutine.execute,X86Routine.execute,logical32])
    exact .nil _
  obtain ⟨c,hc,pc⟩ := OriginalTextureSearch.full_search_execution (namedStart s) (some (logical32 0)) (by simp [namedStart,OriginalTextureTable.tested,put,write])
  exact ⟨a+b+1+c,by omega,((pa.trans pb).trans init).trans (pc.transfer joined [] search_agreement (by simp))⟩

theorem named_return (s : X86Memory.State) :
    (namedResult s).pc=(load32 s.memory (s.regs 4)).toNat ∧
    (namedResult s).core.regs 4=s.regs 4+4 := by
  have h := OriginalTextureSearch.search_return 2147483647 (namedStart s) (some (logical32 0)) (by decide) (by simp [namedStart,OriginalTextureTable.tested,put,write])
  have mem := OriginalTextureDash.stack_above s 0 (by simp)
  simp at mem
  simpa [namedResult,namedStart,OriginalTextureTable.tested,OriginalTextureDash.prepared,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,mem] using And.intro h.1 h.2.1

theorem named_above (s : X86Memory.State) (off : Word) (member : off∈[(0#32),4,8,12]) :
    load32 (namedResult s).core.memory (s.regs 4+off)=load32 s.memory (s.regs 4+off) := by
  have slot : off+20∈[(0#32),4,8,12,16,20,24,28,32] := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl <;> decide
  have sep := OriginalTextureSearch.slot_separation ((namedStart s).regs 4) (off+20) slot
  have eq : (namedStart s).regs 4+(off+20)=s.regs 4+off := by
    rw [BitVec.add_comm off 20]
    rw [← BitVec.add_assoc]
    simp [namedStart,OriginalTextureTable.tested,OriginalTextureDash.prepared,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc]
  rw [eq] at sep
  have h := OriginalTextureSearch.search_frame 2147483647 (namedStart s) (some (logical32 0)) (s.regs 4+off) sep.1 sep.2
  exact h.trans (OriginalTextureDash.stack_above s off member)

def innerResult (s : X86Memory.State) (f : Option Flags) := namedResult (OriginalTextureWrapper.search s f).core
def wrappedResult (s : X86Memory.State) (f : Option Flags) :=
  let t := innerResult s f
  let u := OriginalTextureWrapper.choice t.core
  if t.core.regs 0=(0xffffffff#32) then u else OriginalTextureWrapper.result u.core u.flags

theorem inner_return (s : X86Memory.State) (f : Option Flags) :
    (innerResult s f).pc=0x34759 ∧ (innerResult s f).core.regs 4=s.regs 4-8 := by
  have h := named_return (OriginalTextureWrapper.search s f).core
  simpa [innerResult,OriginalTextureWrapper.search,OriginalTextureWrapper.saved,X86Routine.pushWord,put,write,load_store,BitVec.sub_eq_add_neg,BitVec.add_assoc] using h

theorem wrapper_words (s : X86Memory.State) (f : Option Flags) :
    load32 (innerResult s f).core.memory ((innerResult s f).core.regs 4)=s.regs 2 ∧
    load32 (innerResult s f).core.memory ((innerResult s f).core.regs 4+4)=s.regs 3 ∧
    load32 (innerResult s f).core.memory ((innerResult s f).core.regs 4+8)=load32 s.memory (s.regs 4) := by
  have a := named_above (OriginalTextureWrapper.search s f).core 4 (by simp)
  have b := named_above (OriginalTextureWrapper.search s f).core 8 (by simp)
  have c := named_above (OriginalTextureWrapper.search s f).core 12 (by simp)
  have sp : (OriginalTextureWrapper.search s f).core.regs 4=s.regs 4-12 := by
    simp [OriginalTextureWrapper.search,OriginalTextureWrapper.saved,X86Routine.pushWord,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc]
  rw [sp] at a b c
  have saved := OriginalTextureWrapper.saved_slots s f
  simp [BitVec.sub_eq_add_neg,BitVec.add_assoc] at a b c saved
  rw [(inner_return s f).2]
  simpa [innerResult,BitVec.sub_eq_add_neg,BitVec.add_assoc] using
    And.intro (a.trans saved.1) (And.intro (b.trans saved.2.1) (c.trans saved.2.2))

/-- Both named-search outcomes execute: matched lookup returns to the caller;
exhaustion branches to the original error arm at 0x34760, before I_Error. -/
theorem wrapper_execution (s : X86Memory.State) (f : Option Flags)
    (named : OriginalTextureDash.nameByte (OriginalTextureWrapper.search s f).core≠0x2d)
    (positive : 0<(OriginalTextureTable.count (OriginalTextureDash.prepared (OriginalTextureWrapper.search s f).core)).toInt)
    (dest : Word) (outside : dest.toNat<0x3476e ∨ 0x34773≤dest.toNat)
    (ret : load32 s.memory (s.regs 4)=dest) :
    ∃ k≤202*2147483647+24, X86ByteRoutine.Prefix joined [] k ⟨s,f,0x34750⟩ (wrappedResult s f) := by
  obtain ⟨a,ha,pa⟩ := lift_run _ _ _ _ _ (OriginalTextureWrapper.entry_execution s f) wrapper_agreement
  obtain ⟨b,hb,pb⟩ := named_execution (OriginalTextureWrapper.search s f).core f named positive
  have middle : ⟨(OriginalTextureWrapper.search s f).core,f,0x346f0⟩=OriginalTextureWrapper.search s f := rfl
  rw [middle] at pb
  have inner : namedResult (OriginalTextureWrapper.search s f).core=innerResult s f := rfl
  rw [inner] at pb
  obtain ⟨c,hc,pc⟩ := lift_run _ _ _ _ _ (OriginalTextureWrapper.gate_execution (innerResult s f).core (innerResult s f).flags) wrapper_agreement
  have seam : ⟨(innerResult s f).core,(innerResult s f).flags,0x34759⟩=innerResult s f := by
    have h := (inner_return s f).1
    cases e : innerResult s f
    simp_all
  rw [seam] at pc
  have path := (pa.trans pb).trans pc
  by_cases missing : (innerResult s f).core.regs 0=(0xffffffff#32)
  · exact ⟨a+b+c,by omega,by simpa only [wrappedResult,missing,↓reduceIte] using path⟩
  · have returns : load32 (OriginalTextureWrapper.choice (innerResult s f).core).core.memory
        ((OriginalTextureWrapper.choice (innerResult s f).core).core.regs 4+8)=dest := by
      simpa [OriginalTextureWrapper.choice,put,write] using (wrapper_words s f).2.2.trans ret
    obtain ⟨d,hd,pd⟩ := lift_run _ _ _ _ _
      (OriginalTextureWrapper.return_execution (OriginalTextureWrapper.choice (innerResult s f).core).core
        (OriginalTextureWrapper.choice (innerResult s f).core).flags dest outside returns) wrapper_agreement
    have seam : ⟨(OriginalTextureWrapper.choice (innerResult s f).core).core,
        (OriginalTextureWrapper.choice (innerResult s f).core).flags,0x3476e⟩=OriginalTextureWrapper.choice (innerResult s f).core := by
      simp [OriginalTextureWrapper.choice,missing]
    rw [seam] at pd
    exact ⟨a+b+c+d,by omega,by simpa only [wrappedResult,missing,↓reduceIte] using path.trans pd⟩

theorem wrapper_outcomes (s : X86Memory.State) (f : Option Flags) :
    ((innerResult s f).core.regs 0=0xffffffff → (wrappedResult s f).pc=0x34760) ∧
    ((innerResult s f).core.regs 0≠0xffffffff →
      (wrappedResult s f).pc=(load32 s.memory (s.regs 4)).toNat ∧
      (wrappedResult s f).core.regs 0=(innerResult s f).core.regs 0 ∧
      (wrappedResult s f).core.regs 2=s.regs 2 ∧
      (wrappedResult s f).core.regs 3=s.regs 3 ∧
      (wrappedResult s f).core.regs 4=s.regs 4+4) := by
  constructor
  · intro h
    have h : (innerResult s f).core.regs 0=(0xffffffff#32) := h
    simp [wrappedResult,h,OriginalTextureWrapper.choice]
  · intro h
    have h : (innerResult s f).core.regs 0≠(0xffffffff#32) := h
    have words := wrapper_words s f
    have sp := (inner_return s f).2
    simp only [wrappedResult,h,↓reduceIte]
    have regs := E1M1AimTextureWrapper.caller_registers s (innerResult s f).core sp words.1 words.2.1
    refine ⟨?_,regs⟩
    simpa [OriginalTextureWrapper.result,OriginalTextureWrapper.choice,put,write] using congrArg BitVec.toNat words.2.2

theorem named_registers (s : X86Memory.State) (r : Reg) (h0 : r≠0) (h4 : r≠4) :
    (namedResult s).core.regs r=s.regs r := by
  have h := OriginalTextureSearch.search_saved 2147483647 (namedStart s) (some (logical32 0))
    (by decide) (by simp [namedStart,OriginalTextureTable.tested,put,write]) r h0 h4
  change (namedResult s).core.regs r=(OriginalTextureDash.restored (namedStart s)).regs r at h
  rw [h]
  obtain ⟨a,b,c,d,e⟩ := OriginalTextureDash.saved_slots s
  have cases : r=1 ∨ r=2 ∨ r=3 ∨ r=5 ∨ r=6 ∨ r=7 := by
    have all : ∀ r : Reg, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 := by decide
    simpa only [h0,h4,false_or,or_false] using all r
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp_all [OriginalTextureDash.restored,namedStart,OriginalTextureTable.tested,OriginalTextureDash.prepared,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc]
end Doom.Proofs.E1M1AimTextureSearch
