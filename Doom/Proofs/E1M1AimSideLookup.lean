import Doom.Proofs.E1M1AimTextureLookup
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1AimSideLookup
open Verification X86 X86Memory X86Control BlockSummary

def joined : X86ByteRoutine.Program := fun pc =>
  if 0x2e47e≤pc ∧ pc<0x2e4af then X86ByteRoutine.liftProgram OriginalSideTextures.program pc
  else E1M1AimTextureSearch.joined pc

theorem caller_agreement (pc : Nat) (h : (X86ByteRoutine.liftProgram OriginalSideTextures.program) pc≠none) :
    joined pc=(X86ByteRoutine.liftProgram OriginalSideTextures.program) pc := by
  have inside : 0x2e47e≤pc ∧ pc<0x2e4af := by
    by_cases h' : 0x2e47e≤pc ∧ pc<0x2e4af
    · exact h'
    · simp [X86ByteRoutine.liftProgram,OriginalSideTextures.program,OriginalSideTextures.bytesProgram,h'] at h
  simp [joined,inside]

theorem lookup_agreement (pc : Nat) (h : E1M1AimTextureSearch.joined pc≠none) :
    joined pc=E1M1AimTextureSearch.joined pc := by
  have outside : ¬(0x2e47e≤pc ∧ pc<0x2e4af) := by
    intro inside
    have b0 : ¬(0x346f0≤pc ∧ pc<0x34700) := by omega
    have b1 : ¬(0x34750≤pc ∧ pc<0x34773) := by omega
    have b2 : ¬(0x4198c≤pc ∧ pc<0x41999) := by omega
    have b3 : ¬(0x419b5≤pc ∧ pc<0x419ce) := by omega
    have b4 : ¬(0x41999≤pc ∧ pc<0x419b5) := by omega
    have b5 : ¬(0x34700≤pc ∧ pc<0x34722) := by omega
    have b6 : ¬(0x3473c≤pc ∧ pc<0x34741) := by omega
    have b7 : ¬(0x34722≤pc ∧ pc<0x3473c) := by omega
    have b8 : ¬(0x34741≤pc ∧ pc<0x34747) := by omega
    simp [E1M1AimTextureSearch.joined,OriginalTextureSearch.program,OriginalTextureSearch.bytesProgram,
      OriginalTextureComparator.joined,OriginalTextureComparator.combine,
      OriginalTextureIteration.program,OriginalTextureIteration.bytesProgram,
      OriginalTextureFold.bytesProgram,OriginalTextureTable.program,
      OriginalTextureTable.bytesProgram,X86ByteRoutine.liftProgram,b0,b1,b2,b3,b4,b5,b6,b7,b8] at h
  simp [joined,outside]

/-- Explicit old-run embedding; the old caller contract is not silently coerced. -/
theorem caller_run (exits : List Nat) (n : Nat) (s t : X86Control.State)
    (run : X86Routine.run OriginalSideTextures.program exits n s=some t) :
    ∃ k≤n, X86ByteRoutine.Prefix joined [] k s t := by
  have h : X86ByteRoutine.run (X86ByteRoutine.liftProgram OriginalSideTextures.program) exits n s=some t := by
    rw [X86ByteRoutine.run_lift]; exact run
  obtain ⟨k,hk,hp,_⟩ := X86ByteRoutine.run_path h
  exact ⟨k,hk,hp.transfer joined [] caller_agreement (by simp)⟩

def first (s : X86Memory.State) (f : Option Flags) :=
  E1M1AimTextureLookup.wrapped (OriginalSideTextures.firstCall s f).core f
def second (s : X86Memory.State) (f : Option Flags) :=
  E1M1AimTextureLookup.wrapped (OriginalSideTextures.secondCall (first s f).core (first s f).flags).core (first s f).flags
def third (s : X86Memory.State) (f : Option Flags) :=
  E1M1AimTextureLookup.wrapped (OriginalSideTextures.thirdCall (second s f).core (second s f).flags).core (second s f).flags

def finished (s : X86Memory.State) (f : Option Flags) :=
  if (first s f).pc=0x34760 then first s f
  else if (second s f).pc=0x34760 then second s f
  else if (third s f).pc=0x34760 then third s f
  else OriginalSideTextures.finished (third s f).core (third s f).flags

theorem first_outcome (s : X86Memory.State) (f : Option Flags) :
    (first s f).pc=0x34760 ∨ (first s f).pc=0x2e483 := by
  have h := E1M1AimTextureLookup.wrapper_outcomes (OriginalSideTextures.firstCall s f).core f
  by_cases missing : (E1M1AimTextureLookup.inner (OriginalSideTextures.firstCall s f).core f).core.regs 0=0xffffffff
  · exact Or.inl (h.1 missing)
  · exact Or.inr (by simpa [first] using (h.2 missing).1.trans (congrArg BitVec.toNat (OriginalSideTextures.return_addresses s f).1))

theorem second_outcome (s : X86Memory.State) (f : Option Flags) :
    (second s f).pc=0x34760 ∨ (second s f).pc=0x2e494 := by
  have h := E1M1AimTextureLookup.wrapper_outcomes (OriginalSideTextures.secondCall (first s f).core (first s f).flags).core (first s f).flags
  by_cases missing : (E1M1AimTextureLookup.inner (OriginalSideTextures.secondCall (first s f).core (first s f).flags).core (first s f).flags).core.regs 0=0xffffffff
  · exact Or.inl (h.1 missing)
  · exact Or.inr (by simpa [second] using (h.2 missing).1.trans (congrArg BitVec.toNat (OriginalSideTextures.return_addresses (first s f).core (first s f).flags).2.1))

theorem third_outcome (s : X86Memory.State) (f : Option Flags) :
    (third s f).pc=0x34760 ∨ (third s f).pc=0x2e4a5 := by
  have h := E1M1AimTextureLookup.wrapper_outcomes (OriginalSideTextures.thirdCall (second s f).core (second s f).flags).core (second s f).flags
  by_cases missing : (E1M1AimTextureLookup.inner (OriginalSideTextures.thirdCall (second s f).core (second s f).flags).core (second s f).flags).core.regs 0=0xffffffff
  · exact Or.inl (h.1 missing)
  · exact Or.inr (by simpa [third] using (h.2 missing).1.trans (congrArg BitVec.toNat (OriginalSideTextures.return_addresses (second s f).core (second s f).flags).2.2))

/-- Actual CALL/lookup/RET sequences, including failure after any field.
No helper execution, returned image, or successful-lookup premise is supplied. -/
theorem execution (s : X86Memory.State) (f : Option Flags) :
    ∃ k≤3*(202*2147483647+30)+14,
      X86ByteRoutine.Prefix joined [] k ⟨s,f,0x2e47e⟩ (finished s f) := by
  obtain ⟨a,ha,pa⟩ := caller_run _ _ _ _ (OriginalSideTextures.first_execution s f)
  obtain ⟨b,hb,pb⟩ := E1M1AimTextureLookup.wrapper_execution (OriginalSideTextures.firstCall s f).core f
    0x2e483 (by decide) (OriginalSideTextures.return_addresses s f).1
  have pb := pb.transfer joined [] lookup_agreement (by simp)
  have path1 : X86ByteRoutine.Prefix joined [] (a+b) ⟨s,f,0x2e47e⟩ (first s f) := pa.trans pb
  by_cases fail1 : (first s f).pc=0x34760
  · exact ⟨a+b,by omega,by simpa only [finished,fail1,↓reduceIte] using path1⟩
  have pc1 : (first s f).pc=0x2e483 := (first_outcome s f).resolve_left fail1
  have seam1 : ⟨(first s f).core,(first s f).flags,0x2e483⟩=first s f := by
    cases e : first s f; simp_all
  obtain ⟨c,hc,pc⟩ := caller_run _ _ _ _ (OriginalSideTextures.second_execution (first s f).core (first s f).flags)
  rw [seam1] at pc
  obtain ⟨d,hd,pd⟩ := E1M1AimTextureLookup.wrapper_execution (OriginalSideTextures.secondCall (first s f).core (first s f).flags).core (first s f).flags
    0x2e494 (by decide) (OriginalSideTextures.return_addresses (first s f).core (first s f).flags).2.1
  have pd := pd.transfer joined [] lookup_agreement (by simp)
  have path2 : X86ByteRoutine.Prefix joined [] (a+b+c+d) ⟨s,f,0x2e47e⟩ (second s f) := (path1.trans pc).trans pd
  by_cases fail2 : (second s f).pc=0x34760
  · exact ⟨a+b+c+d,by omega,by simpa only [finished,fail1,fail2,↓reduceIte] using path2⟩
  have pc2 : (second s f).pc=0x2e494 := (second_outcome s f).resolve_left fail2
  have seam2 : ⟨(second s f).core,(second s f).flags,0x2e494⟩=second s f := by
    cases e : second s f; simp_all
  obtain ⟨e,he,pe⟩ := caller_run _ _ _ _ (OriginalSideTextures.third_execution (second s f).core (second s f).flags)
  rw [seam2] at pe
  obtain ⟨g,hg,pg⟩ := E1M1AimTextureLookup.wrapper_execution (OriginalSideTextures.thirdCall (second s f).core (second s f).flags).core (second s f).flags
    0x2e4a5 (by decide) (OriginalSideTextures.return_addresses (second s f).core (second s f).flags).2.2
  have pg := pg.transfer joined [] lookup_agreement (by simp)
  have path3 : X86ByteRoutine.Prefix joined [] (a+b+c+d+e+g) ⟨s,f,0x2e47e⟩ (third s f) := (path2.trans pe).trans pg
  by_cases fail3 : (third s f).pc=0x34760
  · exact ⟨a+b+c+d+e+g,by omega,by simpa only [finished,fail1,fail2,fail3,↓reduceIte] using path3⟩
  have pc3 : (third s f).pc=0x2e4a5 := (third_outcome s f).resolve_left fail3
  have seam3 : ⟨(third s f).core,(third s f).flags,0x2e4a5⟩=third s f := by
    cases e : third s f; simp_all
  obtain ⟨j,hj,pj⟩ := caller_run _ _ _ _ (OriginalSideTextures.finish_execution (third s f).core (third s f).flags)
  rw [seam3] at pj
  exact ⟨a+b+c+d+e+g+j,by omega,by simpa only [finished,fail1,fail2,fail3,↓reduceIte] using path3.trans pj⟩

theorem outcomes (s : X86Memory.State) (f : Option Flags) :
    (finished s f).pc=0x34760 ∨ (finished s f).pc=0x2e4af := by
  unfold finished
  split
  · exact Or.inl ‹_›
  · split
    · exact Or.inl ‹_›
    · split
      · exact Or.inl ‹_›
      · exact Or.inr rfl
/-- This is an outcome condition on computed execution, not a callee-path premise.
Pinned catalog initialization must still establish it for named map inputs. -/
def Returned (s : X86Memory.State) (f : Option Flags) : Prop :=
  (first s f).pc≠0x34760 ∧ (second s f).pc≠0x34760 ∧ (third s f).pc≠0x34760

structure Safe (s : X86Memory.State) (a : Word) : Prop where
  stack : ∀ off∈[(0#32),4,8,12,16,20,24,28,32,36,40,44], Apart a (s.regs 4-off)
  fields : ∀ off∈[(8#32),10,12], HalfMemory.Separate 4 2 a (s.regs 2+off)

theorem call_registers (s : X86Memory.State) (f : Option Flags) (dest : Word)
    (ok : (E1M1AimTextureLookup.wrapped (X86Routine.pushWord s dest) f).pc≠0x34760)
    (r : Reg) (h0 : r≠0) :
    (E1M1AimTextureLookup.wrapped (X86Routine.pushWord s dest) f).core.regs r=s.regs r := by
  have success : (E1M1AimTextureLookup.inner (X86Routine.pushWord s dest) f).core.regs 0≠0xffffffff := by
    intro missing
    exact ok ((E1M1AimTextureLookup.wrapper_outcomes _ _).1 missing)
  by_cases h4 : r=4
  · subst r
    have h := (E1M1AimTextureLookup.wrapper_outcomes _ _).2 success
    simpa [X86Routine.pushWord,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc] using h.2.2.2.2
  · simpa [X86Routine.pushWord,put,write,h4] using E1M1AimTextureLookup.wrapper_registers _ _ success r h0 h4

theorem call_frame (s : X86Memory.State) (f : Option Flags) (dest a : Word)
    (safe : ∀ off∈[(4#32),8,12,16,20,24,28,32,36,40,44], Apart a (s.regs 4-off)) :
    load32 (E1M1AimTextureLookup.wrapped (X86Routine.pushWord s dest) f).core.memory a=load32 s.memory a := by
  have h := E1M1AimTextureLookup.wrapper_frame (X86Routine.pushWord s dest) f a (by
    intro off member
    have mem : 4+off∈[(4#32),8,12,16,20,24,28,32,36,40,44] := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    simpa [X86Routine.pushWord,put,write,BitVec.sub_sub] using safe (4+off) mem)
  exact h.trans (load_store_apart _ _ _ _ (safe 4 (by simp)))

attribute [local irreducible] E1M1AimTextureLookup.wrapped

theorem stage_registers (s : X86Memory.State) (f : Option Flags) (ok : Returned s f)
    (r : Reg) (h0 : r≠0) :
    (first s f).core.regs r=s.regs r ∧ (second s f).core.regs r=s.regs r ∧
    (third s f).core.regs r=s.regs r := by
  have a := call_registers s f 0x2e483 ok.1 r h0
  change (first s f).core.regs r=s.regs r at a
  have b := call_registers (put (OriginalSideTextures.stored (first s f).core 8) 0 ((first s f).core.regs 7))
    (first s f).flags 0x2e494 ok.2.1 r h0
  have b : (second s f).core.regs r=s.regs r := by
    change (second s f).core.regs r=(put (OriginalSideTextures.stored (first s f).core 8) 0 ((first s f).core.regs 7)).regs r at b
    have eq : (put (OriginalSideTextures.stored (first s f).core 8) 0 ((first s f).core.regs 7)).regs r=(first s f).core.regs r := by simp only [put,write,if_neg h0,OriginalSideTextures.stored]
    exact b.trans (eq.trans a)
  have c := call_registers (put (OriginalSideTextures.stored (second s f).core 10) 0 ((second s f).core.regs 6))
    (second s f).flags 0x2e4a5 ok.2.2 r h0
  have c : (third s f).core.regs r=s.regs r := by
    change (third s f).core.regs r=(put (OriginalSideTextures.stored (second s f).core 10) 0 ((second s f).core.regs 6)).regs r at c
    have eq : (put (OriginalSideTextures.stored (second s f).core 10) 0 ((second s f).core.regs 6)).regs r=(second s f).core.regs r := by simp only [put,write,if_neg h0,OriginalSideTextures.stored]
    exact c.trans (eq.trans b)
  exact ⟨a,b,c⟩

theorem registers (s : X86Memory.State) (f : Option Flags) (ok : Returned s f)
    (r : Reg) (h0 : r≠0) : (finished s f).core.regs r=s.regs r := by
  simpa only [finished,if_neg ok.1,if_neg ok.2.1,if_neg ok.2.2,OriginalSideTextures.finished,OriginalSideTextures.stored]
    using (stage_registers s f ok r h0).2.2

theorem frame (s : X86Memory.State) (f : Option Flags) (ok : Returned s f)
    (a : Word) (safe : Safe s a) :
    load32 (finished s f).core.memory a=load32 s.memory a := by
  have stack : ∀ off∈[(4#32),8,12,16,20,24,28,32,36,40,44], Apart a (s.regs 4-off) := by
    intro off mem; exact safe.stack off (List.mem_cons_of_mem 0 mem)
  have sp := stage_registers s f ok 4 (by decide)
  have record := stage_registers s f ok 2 (by decide)
  have aFrame : load32 (first s f).core.memory a=load32 s.memory a := call_frame s f 0x2e483 a stack
  have bFrame := call_frame (put (OriginalSideTextures.stored (first s f).core 8) 0 ((first s f).core.regs 7))
    (first s f).flags 0x2e494 a (by intro off mem; change Apart a ((first s f).core.regs 4-off); rw [sp.1]; exact stack off mem)
  have bFrame : load32 (second s f).core.memory a=load32 (OriginalSideTextures.stored (first s f).core 8).memory a := bFrame
  have bStore := OriginalSideTextures.stored_frame (first s f).core 8 a
    (by rw [sp.1]; simpa using safe.stack 0 (by simp)) (by rw [record.1]; exact safe.fields 8 (by simp))
  have cFrame := call_frame (put (OriginalSideTextures.stored (second s f).core 10) 0 ((second s f).core.regs 6))
    (second s f).flags 0x2e4a5 a (by intro off mem; change Apart a ((second s f).core.regs 4-off); rw [sp.2.1]; exact stack off mem)
  have cFrame : load32 (third s f).core.memory a=load32 (OriginalSideTextures.stored (second s f).core 10).memory a := cFrame
  have cStore := OriginalSideTextures.stored_frame (second s f).core 10 a
    (by rw [sp.2.1]; simpa using safe.stack 0 (by simp)) (by rw [record.2.1]; exact safe.fields 10 (by simp))
  have last := OriginalSideTextures.stored_frame (third s f).core 12 a
    (by rw [sp.2.2]; simpa using safe.stack 0 (by simp)) (by rw [record.2.2]; exact safe.fields 12 (by simp))
  simpa only [finished,if_neg ok.1,if_neg ok.2.1,if_neg ok.2.2,OriginalSideTextures.finished] using
    last.trans (cFrame.trans (cStore.trans (bFrame.trans (bStore.trans aFrame))))

theorem half_of_load (m : Memory) (a : Word) (v : BitVec 16) (value : load16 m a=v) :
    E1M1NoiseImage.Realizes (E1M1NoiseImage.half a v) m := by
  subst v
  intro x hx
  simp only [E1M1NoiseImage.half,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl
  · simp only [load16,BitVec.extractLsb'_append_eq_right]
  · simp only [load16,BitVec.extractLsb'_append_eq_left]

/-- The suffix input is derived from the incoming source and actual executed
write frames; no reached post-texture image is assumed. -/
theorem post_input (s : X86Memory.State) (f : Option Flags) (ok : Returned s f)
    (side : BitVec 16) (index : Nat) (sideBase sectorBase : Word)
    (input : E1M1AimSideEncoding.Input s side index sideBase sectorBase)
    (sourceSafe : Safe s (s.regs 3+28)) (sectorSafe : Safe s 0x2c148) :
    E1M1AimSideEncoding.Input (finished s f).core side index sideBase sectorBase := by
  refine ⟨(registers s f ok 2 (by decide)).trans input.record,?_,
    (frame s f ok 0x2c148 sectorSafe).trans input.sectors,?_,input.valid⟩
  · rw [registers s f ok 3 (by decide)]
    exact half_of_load _ _ _ ((E1M1LineSource.half_of_word (frame s f ok _ sourceSafe)).trans (E1M1NoiseImage.read_half input.source))
  · rw [registers s f ok 4 (by decide)]
    exact input.safe
def iterationProgram : X86ByteRoutine.Program := fun pc =>
  if pc<0x2e47e ∨ (0x2e4af≤pc ∧ pc<0x2e4dd) then
    X86ByteRoutine.liftProgram OriginalSideAdvance.program pc else joined pc

theorem iteration_caller_agreement (pc : Nat) (h : joined pc≠none) :
    iterationProgram pc=joined pc := by
  have outside : ¬(pc<0x2e47e ∨ (0x2e4af≤pc ∧ pc<0x2e4dd)) := by
    intro inside
    have c : ¬(0x2e47e≤pc ∧ pc<0x2e4af) := by omega
    have b0 : ¬(0x346f0≤pc ∧ pc<0x34700) := by omega
    have b1 : ¬(0x34750≤pc ∧ pc<0x34773) := by omega
    have b2 : ¬(0x4198c≤pc ∧ pc<0x41999) := by omega
    have b3 : ¬(0x419b5≤pc ∧ pc<0x419ce) := by omega
    have b4 : ¬(0x41999≤pc ∧ pc<0x419b5) := by omega
    have b5 : ¬(0x34700≤pc ∧ pc<0x34722) := by omega
    have b6 : ¬(0x3473c≤pc ∧ pc<0x34741) := by omega
    have b7 : ¬(0x34722≤pc ∧ pc<0x3473c) := by omega
    have b8 : ¬(0x34741≤pc ∧ pc<0x34747) := by omega
    simp [joined,E1M1AimTextureSearch.joined,OriginalTextureSearch.program,OriginalTextureSearch.bytesProgram,
      OriginalTextureComparator.joined,OriginalTextureComparator.combine,
      OriginalTextureIteration.program,OriginalTextureIteration.bytesProgram,
      OriginalTextureFold.bytesProgram,OriginalTextureTable.program,
      OriginalTextureTable.bytesProgram,X86ByteRoutine.liftProgram,c,b0,b1,b2,b3,b4,b5,b6,b7,b8] at h
  simp [iterationProgram,outside]

theorem iteration_advance_agreement (pc : Nat) (h : (X86ByteRoutine.liftProgram OriginalSideAdvance.program) pc≠none) :
    iterationProgram pc=(X86ByteRoutine.liftProgram OriginalSideAdvance.program) pc := by
  have inside : pc<0x2e47e ∨ (0x2e4af≤pc ∧ pc<0x2e4dd) := by
    by_cases i : pc<0x2e47e ∨ (0x2e4af≤pc ∧ pc<0x2e4dd)
    · exact i
    · have b0 : ¬(0x2e4d1≤pc ∧ pc<0x2e4dd) := by omega
      have b1 : ¬(0x2e46a≤pc ∧ pc<0x2e47e) := by omega
      have b2 : ¬(0x2e415≤pc ∧ pc<0x2e41c) := by omega
      have b3 : ¬(0x2e4af≤pc ∧ pc<0x2e4d1) := by omega
      simp [X86ByteRoutine.liftProgram,OriginalSideAdvance.program,OriginalSideAdvance.bytesProgram,OriginalSideLoader.bytesProgram,b0,b1,b2,b3] at h
  simp [iterationProgram,inside]

def iteration (s : X86Memory.State) (f : Option Flags) :=
  if (finished s f).pc=0x34760 then finished s f else OriginalSideAdvance.result (finished s f).core

theorem iteration_execution (s : X86Memory.State) (f : Option Flags) :
    ∃ k≤3*(202*2147483647+30)+29,
      X86ByteRoutine.Prefix iterationProgram [] k ⟨s,f,0x2e47e⟩ (iteration s f) := by
  obtain ⟨a,ha,pa⟩ := execution s f
  have pa := pa.transfer iterationProgram [] iteration_caller_agreement (by simp)
  by_cases failed : (finished s f).pc=0x34760
  · exact ⟨a,by omega,by simpa only [iteration,failed,↓reduceIte] using pa⟩
  have pc : (finished s f).pc=0x2e4af := (outcomes s f).resolve_left failed
  have seam : ⟨(finished s f).core,(finished s f).flags,0x2e4af⟩=finished s f := by
    cases e : finished s f; simp_all
  have run := OriginalSideAdvance.linked_execution (finished s f).core (finished s f).flags
  have run : X86ByteRoutine.run (X86ByteRoutine.liftProgram OriginalSideAdvance.program) [0x2e46a,0x2e4dd] 15
      ⟨(finished s f).core,(finished s f).flags,0x2e4af⟩=some (OriginalSideAdvance.result (finished s f).core) := by
    rw [X86ByteRoutine.run_lift]; exact run
  obtain ⟨b,hb,pb,_⟩ := X86ByteRoutine.run_path run
  rw [seam] at pb
  have pb := pb.transfer iterationProgram [] iteration_advance_agreement (by simp)
  exact ⟨a+b,by omega,by simpa only [iteration,failed,↓reduceIte] using pa.trans pb⟩

theorem returned_pc (s : X86Memory.State) (f : Option Flags) (ok : Returned s f) :
    (finished s f).pc=0x2e4af := by
  simp only [finished,if_neg ok.1,if_neg ok.2.1,if_neg ok.2.2,OriginalSideTextures.finished]

theorem emitted (s : X86Memory.State) (f : Option Flags) (ok : Returned s f)
    (side : BitVec 16) (index : Nat) (sideBase sectorBase : Word)
    (input : E1M1AimSideEncoding.Input s side index sideBase sectorBase)
    (sourceSafe : Safe s (s.regs 3+28)) (sectorSafe : Safe s 0x2c148) :
    E1M1NoiseImage.Realizes
      (E1M1NoiseImage.word (E1M1NoiseGraph.sideAddress sideBase side) (E1M1AimSideEncoding.sectorAddress sectorBase index))
      (iteration s f).core.memory := by
  have post := post_input s f ok side index sideBase sectorBase input sourceSafe sectorSafe
  have h := (E1M1AimSideAdvance.emitted (finished s f).core (finished s f).flags side index sideBase sectorBase post).2
  simpa only [iteration,returned_pc s f ok,show (0x2e4af : Nat)≠0x34760 by decide,↓reduceIte] using h
/-- One complete loop body, including the offset reads/stores before the CALLs.
This is not repetition, loader entry, cleanup, or successful catalog initialization. -/
theorem body_execution (s : X86Memory.State) (f : Option Flags) :
    ∃ k≤3*(202*2147483647+30)+36,
      X86ByteRoutine.Prefix iterationProgram [] k ⟨s,f,0x2e46a⟩
        (iteration (OriginalSideAdvance.prepared s).core none) := by
  have run : X86ByteRoutine.run (X86ByteRoutine.liftProgram OriginalSideAdvance.program) [0x2e47e] 7
      ⟨s,f,0x2e46a⟩=some (OriginalSideAdvance.prepared s) := by
    rw [X86ByteRoutine.run_lift]
    exact OriginalSideAdvance.offsets_execution s f
  obtain ⟨a,ha,pa,_⟩ := X86ByteRoutine.run_path run
  have pa := pa.transfer iterationProgram [] iteration_advance_agreement (by simp)
  obtain ⟨b,hb,pb⟩ := iteration_execution (OriginalSideAdvance.prepared s).core none
  exact ⟨a+b,by omega,pa.trans pb⟩
end Doom.Proofs.E1M1AimSideLookup
