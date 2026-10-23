import Doom.Proofs.OriginalTextureIteration
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalTextureComparator
open Verification X86 X86Memory X86Control BlockSummary OriginalTextureIteration

def zeroExit (s : X86Memory.State) : X86Control.State :=
  ⟨put s 0 0,some (logical32 0),0x419cc⟩

theorem gate_nonzero (s : X86Memory.State) (f : Option Flags) (h : s.regs 3≠0) :
    X86ByteRoutine.Prefix program [] 2 ⟨s,f,0x4198d⟩
      ⟨s,some (logical32 (s.regs 3)),0x41995⟩ := by
  have nz : s.regs 3≠(0#32) := h
  apply X86ByteRoutine.Prefix.step (middle := ⟨s,some (logical32 (s.regs 3)),0x4198f⟩) (by simp) (show program 0x4198d=some (.base (.control (.testWord 3 3)),2) by decide) (by simp [X86ByteRoutine.execute,X86Routine.execute,X86Control.execute])
  apply X86ByteRoutine.Prefix.step (middle := ⟨s,some (logical32 (s.regs 3)),0x41995⟩) (by simp) (show program 0x4198f=some (.base (.control (.jumpZero false 4)),2) by decide) (by simp [X86ByteRoutine.execute,X86Routine.execute,X86Control.execute,logical32,h,nz])
  exact X86ByteRoutine.Prefix.nil _

theorem gate_zero (s : X86Memory.State) (f : Option Flags) (h : s.regs 3=0) :
    X86ByteRoutine.Prefix program [] 4 ⟨s,f,0x4198d⟩ (zeroExit s) := by
  have nz : s.regs 3=(0#32) := h
  apply X86ByteRoutine.Prefix.step (middle := ⟨s,some (logical32 (s.regs 3)),0x4198f⟩) (by simp) (show program 0x4198d=some (.base (.control (.testWord 3 3)),2) by decide) (by simp [X86ByteRoutine.execute,X86Routine.execute,X86Control.execute])
  apply X86ByteRoutine.Prefix.step (middle := ⟨s,some (logical32 (s.regs 3)),0x41991⟩) (by simp) (show program 0x4198f=some (.base (.control (.jumpZero false 4)),2) by decide) (by simp [X86ByteRoutine.execute,X86Routine.execute,X86Control.execute,logical32,h,nz])
  apply X86ByteRoutine.Prefix.step (middle := ⟨put s 0 0,some (logical32 0),0x41993⟩) (by simp) (show program 0x41991=some (.base (.xorRegister 0 0),2) by decide) (by simp [X86ByteRoutine.execute,X86Routine.execute,logical32])
  apply X86ByteRoutine.Prefix.step (by simp) (show program 0x41993=some (.base (.jump 55),2) by decide) (by rfl)
  exact X86ByteRoutine.Prefix.nil _

/-- Natural recursion counts original nonzero-byte iterations; it is not a
wrapping machine counter or an assumed helper execution. -/
def loop : Nat → X86Memory.State → X86Control.State
  | 0,s => zeroExit s
  | n+1,s => if (iteration s).pc=0x419cc then iteration s else loop n (iteration s).core

theorem iteration_continue (s : X86Memory.State) (h : (iteration s).pc≠0x419cc) :
    iteration s=⟨advanced (foldedPair s),none,0x4198d⟩ ∧
    (iteration s).core.regs 3=s.regs 3-1 := by
  have same : iteration s=⟨advanced (foldedPair s),none,0x4198d⟩ := by
    unfold iteration suffix at *
    split at h <;> simp_all
    split at h <;> simp_all
  refine ⟨same,?_⟩
  rw [same]
  simp [advanced,put,write,folded_other_registers,BitVec.sub_eq_add_neg]

theorem decrement_measure (v : Word) (n : Nat) (h : v.toNat=n+1) :
    (v-1).toNat=n := by
  have lt := v.isLt
  simp [BitVec.toNat_sub,h]
  omega

theorem loop_exit (n : Nat) (s : X86Memory.State) : (loop n s).pc=0x419cc := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [loop]
    split
    · assumption
    · exact ih _

theorem loop_execution (n : Nat) (s : X86Memory.State) (f : Option Flags)
    (h : (s.regs 3).toNat=n) :
    ∃ k≤22*n+4, X86ByteRoutine.Prefix program [] k ⟨s,f,0x4198d⟩ (loop n s) := by
  induction n generalizing s f with
  | zero =>
    have z : s.regs 3=0 := BitVec.eq_of_toNat_eq h
    exact ⟨4,by omega,gate_zero s f z⟩
  | succ n ih =>
    have nz : s.regs 3≠0 := by intro z; simp [z] at h
    obtain ⟨k,hk,hp⟩ := iteration_execution s (some (logical32 (s.regs 3)))
    have start := (gate_nonzero s f nz).trans hp
    by_cases done : (iteration s).pc=0x419cc
    · exact ⟨2+k,by omega,by simpa only [loop,done,↓reduceIte] using start⟩
    · have facts := iteration_continue s done
      have dec : ((iteration s).core.regs 3).toNat=n := by
        rw [facts.2]; exact decrement_measure _ _ h
      obtain ⟨j,hj,pj⟩ := ih (iteration s).core (iteration s).flags dec
      have seam : ⟨(iteration s).core,(iteration s).flags,0x4198d⟩=iteration s := by rw [facts.1]
      rw [seam] at pj
      exact ⟨(2+k)+j,by omega,by simpa only [loop,done,↓reduceIte] using start.trans pj⟩

theorem iteration_preserved (s : X86Memory.State) (r : Reg)
    (h0 : r≠0) (h1 : r≠1) (h2 : r≠2) (h3 : r≠3) :
    (iteration s).core.regs r=s.regs r := by
  have h := folded_other_registers s r h1
  simp only [iteration,suffix]
  split
  · simpa [mismatch,putByte,put,write,byteReg,h0,h1,h2] using h
  · split
    · simpa [put,write,h0] using h
    · simpa [advanced,put,write,h0,h2,h3] using h

theorem loop_memory (n : Nat) (s : X86Memory.State) : (loop n s).core.memory=s.memory := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [loop]
    split
    · exact iteration_memory s
    · rw [ih,iteration_memory]

theorem loop_preserved (n : Nat) (s : X86Memory.State) (r : Reg)
    (h0 : r≠0) (h1 : r≠1) (h2 : r≠2) (h3 : r≠3) :
    (loop n s).core.regs r=s.regs r := by
  induction n generalizing s with
  | zero => simp [loop,zeroExit,put,write,h0]
  | succ n ih =>
    simp only [loop]
    split
    · exact iteration_preserved s r h0 h1 h2 h3
    · rw [ih,iteration_preserved s r h0 h1 h2 h3]

def complete (s : X86Memory.State) : X86Control.State :=
  let t := loop (s.regs 3).toNat (prepared s)
  restored t.core t.flags

theorem complete_execution (s : X86Memory.State) (f : Option Flags) :
    ∃ k≤22*(s.regs 3).toNat+7,
      X86ByteRoutine.Prefix program [] k ⟨s,f,0x4198c⟩ (complete s) := by
  have push : X86ByteRoutine.Prefix program [] 1 ⟨s,f,0x4198c⟩ ⟨prepared s,f,0x4198d⟩ := by
    exact X86ByteRoutine.Prefix.step (by simp) (show program 0x4198c=some (.base (.push 1),1) by decide) (by rfl) (.nil _)
  obtain ⟨k,hk,hp⟩ := loop_execution (s.regs 3).toNat (prepared s) f (by rfl)
  have tail := restore_execution (loop (s.regs 3).toNat (prepared s)).core
    (loop (s.regs 3).toNat (prepared s)).flags
  have seam : ⟨(loop (s.regs 3).toNat (prepared s)).core,
      (loop (s.regs 3).toNat (prepared s)).flags,0x419cc⟩=loop (s.regs 3).toNat (prepared s) := by
    have h := loop_exit (s.regs 3).toNat (prepared s)
    cases e : loop (s.regs 3).toNat (prepared s)
    simp_all
  rw [seam] at tail
  exact ⟨1+k+2,by omega,(push.trans hp).trans tail⟩

/-- POP/RET read the unchanged post-PUSH stack on every exit, not just the first.
Apart protects the caller word; no separation from either name is assumed. -/
theorem complete_restoration (s : X86Memory.State)
    (safe : Apart (s.regs 4) (s.regs 4-4)) :
    (complete s).core.regs 1=s.regs 1 ∧ (complete s).core.regs 4=s.regs 4+4 ∧
      (complete s).pc=(load32 s.memory (s.regs 4)).toNat := by
  have sp := loop_preserved (s.regs 3).toNat (prepared s) 4 (by decide) (by decide) (by decide) (by decide)
  simp only [complete,restored,loop_memory,sp]
  simp [prepared,X86Routine.pushWord,put,write,
    load_store,BitVec.sub_eq_add_neg,BitVec.add_assoc]
  have keep := load_store_apart s.memory (s.regs 4-4) (s.regs 4) (s.regs 1) safe
  simpa [BitVec.sub_eq_add_neg] using congrArg BitVec.toNat keep

theorem complete_frame (s : X86Memory.State) :
    (complete s).core.memory=(prepared s).memory ∧
    ∀ r : Reg, r≠0 → r≠1 → r≠2 → r≠3 → r≠4 → (complete s).core.regs r=s.regs r := by
  constructor
  · exact loop_memory _ _
  · intro r h0 h1 h2 h3 h4
    simp [complete,restored,put,write,h1,h4,loop_preserved _ _ r h0 h1 h2 h3,
      prepared,X86Routine.pushWord]

theorem table_return (s : X86Memory.State)
    (safe : Apart ((OriginalTextureTable.comparison s).core.regs 4)
      ((OriginalTextureTable.comparison s).core.regs 4-4)) :
    ∃ k≤183, X86ByteRoutine.Prefix program [] k (OriginalTextureTable.comparison s)
      (complete (OriginalTextureTable.comparison s).core) ∧
      (complete (OriginalTextureTable.comparison s).core).pc=0x34722 := by
  obtain ⟨k,hk,hp⟩ := complete_execution (OriginalTextureTable.comparison s).core
    (OriginalTextureTable.comparison s).flags
  rw [(OriginalTextureTable.comparison_arguments s).2.2.1] at hk
  refine ⟨k,hk,hp,?_⟩
  rw [(complete_restoration _ safe).2.2,(OriginalTextureTable.comparison_arguments s).2.2.2.2.2.2]
  rfl

/-- A memory-byte specification, proved below from the original loop. Reads are
from the supplied post-PUSH memory; addresses wrap as 32-bit words. The first
folded mismatch returns the difference of *zero-extended* bytes. Equal NUL or
exhaustion returns zero. This specification is not an execution oracle. -/
def compareBytes : Nat → Memory → Word → Word → Word
  | 0,_,_,_ => 0
  | n+1,m,a,b =>
    let x := OriginalTextureFold.lower (m a)
    let y := OriginalTextureFold.lower (m b)
    if x≠y then x.zeroExtend 32-y.zeroExtend 32
    else if y=0 then 0 else compareBytes n m (a+1) (b+1)

theorem loop_result (n : Nat) (s : X86Memory.State) :
    (loop n s).core.regs 0=compareBytes n s.memory (s.regs 0) (s.regs 2) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    have vals := loaded_fold_values s
    have mem : (foldedPair s).memory=s.memory := by
      simp [foldedPair,OriginalTextureFold.chResult,OriginalTextureFold.clResult,
        OriginalTextureFold.fold_memory,loaded,putByte,put]
    by_cases eq : OriginalTextureFold.lower (s.memory (s.regs 0))=OriginalTextureFold.lower (s.memory (s.regs 2))
    · by_cases z : OriginalTextureFold.lower (s.memory (s.regs 2))=(0#8)
      · simp [loop,iteration,suffix,vals.1,vals.2,eq,z,compareBytes,put,write]
      · have next : iteration s=⟨advanced (foldedPair s),none,0x4198d⟩ := by
          simp [iteration,suffix,vals.1,vals.2,eq,z]
        simp only [loop,next]
        simp only [show (0x4198d:Nat)≠0x419cc from by decide,↓reduceIte]
        rw [ih]
        simp [compareBytes,eq,z,advanced,put,write,mem,folded_other_registers]
    · have diff : readByte (foldedPair s).regs 1-readByte (foldedPair s).regs 5≠(0#8) := by
        intro h
        have equal := BitVec.sub_eq_iff_eq_add.mp h
        apply eq
        simpa [vals.1,vals.2] using equal
      have next : iteration s=⟨mismatch (foldedPair s),none,0x419cc⟩ := by
        simp [iteration,suffix,diff]
      simp only [loop,next,↓reduceIte]
      rw [mismatch_value]
      simp [compareBytes,eq,vals.1,vals.2]

theorem complete_result (s : X86Memory.State) :
    (complete s).core.regs 0=compareBytes (s.regs 3).toNat
      (prepared s).memory (s.regs 0) (s.regs 2) := by
  simpa [complete,restored,put,write,prepared,X86Routine.pushWord] using
    loop_result (s.regs 3).toNat (prepared s)

def combine (cmp : X86ByteRoutine.Program) (table : X86Routine.Program) : X86ByteRoutine.Program :=
  fun pc => match cmp pc with
  | some op => some op
  | none => X86ByteRoutine.liftProgram table pc

def joined := combine program OriginalTextureTable.program

theorem joined_comparator (pc : Nat) (h : program pc≠none) : joined pc=program pc := by
  simp only [joined,combine]
  cases he : program pc <;> simp_all

theorem joined_table (pc : Nat) (h : (X86ByteRoutine.liftProgram OriginalTextureTable.program) pc≠none) :
    joined pc=(X86ByteRoutine.liftProgram OriginalTextureTable.program) pc := by
  have bounds : pc<0x4198c := by
    by_cases b : (0x34700≤pc ∧ pc<0x34722) ∨ (0x3473c≤pc ∧ pc<0x34741)
    · omega
    · have b1 : ¬(0x34700≤pc ∧ pc<0x34722) := by omega
      have b2 : ¬(0x3473c≤pc ∧ pc<0x34741) := by omega
      simp [X86ByteRoutine.liftProgram,OriginalTextureTable.program,OriginalTextureTable.bytesProgram,b1,b2] at h
  have b1 : ¬(0x4198c≤pc ∧ pc<0x41999) := by omega
  have b2 : ¬(0x419b5≤pc ∧ pc<0x419ce) := by omega
  have b3 : ¬(0x41999≤pc ∧ pc<0x419b5) := by omega
  simp [joined,combine,program,bytesProgram,OriginalTextureFold.bytesProgram,b1,b2,b3]

/-- Actual six-instruction table setup/CALL, then the entire eight-byte
comparator including POP ECX/RET, all in one program without resetting state. -/
theorem table_call_return (s : X86Memory.State) (f : Option Flags)
    (safe : Apart ((OriginalTextureTable.comparison s).core.regs 4)
      ((OriginalTextureTable.comparison s).core.regs 4-4)) :
    ∃ k≤189, X86ByteRoutine.Prefix joined [] k ⟨s,f,0x3470c⟩
      (complete (OriginalTextureTable.comparison s).core) ∧
      (complete (OriginalTextureTable.comparison s).core).pc=0x34722 := by
  have call : X86ByteRoutine.run (X86ByteRoutine.liftProgram OriginalTextureTable.program)
      [0x4198c] 6 ⟨s,f,0x3470c⟩=some (OriginalTextureTable.comparison s) := by
    rw [X86ByteRoutine.run_lift]
    exact OriginalTextureTable.comparison_execution s f
  obtain ⟨a,ha,pa,_⟩ := X86ByteRoutine.run_path call
  obtain ⟨b,hb,pb,ret⟩ := table_return s safe
  exact ⟨a+b,by omega,(pa.transfer joined [] joined_table (by simp)).trans
    (pb.transfer joined [] joined_comparator (by simp)),ret⟩

end Doom.Proofs.OriginalTextureComparator
