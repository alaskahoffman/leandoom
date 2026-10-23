import Doom.Proofs.OriginalTextureFold
import Doom.Verification.X86ComparatorRoutine
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalTextureIteration
open Verification X86 X86Memory X86Control BlockSummary

def entryBytes : List UInt8 := [0x51,0x85,0xdb,0x75,0x04,0x31,0xc0,0xeb,0x37,0x8a,0x08,0x8a,0x2a]
def suffixBytes : List UInt8 := [0x74,0x0c,0x31,0xc0,0x31,0xd2,0x88,0xc8,0x88,0xea,0x29,0xd0,0xeb,0x09,0x84,0xed,0x74,0xca,0x4b,0x42,0x40,0xeb,0xc1,0x59,0xc3]
def bytesProgram (entry suffix fold : List UInt8) : X86ByteRoutine.Program := fun pc =>
  if 0x4198c≤pc ∧ pc<0x41999 then X86ByteRoutine.decodeAt entry (pc-0x4198c)
  else if 0x419b5≤pc ∧ pc<0x419ce then X86ComparatorRoutine.decodeAt suffix (pc-0x419b5)
  else OriginalTextureFold.bytesProgram fold pc
def program := bytesProgram entryBytes suffixBytes OriginalTextureFold.foldBytes

def loaded (s : X86Memory.State) : X86Memory.State :=
  let t := putByte s 1 (s.memory (s.regs 0))
  putByte t 5 (t.memory (t.regs 2))

theorem loads_execution (s : X86Memory.State) (f : Option Flags) :
    X86ByteRoutine.run program [0x41999] 2 ⟨s,f,0x41995⟩=some ⟨loaded s,f,0x41999⟩ := by
  have a : program 0x41995=some (.base (.control (.loadByte 1 ⟨some 0,none,0,0⟩)),2) := by decide
  have b : program 0x41997=some (.base (.control (.loadByte 5 ⟨some 2,none,0,0⟩)),2) := by decide
  simp [X86ByteRoutine.run,a,b,X86ByteRoutine.execute,X86Routine.execute,X86Control.execute,
    X86Block.Address.eval,loaded]


def listed : X86ByteRoutine.Program
  | 0x4198c => some (.base (.push 1),1)
  | 0x4198d => some (.base (.control (.testWord 3 3)),2)
  | 0x4198f => some (.base (.control (.jumpZero false 4)),2)
  | 0x41991 => some (.base (.xorRegister 0 0),2)
  | 0x41993 => some (.base (.jump 55),2)
  | 0x41995 => some (.base (.control (.loadByte 1 ⟨some 0,none,0,0⟩)),2)
  | 0x41997 => some (.base (.control (.loadByte 5 ⟨some 2,none,0,0⟩)),2)
  | 0x419b5 => some (.base (.control (.jumpZero true 12)),2)
  | 0x419b7 => some (.base (.xorRegister 0 0),2)
  | 0x419b9 => some (.base (.xorRegister 2 2),2)
  | 0x419bb => some (.base (.moveByte 0 1),2)
  | 0x419bd => some (.base (.moveByte 2 5),2)
  | 0x419bf => some (.base (.control (.block (.arithmetic (.sub 0 2)))),2)
  | 0x419c1 => some (.base (.jump 9),2)
  | 0x419c3 => some (.base (.control (.testByte 5 5)),2)
  | 0x419c5 => some (.base (.control (.jumpZero true (-54))),2)
  | 0x419c7 => some (.base (.addImmediate 3 (-1)),1)
  | 0x419c8 => some (.base (.addImmediate 2 1),1)
  | 0x419c9 => some (.base (.addImmediate 0 1),1)
  | 0x419ca => some (.base (.jump (-63)),2)
  | 0x419cc => some (.base (.pop 1),1)
  | 0x419cd => some (.base .ret,1)
  | _ => none
theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide
@[local simp] private theorem step_4198c (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x4198c∉exits) :
    X86ByteRoutine.run listed exits (n+1) ⟨s,f,0x4198c⟩=
      (X86ByteRoutine.execute (.base (.push 1)) ⟨s,f,0x4198d⟩).bind (X86ByteRoutine.run listed exits n) := by
  rw [X86ByteRoutine.run,if_neg h]; rfl
@[local simp] private theorem step_4198d (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x4198d∉exits) :
    X86ByteRoutine.run listed exits (n+1) ⟨s,f,0x4198d⟩=
      (X86ByteRoutine.execute (.base (.control (.testWord 3 3))) ⟨s,f,0x4198f⟩).bind (X86ByteRoutine.run listed exits n) := by
  rw [X86ByteRoutine.run,if_neg h]; rfl
@[local simp] private theorem step_4198f (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x4198f∉exits) :
    X86ByteRoutine.run listed exits (n+1) ⟨s,f,0x4198f⟩=
      (X86ByteRoutine.execute (.base (.control (.jumpZero false 4))) ⟨s,f,0x41991⟩).bind (X86ByteRoutine.run listed exits n) := by
  rw [X86ByteRoutine.run,if_neg h]; rfl
@[local simp] private theorem step_41991 (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x41991∉exits) :
    X86ByteRoutine.run listed exits (n+1) ⟨s,f,0x41991⟩=
      (X86ByteRoutine.execute (.base (.xorRegister 0 0)) ⟨s,f,0x41993⟩).bind (X86ByteRoutine.run listed exits n) := by
  rw [X86ByteRoutine.run,if_neg h]; rfl
@[local simp] private theorem step_41993 (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x41993∉exits) :
    X86ByteRoutine.run listed exits (n+1) ⟨s,f,0x41993⟩=
      (X86ByteRoutine.execute (.base (.jump 55)) ⟨s,f,0x41995⟩).bind (X86ByteRoutine.run listed exits n) := by
  rw [X86ByteRoutine.run,if_neg h]; rfl
@[local simp] private theorem step_41995 (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x41995∉exits) :
    X86ByteRoutine.run listed exits (n+1) ⟨s,f,0x41995⟩=
      (X86ByteRoutine.execute (.base (.control (.loadByte 1 ⟨some 0,none,0,0⟩))) ⟨s,f,0x41997⟩).bind (X86ByteRoutine.run listed exits n) := by
  rw [X86ByteRoutine.run,if_neg h]; rfl
@[local simp] private theorem step_41997 (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x41997∉exits) :
    X86ByteRoutine.run listed exits (n+1) ⟨s,f,0x41997⟩=
      (X86ByteRoutine.execute (.base (.control (.loadByte 5 ⟨some 2,none,0,0⟩))) ⟨s,f,0x41999⟩).bind (X86ByteRoutine.run listed exits n) := by
  rw [X86ByteRoutine.run,if_neg h]; rfl
@[local simp] private theorem step_419b5 (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x419b5∉exits) :
    X86ByteRoutine.run listed exits (n+1) ⟨s,f,0x419b5⟩=
      (X86ByteRoutine.execute (.base (.control (.jumpZero true 12))) ⟨s,f,0x419b7⟩).bind (X86ByteRoutine.run listed exits n) := by
  rw [X86ByteRoutine.run,if_neg h]; rfl
@[local simp] private theorem step_419b7 (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x419b7∉exits) :
    X86ByteRoutine.run listed exits (n+1) ⟨s,f,0x419b7⟩=
      (X86ByteRoutine.execute (.base (.xorRegister 0 0)) ⟨s,f,0x419b9⟩).bind (X86ByteRoutine.run listed exits n) := by
  rw [X86ByteRoutine.run,if_neg h]; rfl
@[local simp] private theorem step_419b9 (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x419b9∉exits) :
    X86ByteRoutine.run listed exits (n+1) ⟨s,f,0x419b9⟩=
      (X86ByteRoutine.execute (.base (.xorRegister 2 2)) ⟨s,f,0x419bb⟩).bind (X86ByteRoutine.run listed exits n) := by
  rw [X86ByteRoutine.run,if_neg h]; rfl
@[local simp] private theorem step_419bb (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x419bb∉exits) :
    X86ByteRoutine.run listed exits (n+1) ⟨s,f,0x419bb⟩=
      (X86ByteRoutine.execute (.base (.moveByte 0 1)) ⟨s,f,0x419bd⟩).bind (X86ByteRoutine.run listed exits n) := by
  rw [X86ByteRoutine.run,if_neg h]; rfl
@[local simp] private theorem step_419bd (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x419bd∉exits) :
    X86ByteRoutine.run listed exits (n+1) ⟨s,f,0x419bd⟩=
      (X86ByteRoutine.execute (.base (.moveByte 2 5)) ⟨s,f,0x419bf⟩).bind (X86ByteRoutine.run listed exits n) := by
  rw [X86ByteRoutine.run,if_neg h]; rfl
@[local simp] private theorem step_419bf (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x419bf∉exits) :
    X86ByteRoutine.run listed exits (n+1) ⟨s,f,0x419bf⟩=
      (X86ByteRoutine.execute (.base (.control (.block (.arithmetic (.sub 0 2))))) ⟨s,f,0x419c1⟩).bind (X86ByteRoutine.run listed exits n) := by
  rw [X86ByteRoutine.run,if_neg h]; rfl
@[local simp] private theorem step_419c1 (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x419c1∉exits) :
    X86ByteRoutine.run listed exits (n+1) ⟨s,f,0x419c1⟩=
      (X86ByteRoutine.execute (.base (.jump 9)) ⟨s,f,0x419c3⟩).bind (X86ByteRoutine.run listed exits n) := by
  rw [X86ByteRoutine.run,if_neg h]; rfl
@[local simp] private theorem step_419c3 (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x419c3∉exits) :
    X86ByteRoutine.run listed exits (n+1) ⟨s,f,0x419c3⟩=
      (X86ByteRoutine.execute (.base (.control (.testByte 5 5))) ⟨s,f,0x419c5⟩).bind (X86ByteRoutine.run listed exits n) := by
  rw [X86ByteRoutine.run,if_neg h]; rfl
@[local simp] private theorem step_419c5 (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x419c5∉exits) :
    X86ByteRoutine.run listed exits (n+1) ⟨s,f,0x419c5⟩=
      (X86ByteRoutine.execute (.base (.control (.jumpZero true (-54)))) ⟨s,f,0x419c7⟩).bind (X86ByteRoutine.run listed exits n) := by
  rw [X86ByteRoutine.run,if_neg h]; rfl
@[local simp] private theorem step_419c7 (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x419c7∉exits) :
    X86ByteRoutine.run listed exits (n+1) ⟨s,f,0x419c7⟩=
      (X86ByteRoutine.execute (.base (.addImmediate 3 (-1))) ⟨s,f,0x419c8⟩).bind (X86ByteRoutine.run listed exits n) := by
  rw [X86ByteRoutine.run,if_neg h]; rfl
@[local simp] private theorem step_419c8 (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x419c8∉exits) :
    X86ByteRoutine.run listed exits (n+1) ⟨s,f,0x419c8⟩=
      (X86ByteRoutine.execute (.base (.addImmediate 2 1)) ⟨s,f,0x419c9⟩).bind (X86ByteRoutine.run listed exits n) := by
  rw [X86ByteRoutine.run,if_neg h]; rfl
@[local simp] private theorem step_419c9 (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x419c9∉exits) :
    X86ByteRoutine.run listed exits (n+1) ⟨s,f,0x419c9⟩=
      (X86ByteRoutine.execute (.base (.addImmediate 0 1)) ⟨s,f,0x419ca⟩).bind (X86ByteRoutine.run listed exits n) := by
  rw [X86ByteRoutine.run,if_neg h]; rfl
@[local simp] private theorem step_419ca (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x419ca∉exits) :
    X86ByteRoutine.run listed exits (n+1) ⟨s,f,0x419ca⟩=
      (X86ByteRoutine.execute (.base (.jump (-63))) ⟨s,f,0x419cc⟩).bind (X86ByteRoutine.run listed exits n) := by
  rw [X86ByteRoutine.run,if_neg h]; rfl
@[local simp] private theorem step_419cc (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x419cc∉exits) :
    X86ByteRoutine.run listed exits (n+1) ⟨s,f,0x419cc⟩=
      (X86ByteRoutine.execute (.base (.pop 1)) ⟨s,f,0x419cd⟩).bind (X86ByteRoutine.run listed exits n) := by
  rw [X86ByteRoutine.run,if_neg h]; rfl
@[local simp] private theorem step_419cd (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x419cd∉exits) :
    X86ByteRoutine.run listed exits (n+1) ⟨s,f,0x419cd⟩=
      (X86ByteRoutine.execute (.base .ret) ⟨s,f,0x419ce⟩).bind (X86ByteRoutine.run listed exits n) := by
  rw [X86ByteRoutine.run,if_neg h]; rfl
@[local simp] private theorem stopped (s : X86Memory.State) (f : Option Flags)
    (n pc : Nat) (exits : List Nat) (h : pc∈exits) :
    X86ByteRoutine.run listed exits n ⟨s,f,pc⟩=some ⟨s,f,pc⟩ := by
  cases n <;> simp [X86ByteRoutine.run,h]

def mismatch (s : X86Memory.State) : X86Memory.State :=
  let t := put (put s 0 0) 2 0
  let u := putByte t 0 (readByte t.regs 1)
  let v := putByte u 2 (readByte u.regs 5)
  put v 0 (v.regs 0-v.regs 2)
def advanced (s : X86Memory.State) : X86Memory.State :=
  put (put (put s 3 (s.regs 3+(-1))) 2 (s.regs 2+1)) 0 (s.regs 0+1)
def suffix (s : X86Memory.State) : X86Control.State :=
  if readByte s.regs 1-readByte s.regs 5≠0 then ⟨mismatch s,none,0x419cc⟩
  else if readByte s.regs 5=0 then ⟨put s 0 0,some (logical32 0),0x419cc⟩
  else ⟨advanced s,none,0x4198d⟩
def foldedPair (s : X86Memory.State) : X86Memory.State :=
  (OriginalTextureFold.chResult (OriginalTextureFold.clResult (loaded s)).core).core
def iteration (s : X86Memory.State) := suffix (foldedPair s)

theorem suffix_execution (s : X86Memory.State) :
    X86ByteRoutine.run program [0x419cc,0x4198d] 7 (OriginalTextureFold.compared s)=some (suffix s) := by
  have run : X86ByteRoutine.run listed [0x419cc,0x4198d] 7 (OriginalTextureFold.compared s)=some (suffix s) := by
    by_cases eq : readByte s.regs 1-readByte s.regs 5=(0#8)
    all_goals by_cases z : readByte s.regs 5=(0#8)
    all_goals simp_all [OriginalTextureFold.compared,X86ByteRoutine.execute,X86Routine.execute,
      X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,blockPreservesFlags,
      X86ByteRoutine.compare8,X86Routine.compare8,suffix,mismatch,advanced,eq,z,logical8,
      logical32,put,write]
  rw [X86ByteRoutine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

theorem fold_code (pc : Nat) (h : OriginalTextureFold.program pc≠none) :
    program pc=OriginalTextureFold.program pc := by
  have bounds : 0x41999≤pc ∧ pc<0x419b5 := by
    by_cases hn : 0x41999≤pc ∧ pc<0x419b5
    · exact hn
    · simp [OriginalTextureFold.program,OriginalTextureFold.bytesProgram,hn] at h
  have a : ¬(0x4198c≤pc ∧ pc<0x41999) := by omega
  have b : ¬(0x419b5≤pc ∧ pc<0x419ce) := by omega
  simp [program,bytesProgram,a,b,OriginalTextureFold.program]

private theorem path {p exits n s t} (h : X86ByteRoutine.run p exits n s=some t)
    (agree : ∀ pc, p pc≠none → program pc=p pc) :
    ∃ k≤n, X86ByteRoutine.Prefix program [] k s t := by
  obtain ⟨k,hk,hp,_⟩ := X86ByteRoutine.run_path h
  exact ⟨k,hk,hp.transfer program [] agree (by simp)⟩

/-- Actual instruction paths, with no reset between loads, folding, CMP and suffix.
The final PC is the common restore or loop-header TEST, not a synthetic return. -/
theorem iteration_execution (s : X86Memory.State) (f : Option Flags) :
    ∃ n≤20, X86ByteRoutine.Prefix program [] n ⟨s,f,0x41995⟩ (iteration s) := by
  obtain ⟨a,ha,pa⟩ := path (loads_execution s f) (by intros; rfl)
  obtain ⟨b,hb,pb⟩ := path (OriginalTextureFold.cl_execution (loaded s) f) fold_code
  obtain ⟨c,hc,pc⟩ := path (OriginalTextureFold.ch_execution
    (OriginalTextureFold.clResult (loaded s)).core
    (OriginalTextureFold.clResult (loaded s)).flags) fold_code
  obtain ⟨d,hd,pd⟩ := path (OriginalTextureFold.compare_execution (foldedPair s)
    (OriginalTextureFold.chResult (OriginalTextureFold.clResult (loaded s)).core).flags) fold_code
  obtain ⟨e,he,pe⟩ := path (suffix_execution (foldedPair s)) (by intros; rfl)
  exact ⟨a+b+c+d+e,by omega,(((pa.trans pb).trans pc).trans pd).trans pe⟩

theorem iteration_memory (s : X86Memory.State) : (iteration s).core.memory=s.memory := by
  have h : (foldedPair s).memory=s.memory := by
    simp [foldedPair,OriginalTextureFold.chResult,OriginalTextureFold.clResult,
      OriginalTextureFold.fold_memory,loaded,putByte,put]
  simp only [iteration,suffix]
  split
  · exact h
  · split <;> exact h

private theorem high_preserves_low (s : X86Memory.State) (v : BitVec 8) :
    readByte (putByte s 5 v).regs 1=readByte s.regs 1 := by
  change ((s.regs 1 &&& (0xffff00ff#32)) ||| (v.zeroExtend 32 <<< 8)).extractLsb' 0 8 = (s.regs 1).extractLsb' 0 8
  rw [BitVec.extractLsb'_or,BitVec.extractLsb'_and]
  have mask : (0xffff00ff#32).extractLsb' 0 8 = -1 := by decide
  have zero : ∀ v : BitVec 8, (v.zeroExtend 32 <<< 8).extractLsb' 0 8=0 := by decide +kernel
  have ones : ∀ b : BitVec 8, b &&& (-1)=b := by decide +kernel
  simp only [mask,ones,zero]
  exact BitVec.or_zero

theorem loaded_values (s : X86Memory.State) :
    readByte (loaded s).regs 1=s.memory (s.regs 0) ∧
    readByte (loaded s).regs 5=s.memory (s.regs 2) := by
  constructor
  · rw [loaded,high_preserves_low]
    exact write_low_read _ _
  · change readByte (putByte (putByte s 1 (s.memory (s.regs 0))) 5 (s.memory (s.regs 2))).regs 5=_
    exact write_high_read _ _

theorem loaded_fold_values (s : X86Memory.State) :
    readByte (foldedPair s).regs 1=OriginalTextureFold.lower (s.memory (s.regs 0)) ∧
    readByte (foldedPair s).regs 5=OriginalTextureFold.lower (s.memory (s.regs 2)) := by
  have h := OriginalTextureFold.pair_values (loaded s)
  simpa only [foldedPair,(loaded_values s).1,(loaded_values s).2] using h

theorem folded_other_registers (s : X86Memory.State) (r : Reg) (other : r≠1) :
    (foldedPair s).regs r=s.regs r := by
  simp only [foldedPair,OriginalTextureFold.chResult,OriginalTextureFold.clResult]
  rw [OriginalTextureFold.fold_other_registers _ 5 r (by exact other),
      OriginalTextureFold.fold_other_registers _ 1 r (by exact other)]
  simp [loaded,putByte,put,write,other,show byteReg (5:Reg)=1 from rfl,show byteReg (1:Reg)=1 from rfl]

theorem mismatch_value (s : X86Memory.State) :
    (mismatch s).regs 0=(readByte s.regs 1).zeroExtend 32-(readByte s.regs 5).zeroExtend 32 := by
  simp [mismatch,putByte,readByte,byteReg,put,write,show (5:Reg).val=5 from rfl]

/-- POP ECX then RET, reading the actual two stack words. No synthetic return PC. -/
def restored (s : X86Memory.State) (f : Option Flags) : X86Control.State :=
  ⟨put (put (put s 4 (s.regs 4+4)) 1 (load32 s.memory (s.regs 4))) 4 ((s.regs 4+4)+4),f,
    (load32 s.memory (s.regs 4+4)).toNat⟩

theorem restore_execution (s : X86Memory.State) (f : Option Flags) :
    X86ByteRoutine.Prefix program [] 2 ⟨s,f,0x419cc⟩ (restored s f) := by
  apply X86ByteRoutine.Prefix.step (by simp) (show program 0x419cc=some (.base (.pop 1),1) by decide) (by rfl)
  apply X86ByteRoutine.Prefix.step (by simp) (show program 0x419cd=some (.base .ret,1) by decide) (by rfl)
  exact X86ByteRoutine.Prefix.nil _

theorem iteration_return (s : X86Memory.State) (f : Option Flags)
    (done : (iteration s).pc=0x419cc) :
    ∃ n≤22, X86ByteRoutine.Prefix program [] n ⟨s,f,0x41995⟩
      (restored (iteration s).core (iteration s).flags) := by
  obtain ⟨n,hn,hp⟩ := iteration_execution s f
  have tail := restore_execution (iteration s).core (iteration s).flags
  have same : ⟨(iteration s).core,(iteration s).flags,0x419cc⟩=iteration s := by
    cases h : iteration s
    simp_all
  rw [same] at tail
  exact ⟨n+2,by omega,hp.trans tail⟩

def prepared (s : X86Memory.State) := X86Routine.pushWord s (s.regs 1)

theorem entry_execution (s : X86Memory.State) (f : Option Flags) (nonzero : s.regs 3≠0) :
    X86ByteRoutine.run program [0x41995] 3 ⟨s,f,0x4198c⟩=
      some ⟨prepared s,some (logical32 (s.regs 3)),0x41995⟩ := by
  have run : X86ByteRoutine.run listed [0x41995] 3 ⟨s,f,0x4198c⟩=
      some ⟨prepared s,some (logical32 (s.regs 3)),0x41995⟩ := by
    have nz : s.regs 3≠(0#32) := nonzero
    simp [X86ByteRoutine.execute,X86Routine.execute,X86Control.execute,
      prepared,X86Routine.pushWord,put,write,logical32,nz]
  rw [X86ByteRoutine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

theorem first_iteration_return (s : X86Memory.State) (f : Option Flags) (nonzero : s.regs 3≠0)
    (done : (iteration (prepared s)).pc=0x419cc) :
    ∃ n≤25, X86ByteRoutine.Prefix program [] n ⟨s,f,0x4198c⟩
      (restored (iteration (prepared s)).core (iteration (prepared s)).flags) := by
  obtain ⟨a,ha,pa⟩ := path (entry_execution s f nonzero) (by intros; rfl)
  obtain ⟨b,hb,pb⟩ := iteration_return (prepared s) (some (logical32 (s.regs 3))) done
  exact ⟨a+b,by omega,pa.trans pb⟩

theorem iteration_stack (s : X86Memory.State) : (iteration s).core.regs 4=s.regs 4 := by
  have h := folded_other_registers s 4 (by decide)
  simp only [iteration,suffix]
  split
  · simpa [mismatch,putByte,put,write,byteReg] using h
  · split
    · simpa [put,write] using h
    · simpa [advanced,put,write] using h

/-- Stack restoration uses the stack after the real prologue write. The explicit
separation premise protects the incoming return word, not the name bytes. -/
theorem first_restoration (s : X86Memory.State)
    (safe : Apart (s.regs 4) (s.regs 4-4)) :
    (restored (iteration (prepared s)).core (iteration (prepared s)).flags).core.regs 1=s.regs 1 ∧
    (restored (iteration (prepared s)).core (iteration (prepared s)).flags).core.regs 4=s.regs 4+4 ∧
    (restored (iteration (prepared s)).core (iteration (prepared s)).flags).pc=(load32 s.memory (s.regs 4)).toNat := by
  simp [restored,iteration_memory,iteration_stack,prepared,X86Routine.pushWord,put,write,
    load_store,BitVec.sub_eq_add_neg,BitVec.add_assoc]
  have keep := load_store_apart s.memory (s.regs 4-4) (s.regs 4) (s.regs 1) safe
  simpa [BitVec.sub_eq_add_neg] using congrArg BitVec.toNat keep

/-- A real RET to the texture-search continuation, not a supplied helper path. -/
theorem caller_return (s : X86Memory.State) (f : Option Flags)
    (nonzero : s.regs 3≠0) (done : (iteration (prepared s)).pc=0x419cc)
    (safe : Apart (s.regs 4) (s.regs 4-4))
    (returnWord : load32 s.memory (s.regs 4)=0x34722) :
    ∃ n≤25, X86ByteRoutine.Prefix program [] n ⟨s,f,0x4198c⟩
      (restored (iteration (prepared s)).core (iteration (prepared s)).flags) ∧
      (restored (iteration (prepared s)).core (iteration (prepared s)).flags).pc=0x34722 := by
  obtain ⟨n,hn,hp⟩ := first_iteration_return s f nonzero done
  exact ⟨n,hn,hp,by rw [(first_restoration s safe).2.2,returnWord]; rfl⟩

/-- Specialize the real-return theorem to the already proved table CALL result.
The caller's eight-byte bound and return word are derived, not assumed again. -/
theorem table_first_return (s : X86Memory.State)
    (done : (iteration (prepared (OriginalTextureTable.comparison s).core)).pc=0x419cc)
    (safe : Apart ((OriginalTextureTable.comparison s).core.regs 4)
      ((OriginalTextureTable.comparison s).core.regs 4-4)) :
    ∃ n≤25, X86ByteRoutine.Prefix program [] n (OriginalTextureTable.comparison s)
      (restored (iteration (prepared (OriginalTextureTable.comparison s).core)).core
        (iteration (prepared (OriginalTextureTable.comparison s).core)).flags) ∧
      (restored (iteration (prepared (OriginalTextureTable.comparison s).core)).core
        (iteration (prepared (OriginalTextureTable.comparison s).core)).flags).pc=0x34722 := by
  have nonzero : (OriginalTextureTable.comparison s).core.regs 3≠0 := by
    rw [(OriginalTextureTable.comparison_arguments s).2.2.1]
    decide
  exact caller_return (OriginalTextureTable.comparison s).core
    (OriginalTextureTable.comparison s).flags nonzero done safe
    (OriginalTextureTable.comparison_arguments s).2.2.2.2.2.2

end Doom.Proofs.OriginalTextureIteration
