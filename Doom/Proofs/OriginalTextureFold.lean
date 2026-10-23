import Doom.Proofs.E1M1AimTextureTable
import Doom.Verification.X86ByteRoutine
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalTextureFold
open Verification X86 X86Memory X86Control BlockSummary
def foldBytes : List UInt8 := [0x80,0xf9,0x41,0x72,0x8,0x80,0xf9,0x5a,0x77,0x3,0x80,0xc1,0x20,0x80,0xfd,0x41,0x72,0x8,0x80,0xfd,0x5a,0x77,0x3,0x80,0xc5,0x20,0x38,0xe9]
def bytesProgram (bytes : List UInt8) : X86ByteRoutine.Program := fun pc =>
  if 0x41999≤pc ∧ pc<0x419b5 then X86ByteRoutine.decodeAt bytes (pc-0x41999) else none
def program := bytesProgram foldBytes
def listed : X86ByteRoutine.Program
  | 0x41999 => some (.compareImmediate 1 0x41,3)
  | 0x4199c => some (.base (.jumpUnsigned 0 8),2)
  | 0x4199e => some (.compareImmediate 1 0x5a,3)
  | 0x419a1 => some (.base (.jumpAbove 3),2)
  | 0x419a3 => some (.addImmediate 1 0x20,3)
  | 0x419a6 => some (.compareImmediate 5 0x41,3)
  | 0x419a9 => some (.base (.jumpUnsigned 0 8),2)
  | 0x419ab => some (.compareImmediate 5 0x5a,3)
  | 0x419ae => some (.base (.jumpAbove 3),2)
  | 0x419b0 => some (.addImmediate 5 0x20,3)
  | 0x419b3 => some (.compareBytes 1 5,2)
  | _ => none
theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def lower (b : BitVec 8) : BitVec 8 :=
  if b.toNat<65 then b else if 90<b.toNat then b else b+32

def folded (s : X86Memory.State) (r : Reg) : X86Memory.State :=
  let b := readByte s.regs r
  if b.toNat<65 then s else if 90<b.toNat then s else putByte s r (b+32)
def foldFlags (b : BitVec 8) : Flags :=
  if b.toNat<65 then X86ByteRoutine.compare8 b 65
  else if 90<b.toNat then X86ByteRoutine.compare8 b 90
  else X86ByteRoutine.add8 b 32

def clResult (s : X86Memory.State) : X86Control.State :=
  ⟨folded s 1,some (foldFlags (readByte s.regs 1)),0x419a6⟩
def chResult (s : X86Memory.State) : X86Control.State :=
  ⟨folded s 5,some (foldFlags (readByte s.regs 5)),0x419b3⟩
def compared (s : X86Memory.State) : X86Control.State :=
  ⟨s,some (X86ByteRoutine.compare8 (readByte s.regs 1) (readByte s.regs 5)),0x419b5⟩

private theorem below65 (b : BitVec 8) : b.ult (65#8)=decide (b.toNat<65) := by
  have h : ∀ b : BitVec 8, b.ult (65#8)=decide (b.toNat<65) := by decide +kernel
  exact h b
private theorem above90 (b : BitVec 8) :
    (b.ult (90#8)=false ∧ b-(90#8)≠(0#8)) ↔ 90<b.toNat := by
  have h : ∀ b : BitVec 8, (b.ult (90#8)=false ∧ b-(90#8)≠(0#8)) ↔ 90<b.toNat := by decide +kernel
  exact h b
@[local simp] private theorem step_41999 (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x41999∉exits) :
    X86ByteRoutine.run listed exits (n+1) ⟨s,f,0x41999⟩=
      (X86ByteRoutine.execute (.compareImmediate 1 0x41) ⟨s,f,0x4199c⟩).bind (X86ByteRoutine.run listed exits n) := by
  rw [X86ByteRoutine.run,if_neg h]; rfl
@[local simp] private theorem step_4199c (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x4199c∉exits) :
    X86ByteRoutine.run listed exits (n+1) ⟨s,f,0x4199c⟩=
      (X86ByteRoutine.execute (.base (.jumpUnsigned 0 8)) ⟨s,f,0x4199e⟩).bind (X86ByteRoutine.run listed exits n) := by
  rw [X86ByteRoutine.run,if_neg h]; rfl
@[local simp] private theorem step_4199e (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x4199e∉exits) :
    X86ByteRoutine.run listed exits (n+1) ⟨s,f,0x4199e⟩=
      (X86ByteRoutine.execute (.compareImmediate 1 0x5a) ⟨s,f,0x419a1⟩).bind (X86ByteRoutine.run listed exits n) := by
  rw [X86ByteRoutine.run,if_neg h]; rfl
@[local simp] private theorem step_419a1 (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x419a1∉exits) :
    X86ByteRoutine.run listed exits (n+1) ⟨s,f,0x419a1⟩=
      (X86ByteRoutine.execute (.base (.jumpAbove 3)) ⟨s,f,0x419a3⟩).bind (X86ByteRoutine.run listed exits n) := by
  rw [X86ByteRoutine.run,if_neg h]; rfl
@[local simp] private theorem step_419a3 (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x419a3∉exits) :
    X86ByteRoutine.run listed exits (n+1) ⟨s,f,0x419a3⟩=
      (X86ByteRoutine.execute (.addImmediate 1 0x20) ⟨s,f,0x419a6⟩).bind (X86ByteRoutine.run listed exits n) := by
  rw [X86ByteRoutine.run,if_neg h]; rfl
@[local simp] private theorem step_419a6 (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x419a6∉exits) :
    X86ByteRoutine.run listed exits (n+1) ⟨s,f,0x419a6⟩=
      (X86ByteRoutine.execute (.compareImmediate 5 0x41) ⟨s,f,0x419a9⟩).bind (X86ByteRoutine.run listed exits n) := by
  rw [X86ByteRoutine.run,if_neg h]; rfl
@[local simp] private theorem step_419a9 (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x419a9∉exits) :
    X86ByteRoutine.run listed exits (n+1) ⟨s,f,0x419a9⟩=
      (X86ByteRoutine.execute (.base (.jumpUnsigned 0 8)) ⟨s,f,0x419ab⟩).bind (X86ByteRoutine.run listed exits n) := by
  rw [X86ByteRoutine.run,if_neg h]; rfl
@[local simp] private theorem step_419ab (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x419ab∉exits) :
    X86ByteRoutine.run listed exits (n+1) ⟨s,f,0x419ab⟩=
      (X86ByteRoutine.execute (.compareImmediate 5 0x5a) ⟨s,f,0x419ae⟩).bind (X86ByteRoutine.run listed exits n) := by
  rw [X86ByteRoutine.run,if_neg h]; rfl
@[local simp] private theorem step_419ae (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x419ae∉exits) :
    X86ByteRoutine.run listed exits (n+1) ⟨s,f,0x419ae⟩=
      (X86ByteRoutine.execute (.base (.jumpAbove 3)) ⟨s,f,0x419b0⟩).bind (X86ByteRoutine.run listed exits n) := by
  rw [X86ByteRoutine.run,if_neg h]; rfl
@[local simp] private theorem step_419b0 (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x419b0∉exits) :
    X86ByteRoutine.run listed exits (n+1) ⟨s,f,0x419b0⟩=
      (X86ByteRoutine.execute (.addImmediate 5 0x20) ⟨s,f,0x419b3⟩).bind (X86ByteRoutine.run listed exits n) := by
  rw [X86ByteRoutine.run,if_neg h]; rfl
@[local simp] private theorem step_419b3 (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x419b3∉exits) :
    X86ByteRoutine.run listed exits (n+1) ⟨s,f,0x419b3⟩=
      (X86ByteRoutine.execute (.compareBytes 1 5) ⟨s,f,0x419b5⟩).bind (X86ByteRoutine.run listed exits n) := by
  rw [X86ByteRoutine.run,if_neg h]; rfl
@[local simp] private theorem stopped (s : X86Memory.State) (f : Option Flags)
    (n pc : Nat) (exits : List Nat) (h : pc∈exits) :
    X86ByteRoutine.run listed exits n ⟨s,f,pc⟩=some ⟨s,f,pc⟩ := by
  cases n <;> simp [X86ByteRoutine.run,h]

theorem cl_execution (s : X86Memory.State) (f : Option Flags) :
    X86ByteRoutine.run program [0x419a6] 5 ⟨s,f,0x41999⟩=some (clResult s) := by
  have run : X86ByteRoutine.run listed [0x419a6] 5 ⟨s,f,0x41999⟩=some (clResult s) := by
    by_cases lo : (readByte s.regs 1).toNat<65
    all_goals by_cases hi : 90<(readByte s.regs 1).toNat
    all_goals simp [X86ByteRoutine.execute,X86Routine.execute,X86ByteRoutine.compare8,
      X86Routine.compare8,below65,above90,clResult,folded,foldFlags,lo,hi]
  rw [X86ByteRoutine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

theorem ch_execution (s : X86Memory.State) (f : Option Flags) :
    X86ByteRoutine.run program [0x419b3] 5 ⟨s,f,0x419a6⟩=some (chResult s) := by
  have run : X86ByteRoutine.run listed [0x419b3] 5 ⟨s,f,0x419a6⟩=some (chResult s) := by
    by_cases lo : (readByte s.regs 5).toNat<65
    all_goals by_cases hi : 90<(readByte s.regs 5).toNat
    all_goals simp [X86ByteRoutine.execute,X86Routine.execute,X86ByteRoutine.compare8,
      X86Routine.compare8,below65,above90,chResult,folded,foldFlags,lo,hi]
  rw [X86ByteRoutine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

theorem compare_execution (s : X86Memory.State) (f : Option Flags) :
    X86ByteRoutine.run program [0x419b5] 1 ⟨s,f,0x419b3⟩=some (compared s) := by
  have run : X86ByteRoutine.run listed [0x419b5] 1 ⟨s,f,0x419b3⟩=some (compared s) := by
    simp [X86ByteRoutine.execute,compared]
  rw [X86ByteRoutine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

theorem lowercase_spec (b : BitVec 8) :
    lower b=if 65≤b.toNat ∧ b.toNat≤90 then b+32 else b := by
  have h : ∀ b : BitVec 8, lower b=(if 65≤b.toNat ∧ b.toNat≤90 then b+32 else b) := by decide +kernel
  exact h b

theorem lower_idempotent (b : BitVec 8) : lower (lower b)=lower b := by
  have h : ∀ b : BitVec 8, lower (lower b)=lower b := by decide +kernel
  exact h b

theorem fold_memory (s : X86Memory.State) (r : Reg) : (folded s r).memory=s.memory := by
  simp only [folded]; split <;> try rfl
  split <;> rfl

theorem fold_other_registers (s : X86Memory.State) (r q : Reg) (other : q≠byteReg r) :
    (folded s r).regs q=s.regs q := by
  simp only [folded]; split <;> try rfl
  split <;> simp [putByte,put,write,other]
private theorem low_read (s : X86Memory.State) (v : BitVec 8) : readByte (putByte s 1 v).regs 1=v := by
  exact write_low_read (s.regs 1) v
private theorem high_read (s : X86Memory.State) (v : BitVec 8) : readByte (putByte s 5 v).regs 5=v := by
  exact write_high_read (s.regs 1) v
private theorem high_preserves_low (s : X86Memory.State) (v : BitVec 8) : readByte (putByte s 5 v).regs 1=readByte s.regs 1 := by
  change ((s.regs 1 &&& (0xffff00ff#32)) ||| (v.zeroExtend 32 <<< 8)).extractLsb' 0 8 = (s.regs 1).extractLsb' 0 8
  rw [BitVec.extractLsb'_or,BitVec.extractLsb'_and]
  have mask : (0xffff00ff#32).extractLsb' 0 8 = -1 := by decide
  have zero : ∀ v : BitVec 8, (v.zeroExtend 32 <<< 8).extractLsb' 0 8=0 := by decide +kernel
  have ones : ∀ b : BitVec 8, b &&& (-1)=b := by decide +kernel
  simp only [mask,ones,zero]
  exact BitVec.or_zero
private theorem low_preserves_high (s : X86Memory.State) (v : BitVec 8) : readByte (putByte s 1 v).regs 5=readByte s.regs 5 := by
  change ((s.regs 1 &&& (0xffffff00#32)) ||| v.zeroExtend 32).extractLsb' 8 8 = (s.regs 1).extractLsb' 8 8
  rw [BitVec.extractLsb'_or,BitVec.extractLsb'_and]
  have mask : (0xffffff00#32).extractLsb' 8 8 = -1 := by decide
  have zero : ∀ v : BitVec 8, (v.zeroExtend 32).extractLsb' 8 8=0 := by decide +kernel
  have ones : ∀ b : BitVec 8, b &&& (-1)=b := by decide +kernel
  simp only [mask,ones,zero]
  exact BitVec.or_zero

theorem cl_value (s : X86Memory.State) :
    readByte (clResult s).core.regs 1=lower (readByte s.regs 1) ∧
    readByte (clResult s).core.regs 5=readByte s.regs 5 := by
  simp only [clResult,folded,lower]
  split <;> try exact ⟨rfl,rfl⟩
  split <;> simp [low_read,low_preserves_high]

theorem ch_value (s : X86Memory.State) :
    readByte (chResult s).core.regs 5=lower (readByte s.regs 5) ∧
    readByte (chResult s).core.regs 1=readByte s.regs 1 := by
  simp only [chResult,folded,lower]
  split <;> try exact ⟨rfl,rfl⟩
  split <;> simp [high_read,high_preserves_low]

theorem pair_values (s : X86Memory.State) :
    readByte (chResult (clResult s).core).core.regs 1=lower (readByte s.regs 1) ∧
    readByte (chResult (clResult s).core).core.regs 5=lower (readByte s.regs 5) := by
  rw [(ch_value _).2,(ch_value _).1,(cl_value _).1,(cl_value _).2]
  exact ⟨rfl,rfl⟩

end Doom.Proofs.OriginalTextureFold
