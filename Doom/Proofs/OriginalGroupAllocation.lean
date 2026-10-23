import Doom.Proofs.OriginalGroupCountScan
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalGroupAllocation
open Verification X86 X86Memory X86Control BlockSummary
def allocationBytes : List UInt8 := [0x85,0xff,0x74,0xa,0x8d,0x43,0x18,0x89,0x7b,0x4,0x89,0x7,0xeb,0x19,0x83,0xfd,0x64,0x7c,0xd,0x68,0x54,0x3b,0x2,0x0,0xe8,0xc2,0x13,0xfe,0xff,0x83,0xc4,0x4,0xc7,0x43,0x4,0x2,0x0,0x0,0x0,0x8b,0x15,0xe0,0x4f,0x7,0x0,0x8b,0x43,0x10,0x89,0x6b,0x8,0x89,0x42,0x1c,0x8d,0x43,0x18,0xc7,0x43,0xc,0x11,0x4a,0x1d,0x0,0x5d,0x5f,0x5e,0x59,0xc3]
def bytesProgram (code : List UInt8) : X86Routine.Program := fun pc =>
  if 0x39731≤pc ∧ pc<0x39776 then X86Routine.decodeAt code (pc-0x39731) else none
def program := bytesProgram allocationBytes
def listed : X86Routine.Program
  | 0x39731 => some (.control (.testWord 7 7),2)
  | 0x39733 => some (.control (.jumpZero true 10),2)
  | 0x3973f => some (.compareRegister 5 100,3)
  | 0x39742 => some (.jumpSigned 3 13,2)
  | 0x39751 => some (.storeImmediate ⟨some 3,none,0,4⟩ 2,7)
  | 0x39758 => some (.control (.block (.load 2 ⟨none,none,0,0x74fe0⟩)),6)
  | 0x3975e => some (.control (.block (.legacy (.load 0 3 16))),3)
  | 0x39761 => some (.control (.block (.store ⟨some 3,none,0,8⟩ 5)),3)
  | 0x39764 => some (.control (.block (.store ⟨some 2,none,0,28⟩ 0)),3)
  | 0x39767 => some (.control (.block (.legacy (.lea 0 3 24))),3)
  | 0x3976a => some (.storeImmediate ⟨some 3,none,0,12⟩ 0x1d4a11,7)
  | 0x39771 => some (.pop 5,1)
  | 0x39772 => some (.pop 7,1)
  | 0x39773 => some (.pop 6,1)
  | 0x39774 => some (.pop 1,1)
  | 0x39775 => some (.ret,1)
  | _ => none
theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

/-- Exact ordered metadata writes of the no-user, non-purgeable allocation tail.
Selection and possible splitting of the block precede this interval. -/
def owned (s : X86Memory.State) := store32 s.memory (s.regs 3+4) 2
def zone (s : X86Memory.State) := load32 (owned s) 0x74fe0
def next (s : X86Memory.State) := load32 (owned s) (s.regs 3+16)
def tagged (s : X86Memory.State) := store32 (owned s) (s.regs 3+8) (s.regs 5)
def advanced (s : X86Memory.State) := store32 (tagged s) (zone s+28) (next s)
def committed (s : X86Memory.State) : X86Memory.State :=
  {put (put s 2 (zone s)) 0 (s.regs 3+24) with memory := store32 (advanced s) (s.regs 3+12) 0x1d4a11}
def pop (s : X86Memory.State) (r : Reg) := put (put s 4 (s.regs 4+4)) r (load32 s.memory (s.regs 4))
def restored (s : X86Memory.State) := pop (pop (pop (pop (committed s) 5) 7) 6) 1
def returned (s : X86Memory.State) : X86Control.State :=
  ⟨put (restored s) 4 ((restored s).regs 4+4),some (compare32 (s.regs 5) 100),
    (load32 (restored s).memory ((restored s).regs 4)).toNat⟩
@[local simp] private theorem step_39731 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e63e] (n+1) ⟨s,f,0x39731⟩ =
      (X86Routine.execute (.control (.testWord 7 7)) ⟨s,f,0x39733⟩).bind (X86Routine.run listed [0x2e63e] n) := by rfl
@[local simp] private theorem step_39733 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e63e] (n+1) ⟨s,f,0x39733⟩ =
      (X86Routine.execute (.control (.jumpZero true 10)) ⟨s,f,0x39735⟩).bind (X86Routine.run listed [0x2e63e] n) := by rfl
@[local simp] private theorem step_3973f (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e63e] (n+1) ⟨s,f,0x3973f⟩ =
      (X86Routine.execute (.compareRegister 5 100) ⟨s,f,0x39742⟩).bind (X86Routine.run listed [0x2e63e] n) := by rfl
@[local simp] private theorem step_39742 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e63e] (n+1) ⟨s,f,0x39742⟩ =
      (X86Routine.execute (.jumpSigned 3 13) ⟨s,f,0x39744⟩).bind (X86Routine.run listed [0x2e63e] n) := by rfl
@[local simp] private theorem step_39751 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e63e] (n+1) ⟨s,f,0x39751⟩ =
      (X86Routine.execute (.storeImmediate ⟨some 3,none,0,4⟩ 2) ⟨s,f,0x39758⟩).bind (X86Routine.run listed [0x2e63e] n) := by rfl
@[local simp] private theorem step_39758 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e63e] (n+1) ⟨s,f,0x39758⟩ =
      (X86Routine.execute (.control (.block (.load 2 ⟨none,none,0,0x74fe0⟩))) ⟨s,f,0x3975e⟩).bind (X86Routine.run listed [0x2e63e] n) := by rfl
@[local simp] private theorem step_3975e (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e63e] (n+1) ⟨s,f,0x3975e⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 0 3 16)))) ⟨s,f,0x39761⟩).bind (X86Routine.run listed [0x2e63e] n) := by rfl
@[local simp] private theorem step_39761 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e63e] (n+1) ⟨s,f,0x39761⟩ =
      (X86Routine.execute (.control (.block (.store ⟨some 3,none,0,8⟩ 5))) ⟨s,f,0x39764⟩).bind (X86Routine.run listed [0x2e63e] n) := by rfl
@[local simp] private theorem step_39764 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e63e] (n+1) ⟨s,f,0x39764⟩ =
      (X86Routine.execute (.control (.block (.store ⟨some 2,none,0,28⟩ 0))) ⟨s,f,0x39767⟩).bind (X86Routine.run listed [0x2e63e] n) := by rfl
@[local simp] private theorem step_39767 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e63e] (n+1) ⟨s,f,0x39767⟩ =
      (X86Routine.execute (.control (.block (.legacy (.lea 0 3 24)))) ⟨s,f,0x3976a⟩).bind (X86Routine.run listed [0x2e63e] n) := by rfl
@[local simp] private theorem step_3976a (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e63e] (n+1) ⟨s,f,0x3976a⟩ =
      (X86Routine.execute (.storeImmediate ⟨some 3,none,0,12⟩ 0x1d4a11) ⟨s,f,0x39771⟩).bind (X86Routine.run listed [0x2e63e] n) := by rfl
@[local simp] private theorem step_39771 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e63e] (n+1) ⟨s,f,0x39771⟩ =
      (X86Routine.execute (.pop 5) ⟨s,f,0x39772⟩).bind (X86Routine.run listed [0x2e63e] n) := by rfl
@[local simp] private theorem step_39772 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e63e] (n+1) ⟨s,f,0x39772⟩ =
      (X86Routine.execute (.pop 7) ⟨s,f,0x39773⟩).bind (X86Routine.run listed [0x2e63e] n) := by rfl
@[local simp] private theorem step_39773 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e63e] (n+1) ⟨s,f,0x39773⟩ =
      (X86Routine.execute (.pop 6) ⟨s,f,0x39774⟩).bind (X86Routine.run listed [0x2e63e] n) := by rfl
@[local simp] private theorem step_39774 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e63e] (n+1) ⟨s,f,0x39774⟩ =
      (X86Routine.execute (.pop 1) ⟨s,f,0x39775⟩).bind (X86Routine.run listed [0x2e63e] n) := by rfl
@[local simp] private theorem step_39775 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e63e] (n+1) ⟨s,f,0x39775⟩ =
      (X86Routine.execute (.ret) ⟨s,f,0x39776⟩).bind (X86Routine.run listed [0x2e63e] n) := by rfl
@[local simp] private theorem stopped (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e63e] n ⟨s,f,0x2e63e⟩=some ⟨s,f,0x2e63e⟩ := by cases n <;> rfl

/-- Conditions describe entry registers and a saved return slot, not an assumed
successful call or post-allocation memory image. -/
theorem execution (s : X86Memory.State) (f : Option Flags)
    (user : s.regs 7=(0#32)) (tag : (s.regs 5).toInt<100)
    (ret : load32 (committed s).memory (s.regs 4+16)=0x2e63e) :
    X86Routine.run program [0x2e63e] 16 ⟨s,f,0x39731⟩=some (returned s) := by
  have opposite : ¬(100 : Int)≤(s.regs 5).toInt := by omega
  have run : X86Routine.run listed [0x2e63e] 16 ⟨s,f,0x39731⟩=some (returned s) := by
    simp [committed,advanced,tagged,owned,zone,next] at ret
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      X86Block.Address.eval,X86.execute,blockPreservesFlags,returned,restored,pop,
      committed,advanced,tagged,owned,zone,next,user,tag,opposite,PlayerHeight.cmp_ge_prop,
      put,write,BitVec.add_assoc,ret,-BitVec.toInt_add]
    funext r
    by_cases h : r=0 <;> simp [write,h]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

def SafeWord (a : Word) (s : X86Memory.State) : Prop :=
  Apart a (s.regs 3+4) ∧ Apart a (s.regs 3+8) ∧ Apart a (zone s+28) ∧ Apart a (s.regs 3+12)

theorem frame (s : X86Memory.State) (a : Word) (safe : SafeWord a s) :
    load32 (committed s).memory a=load32 s.memory a := by
  change load32 (store32 (advanced s) (s.regs 3+12) 0x1d4a11) a=_
  rw [load_store_apart _ _ _ _ safe.2.2.2]
  unfold advanced
  rw [load_store_apart _ _ _ _ safe.2.2.1]
  unfold tagged
  rw [load_store_apart _ _ _ _ safe.2.1]
  exact load_store_apart _ _ _ _ safe.1

theorem returned_frame (s : X86Memory.State) (a : Word) (safe : SafeWord a s) :
    load32 (returned s).core.memory a=load32 s.memory a := frame s a safe

theorem returned_registers (s : X86Memory.State) :
    (returned s).core.regs 0=s.regs 3+24 ∧ (returned s).core.regs 4=s.regs 4+20 := by
  simp [returned,restored,pop,committed,put,write,BitVec.add_assoc]

theorem return_pc (s : X86Memory.State) (safe : SafeWord (s.regs 4+16) s)
    (ret : load32 s.memory (s.regs 4+16)=0x2e63e) : (returned s).pc=0x2e63e := by
  have kept := (frame s _ safe).trans ret
  simpa [returned,restored,pop,committed,put,write,BitVec.add_assoc] using congrArg BitVec.toNat kept

theorem from_initial (s : X86Memory.State) (f : Option Flags)
    (user : s.regs 7=(0#32)) (tag : s.regs 5=(50#32))
    (safe : SafeWord (s.regs 4+16) s) (ret : load32 s.memory (s.regs 4+16)=0x2e63e) :
    X86Routine.run program [0x2e63e] 16 ⟨s,f,0x39731⟩=some (returned s) :=
  execution s f user (by rw [tag]; decide) ((frame s _ safe).trans ret)

end Doom.Proofs.OriginalGroupAllocation
