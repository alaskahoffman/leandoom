import Doom.Proofs.E1M1AimOrderedMemory
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalTraversalReturn
open Verification X86 X86Memory X86Control BlockSummary
open OriginalAimQuery (pop)
attribute [local irreducible] load32 store32

/-- P_TraverseIntercepts epilogue, including the final cursor store. -/
def interceptCode : List UInt8 := [0xb8,1,0,0,0,0x89,0x0d,0x28,0xc0,2,0,0x83,0xc4,4,0x5f,0x5e,0x59,0x5b,0xc3]
/-- P_PathTraverse cleanup up to (but excluding) RET 8. -/
def pathCode : List UInt8 := [0x83,0xc4,0x30,0x5d,0x5f,0x5e]
def bytesProgram (intercept path : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2c887≤pc ∧ pc<0x2c89a then X86Routine.decodeAt intercept (pc-0x2c887)
  else if 0x2cb0b≤pc ∧ pc<0x2cb11 then X86Routine.decodeAt path (pc-0x2cb0b) else none
def program := bytesProgram interceptCode pathCode
def listed : X86Routine.Program
  | 0x2c887 => some (.immediate 0 1,5)
  | 0x2c88c => some (.control (.block (.store ⟨none,none,0,0x2c028⟩ 1)),6)
  | 0x2c892 => some (.addImmediate 4 4,3)
  | 0x2c895 => some (.pop 7,1)
  | 0x2c896 => some (.pop 6,1)
  | 0x2c897 => some (.pop 1,1)
  | 0x2c898 => some (.pop 3,1)
  | 0x2c899 => some (.ret,1)
  | 0x2cb0b => some (.addImmediate 4 48,3)
  | 0x2cb0e => some (.pop 5,1)
  | 0x2cb0f => some (.pop 7,1)
  | 0x2cb10 => some (.pop 6,1)
  | _ => none

theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def stored (s : X86Memory.State) : X86Memory.State :=
  {s with memory := store32 s.memory 0x2c028 (s.regs 1)}
def restored (s : X86Memory.State) :=
  pop (pop (pop (pop (put (stored s) 4 (s.regs 4+4)) 7) 6) 1) 3
def returned (s : X86Memory.State) : X86Control.State :=
  let t := restored s
  ⟨put t 4 (t.regs 4+4),none,(load32 t.memory (t.regs 4)).toNat⟩
def cleaned (s : X86Memory.State) : X86Control.State :=
  ⟨pop (pop (pop (put s 4 (s.regs 4+48)) 5) 7) 6,none,0x2cb11⟩

/-- The callback-stop route retains EAX; both routes perform the same real
cursor store, four register pops, and return-address load. -/
theorem stop_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 7 ⟨s,f,0x2c88c⟩ (returned s) := by
  have run : X86Routine.Prefix listed [] 7 ⟨s,f,0x2c88c⟩ (returned s) := by
    apply X86Routine.Prefix.step (middle := ⟨stored s,f,0x2c892⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
        X86Block.Address.eval,put,write,blockPreservesFlags,pop,stored,restored,returned])
    apply X86Routine.Prefix.step (middle := ⟨put (stored s) 4 (s.regs 4+4),none,0x2c895⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
        X86Block.Address.eval,put,write,blockPreservesFlags,pop,stored,restored,returned])
    apply X86Routine.Prefix.step (middle := ⟨pop (put (stored s) 4 (s.regs 4+4)) 7,none,0x2c896⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
        X86Block.Address.eval,put,write,blockPreservesFlags,pop,stored,restored,returned])
    apply X86Routine.Prefix.step (middle := ⟨pop (pop (put (stored s) 4 (s.regs 4+4)) 7) 6,none,0x2c897⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
        X86Block.Address.eval,put,write,blockPreservesFlags,pop,stored,restored,returned])
    apply X86Routine.Prefix.step (middle := ⟨pop (pop (pop (put (stored s) 4 (s.regs 4+4)) 7) 6) 1,none,0x2c898⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
        X86Block.Address.eval,put,write,blockPreservesFlags,pop,stored,restored,returned])
    apply X86Routine.Prefix.step (middle := ⟨pop (pop (pop (pop (put (stored s) 4 (s.regs 4+4)) 7) 6) 1) 3,none,0x2c899⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
        X86Block.Address.eval,put,write,blockPreservesFlags,pop,stored,restored,returned])
    apply X86Routine.Prefix.step (middle := returned s) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
        X86Block.Address.eval,put,write,blockPreservesFlags,pop,stored,restored,returned])
    exact .nil _
  exact run.transfer program [] decoded (by simp)

theorem exhausted_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 8 ⟨s,f,0x2c887⟩ (returned (put s 0 1)) := by
  apply X86Routine.Prefix.step (op := .immediate 0 1) (length := 5) (middle := ⟨put s 0 1,f,0x2c88c⟩) (by simp) (by change program 0x2c887=some (.immediate 0 1,5); decide) (by rfl)
  exact stop_execution (put s 0 1) f

/-- P_PathTraverse restores its three saved registers. RET 8 is the explicit
next boundary, not treated as an ordinary RET or a trusted callback. -/
theorem cleanup_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 4 ⟨s,f,0x2cb0b⟩ (cleaned s) := by
  have run : X86Routine.Prefix listed [] 4 ⟨s,f,0x2cb0b⟩ (cleaned s) := by
    apply X86Routine.Prefix.step (middle := ⟨put s 4 (s.regs 4+48),none,0x2cb0e⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
        X86Block.Address.eval,put,write,blockPreservesFlags,pop,cleaned])
    apply X86Routine.Prefix.step (middle := ⟨pop (put s 4 (s.regs 4+48)) 5,none,0x2cb0f⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
        X86Block.Address.eval,put,write,blockPreservesFlags,pop,cleaned])
    apply X86Routine.Prefix.step (middle := ⟨pop (pop (put s 4 (s.regs 4+48)) 5) 7,none,0x2cb10⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
        X86Block.Address.eval,put,write,blockPreservesFlags,pop,cleaned])
    apply X86Routine.Prefix.step (middle := cleaned s) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
        X86Block.Address.eval,put,write,blockPreservesFlags,pop,cleaned])
    exact .nil _
  exact run.transfer program [] decoded (by simp)

theorem return_layout (s : X86Memory.State) :
    (returned s).core.memory=(stored s).memory ∧
    (returned s).core.regs 0=s.regs 0 ∧
    (returned s).core.regs 4=s.regs 4+24 ∧
    (returned s).pc=(load32 (stored s).memory (s.regs 4+20)).toNat ∧
    (returned s).core.regs 7=load32 (stored s).memory (s.regs 4+4) ∧
    (returned s).core.regs 6=load32 (stored s).memory (s.regs 4+8) ∧
    (returned s).core.regs 1=load32 (stored s).memory (s.regs 4+12) ∧
    (returned s).core.regs 3=load32 (stored s).memory (s.regs 4+16) := by
  simp [returned,restored,stored,pop,put,write,BitVec.add_assoc]

theorem cleanup_layout (s : X86Memory.State) :
    (cleaned s).core.memory=s.memory ∧ (cleaned s).core.regs 0=s.regs 0 ∧
    (cleaned s).core.regs 4=s.regs 4+60 ∧
    (cleaned s).core.regs 5=load32 s.memory (s.regs 4+48) ∧
    (cleaned s).core.regs 7=load32 s.memory (s.regs 4+52) ∧
    (cleaned s).core.regs 6=load32 s.memory (s.regs 4+56) := by
  simp [cleaned,pop,put,write,BitVec.add_assoc]
end Doom.Proofs.OriginalTraversalReturn
