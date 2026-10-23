import Doom.Proofs.OriginalPlayerHealth

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.ActorHealth
open Verification X86 X86Memory X86Control BlockSummary

def actorBytes : List UInt8 := [0x83,0xff,0x64,0x7d,0x4,0x89,0xfb,0xeb,0x5,0xbb,0x64,0x0,0x0,0x0,0x8b,0x15,0xdc,0xb3,0x2,0x0,0x8d,0x4,0xd5,0x0,0x0,0x0,0x0,0x1,0xd0,0x8d,0x4,0x85,0x0,0x0,0x0,0x0,0x29,0xd0,0x8d,0x4,0xc5,0x0,0x0,0x0,0x0,0x5,0x78,0xae,0x2,0x0,0x39,0xc5,0x75,0x14,0xb8,0x28,0x0,0x0,0x0,0x1,0xdb,0xba,0xa,0x0,0x0,0x0,0x83,0xc3,0x28,0xe8,0xb6,0x14,0xff,0xff,0x8b,0x5e,0x6c,0x29,0xfb,0x89,0x5e,0x6c,0x85,0xdb,0x7f,0x10]
def tactileBytes : List UInt8 := [0x51,0x56,0x57,0x89,0xc6,0x89,0xd1,0x89,0xdf,0x83,0x3d,0x3c,0x92,0x2,0x0,0x0,0xf,0x84,0xdb,0x0,0x0,0x0]
def tactileReturnBytes : List UInt8 := [0x5f,0x5e,0x59,0xc3]
def bytesProgram (actor tactile tactileReturn : List UInt8) (pc : Nat) : Option (X86Routine.Op × Nat) :=
  if 0x2a650 ≤ pc ∧ pc < 0x2a6a6 then X86Routine.decodeAt actor (pc-0x2a650)
  else if 0x1bb50 ≤ pc ∧ pc < 0x1bb66 then X86Routine.decodeAt tactile (pc-0x1bb50)
  else if 0x1bc41 ≤ pc ∧ pc < 0x1bc45 then X86Routine.decodeAt tactileReturn (pc-0x1bc41)
  else none
def program := bytesProgram actorBytes tactileBytes tactileReturnBytes

def listed : X86Routine.Program
  | 0x2a650 => some (.compareRegister 7 100,3)
  | 0x2a653 => some (.jumpSigned 0 4,2)
  | 0x2a655 => some (.control (.block (.legacy (.mov 3 7))),2)
  | 0x2a657 => some (.jump 5,2)
  | 0x2a659 => some (.immediate 3 100,5)
  | 0x2a65e => some (.control (.block (.load 2 ⟨none,none,0,0x2b3dc⟩)),6)
  | 0x2a664 => some (.control (.block (.lea 0 ⟨none,some 2,3,0⟩)),7)
  | 0x2a66b => some (.control (.block (.arithmetic (.add 0 2))),2)
  | 0x2a66d => some (.control (.block (.lea 0 ⟨none,some 0,2,0⟩)),7)
  | 0x2a674 => some (.control (.block (.arithmetic (.sub 0 2))),2)
  | 0x2a676 => some (.control (.block (.lea 0 ⟨none,some 0,3,0⟩)),7)
  | 0x2a67d => some (.addImmediate 0 0x2ae78,5)
  | 0x2a682 => some (.compareRegisters 5 0,2)
  | 0x2a684 => some (.control (.jumpZero false 20),2)
  | 0x2a686 => some (.immediate 0 40,5)
  | 0x2a68b => some (.control (.block (.arithmetic (.add 3 3))),2)
  | 0x2a68d => some (.immediate 2 10,5)
  | 0x2a692 => some (.addImmediate 3 40,3)
  | 0x2a695 => some (.call (-60234),5)
  | 0x1bb50 => some (.push 1,1)
  | 0x1bb51 => some (.push 6,1)
  | 0x1bb52 => some (.push 7,1)
  | 0x1bb53 => some (.control (.block (.legacy (.mov 6 0))),2)
  | 0x1bb55 => some (.control (.block (.legacy (.mov 1 2))),2)
  | 0x1bb57 => some (.control (.block (.legacy (.mov 7 3))),2)
  | 0x1bb59 => some (.control (.cmpImmediate ⟨none,none,0,0x2923c⟩ 0),7)
  | 0x1bb60 => some (.control (.jumpZero true 219),6)
  | 0x1bc41 => some (.pop 7,1)
  | 0x1bc42 => some (.pop 6,1)
  | 0x1bc43 => some (.pop 1,1)
  | 0x1bc44 => some (.ret,1)
  | 0x2a69a => some (.control (.block (.legacy (.load 3 6 108))),3)
  | 0x2a69d => some (.control (.block (.arithmetic (.sub 3 7))),2)
  | 0x2a69f => some (.control (.block (.store ⟨some 6,none,0,108⟩ 3)),3)
  | 0x2a6a2 => some (.control (.testWord 3 3),2)
  | 0x2a6a4 => some (.jumpSigned 2 16,2)
  | _ => none

theorem decoded (pc : Nat) (h : listed pc ≠ none) : program pc = listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def console (s : X86Memory.State) : Word :=
  let n := load32 s.memory (0x2b3dc#32)
  ((((n <<< 3)+n) <<< 2)-n) <<< 3 |>.add (0x2ae78#32)
abbrev localPlayer (s : X86Memory.State) := s.regs 5 = console s
def slots (s : X86Memory.State) : List Word :=
  [s.regs 4-(4#32),s.regs 4-(8#32),s.regs 4-(12#32),s.regs 4-(16#32)]
def saved (s : X86Memory.State) : Memory :=
  store32 (store32 (store32 (store32 s.memory (s.regs 4-(4#32)) (0x2a69a#32))
    (s.regs 4-(8#32)) (s.regs 1)) (s.regs 4-(12#32)) (s.regs 6)) (s.regs 4-(16#32)) (s.regs 7)
def beforeHealth (s : X86Memory.State) := if localPlayer s then saved s else s.memory
def remainingHealth (s : X86Memory.State) := load32 (beforeHealth s) (s.regs 6+(108#32)) - s.regs 7
def resultMemory (s : X86Memory.State) := store32 (beforeHealth s) (s.regs 6+(108#32)) (remainingHealth s)
def exitPC (s : X86Memory.State) := if 0 < (remainingHealth s).toInt then 0x2a6b6 else 0x2a6a6

/-- The disabled-device branch is checked after the CALL and three pushes. -/
structure Inputs (s : X86Memory.State) : Prop where
  disabled : load32 s.memory (0x2923c#32) = 0
  flagSafe : ∀ a, a ∈ slots s → Apart (0x2923c#32) a

/-- Stack slots remain separated under unaligned and wrapping stack pointers. -/
theorem stack_apart (sp : Word) (a b : Fin 4) (h : a ≠ b) :
    Apart (sp-BitVec.ofNat 32 (4*(a.val+1))) (sp-BitVec.ofNat 32 (4*(b.val+1))) := by
  intro i j eq
  have aa := a.isLt; have bb := b.isLt; have ii := i.isLt; have jj := j.isLt
  have h' : a.val ≠ b.val := fun e => h (Fin.ext e)
  rw [BitVec.sub_eq_add_neg,BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.add_assoc] at eq
  have eq := (BitVec.add_right_inj sp).mp eq
  have eq' := congrArg BitVec.toNat eq
  simp only [BitVec.toNat_add,BitVec.toNat_neg,BitVec.toNat_ofNat] at eq'
  omega

theorem saved_frame (s : X86Memory.State) : PlayerHeight.Frame s.memory (saved s) (slots s) := by
  intro a safe
  unfold saved
  repeat rw [load_store_apart _ _ _ _ (safe _ (by simp [slots]))]

def setupListed : X86Routine.Program
  | 0x2a650 => some (.compareRegister 7 100,3)
  | 0x2a653 => some (.jumpSigned 0 4,2)
  | 0x2a655 => some (.control (.block (.legacy (.mov 3 7))),2)
  | 0x2a657 => some (.jump 5,2)
  | 0x2a659 => some (.immediate 3 100,5)
  | 0x2a65e => some (.control (.block (.load 2 ⟨none,none,0,0x2b3dc⟩)),6)
  | 0x2a664 => some (.control (.block (.lea 0 ⟨none,some 2,3,0⟩)),7)
  | 0x2a66b => some (.control (.block (.arithmetic (.add 0 2))),2)
  | 0x2a66d => some (.control (.block (.lea 0 ⟨none,some 0,2,0⟩)),7)
  | 0x2a674 => some (.control (.block (.arithmetic (.sub 0 2))),2)
  | 0x2a676 => some (.control (.block (.lea 0 ⟨none,some 0,3,0⟩)),7)
  | 0x2a67d => some (.addImmediate 0 0x2ae78,5)
  | 0x2a682 => some (.compareRegisters 5 0,2)
  | 0x2a684 => some (.control (.jumpZero false 20),2)
  | 0x2a686 => some (.immediate 0 40,5)
  | 0x2a68b => some (.control (.block (.arithmetic (.add 3 3))),2)
  | 0x2a68d => some (.immediate 2 10,5)
  | 0x2a692 => some (.addImmediate 3 40,3)
  | _ => none

theorem setupListed_contained (pc : Nat) (h : setupListed pc ≠ none) : listed pc = setupListed pc := by
  fun_cases setupListed pc <;> simp_all [setupListed,listed]
theorem setupListed_active (pc : Nat) (h : setupListed pc ≠ none) : pc ∉ [0x2a6a6,0x2a6b6] := by
  fun_cases setupListed pc <;> simp_all [setupListed]

def callListed : X86Routine.Program
  | 0x2a695 => some (.call (-60234),5)
  | 0x1bb50 => some (.push 1,1)
  | 0x1bb51 => some (.push 6,1)
  | 0x1bb52 => some (.push 7,1)
  | 0x1bb53 => some (.control (.block (.legacy (.mov 6 0))),2)
  | 0x1bb55 => some (.control (.block (.legacy (.mov 1 2))),2)
  | 0x1bb57 => some (.control (.block (.legacy (.mov 7 3))),2)
  | 0x1bb59 => some (.control (.cmpImmediate ⟨none,none,0,0x2923c⟩ 0),7)
  | 0x1bb60 => some (.control (.jumpZero true 219),6)
  | 0x1bc41 => some (.pop 7,1)
  | 0x1bc42 => some (.pop 6,1)
  | 0x1bc43 => some (.pop 1,1)
  | 0x1bc44 => some (.ret,1)
  | _ => none

theorem callListed_contained (pc : Nat) (h : callListed pc ≠ none) : listed pc = callListed pc := by
  fun_cases callListed pc <;> simp_all [callListed,listed]
theorem callListed_active (pc : Nat) (h : callListed pc ≠ none) : pc ∉ [0x2a6a6,0x2a6b6] := by
  fun_cases callListed pc <;> simp_all [callListed]

def bodyListed : X86Routine.Program
  | 0x2a69a => some (.control (.block (.legacy (.load 3 6 108))),3)
  | 0x2a69d => some (.control (.block (.arithmetic (.sub 3 7))),2)
  | 0x2a69f => some (.control (.block (.store ⟨some 6,none,0,108⟩ 3)),3)
  | 0x2a6a2 => some (.control (.testWord 3 3),2)
  | 0x2a6a4 => some (.jumpSigned 2 16,2)
  | _ => none

@[simp] theorem step_0x2a69a (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run bodyListed [0x2a6a6,0x2a6b6] (n+1) ⟨s,f,0x2a69a⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 3 6 108)))) ⟨s,f,0x2a69d⟩).bind (X86Routine.run bodyListed [0x2a6a6,0x2a6b6] n) := by rfl

@[simp] theorem step_0x2a69d (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run bodyListed [0x2a6a6,0x2a6b6] (n+1) ⟨s,f,0x2a69d⟩ =
      (X86Routine.execute (.control (.block (.arithmetic (.sub 3 7)))) ⟨s,f,0x2a69f⟩).bind (X86Routine.run bodyListed [0x2a6a6,0x2a6b6] n) := by rfl

@[simp] theorem step_0x2a69f (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run bodyListed [0x2a6a6,0x2a6b6] (n+1) ⟨s,f,0x2a69f⟩ =
      (X86Routine.execute (.control (.block (.store ⟨some 6,none,0,108⟩ 3))) ⟨s,f,0x2a6a2⟩).bind (X86Routine.run bodyListed [0x2a6a6,0x2a6b6] n) := by rfl

@[simp] theorem step_0x2a6a2 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run bodyListed [0x2a6a6,0x2a6b6] (n+1) ⟨s,f,0x2a6a2⟩ =
      (X86Routine.execute (.control (.testWord 3 3)) ⟨s,f,0x2a6a4⟩).bind (X86Routine.run bodyListed [0x2a6a6,0x2a6b6] n) := by rfl

@[simp] theorem step_0x2a6a4 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run bodyListed [0x2a6a6,0x2a6b6] (n+1) ⟨s,f,0x2a6a4⟩ =
      (X86Routine.execute (.jumpSigned 2 16) ⟨s,f,0x2a6a6⟩).bind (X86Routine.run bodyListed [0x2a6a6,0x2a6b6] n) := by rfl

@[simp] theorem bodyListed_stop_0x2a6a6 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run bodyListed [0x2a6a6,0x2a6b6] n ⟨s,f,0x2a6a6⟩ = some ⟨s,f,0x2a6a6⟩ := by cases n <;> rfl

@[simp] theorem bodyListed_stop_0x2a6b6 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run bodyListed [0x2a6a6,0x2a6b6] n ⟨s,f,0x2a6b6⟩ = some ⟨s,f,0x2a6b6⟩ := by cases n <;> rfl

theorem bodyListed_contained (pc : Nat) (h : bodyListed pc ≠ none) : listed pc = bodyListed pc := by
  fun_cases bodyListed pc <;> simp_all [bodyListed,listed]
theorem bodyListed_active (pc : Nat) (h : bodyListed pc ≠ none) : pc ∉ [0x2a6a6,0x2a6b6] := by
  fun_cases bodyListed pc <;> simp_all [bodyListed]

def capListed : X86Routine.Program
  | 0x2a650 => some (.compareRegister 7 100,3)
  | 0x2a653 => some (.jumpSigned 0 4,2)
  | 0x2a655 => some (.control (.block (.legacy (.mov 3 7))),2)
  | 0x2a657 => some (.jump 5,2)
  | 0x2a659 => some (.immediate 3 100,5)
  | _ => none

@[simp] theorem capListed_step_0x2a650 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run capListed [0x2a65e] (n+1) ⟨s,f,0x2a650⟩ =
      (X86Routine.execute (.compareRegister 7 100) ⟨s,f,0x2a653⟩).bind (X86Routine.run capListed [0x2a65e] n) := by rfl

@[simp] theorem capListed_step_0x2a653 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run capListed [0x2a65e] (n+1) ⟨s,f,0x2a653⟩ =
      (X86Routine.execute (.jumpSigned 0 4) ⟨s,f,0x2a655⟩).bind (X86Routine.run capListed [0x2a65e] n) := by rfl

@[simp] theorem capListed_step_0x2a655 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run capListed [0x2a65e] (n+1) ⟨s,f,0x2a655⟩ =
      (X86Routine.execute (.control (.block (.legacy (.mov 3 7)))) ⟨s,f,0x2a657⟩).bind (X86Routine.run capListed [0x2a65e] n) := by rfl

@[simp] theorem capListed_step_0x2a657 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run capListed [0x2a65e] (n+1) ⟨s,f,0x2a657⟩ =
      (X86Routine.execute (.jump 5) ⟨s,f,0x2a659⟩).bind (X86Routine.run capListed [0x2a65e] n) := by rfl

@[simp] theorem capListed_step_0x2a659 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run capListed [0x2a65e] (n+1) ⟨s,f,0x2a659⟩ =
      (X86Routine.execute (.immediate 3 100) ⟨s,f,0x2a65e⟩).bind (X86Routine.run capListed [0x2a65e] n) := by rfl

@[simp] theorem capListed_stop_0x2a65e (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run capListed [0x2a65e] n ⟨s,f,0x2a65e⟩ = some ⟨s,f,0x2a65e⟩ := by cases n <;> rfl
theorem capListed_contained (pc : Nat) (h : capListed pc ≠ none) : setupListed pc = capListed pc := by
  fun_cases capListed pc <;> simp_all [capListed,setupListed]
theorem capListed_active (pc : Nat) (h : capListed pc ≠ none) : pc ∉ [0x2a695,0x2a69a] := by
  fun_cases capListed pc <;> simp_all [capListed]

def consoleListed : X86Routine.Program
  | 0x2a65e => some (.control (.block (.load 2 ⟨none,none,0,0x2b3dc⟩)),6)
  | 0x2a664 => some (.control (.block (.lea 0 ⟨none,some 2,3,0⟩)),7)
  | 0x2a66b => some (.control (.block (.arithmetic (.add 0 2))),2)
  | 0x2a66d => some (.control (.block (.lea 0 ⟨none,some 0,2,0⟩)),7)
  | 0x2a674 => some (.control (.block (.arithmetic (.sub 0 2))),2)
  | 0x2a676 => some (.control (.block (.lea 0 ⟨none,some 0,3,0⟩)),7)
  | 0x2a67d => some (.addImmediate 0 0x2ae78,5)
  | 0x2a682 => some (.compareRegisters 5 0,2)
  | _ => none

@[simp] theorem consoleListed_step_0x2a65e (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run consoleListed [0x2a684] (n+1) ⟨s,f,0x2a65e⟩ =
      (X86Routine.execute (.control (.block (.load 2 ⟨none,none,0,0x2b3dc⟩))) ⟨s,f,0x2a664⟩).bind (X86Routine.run consoleListed [0x2a684] n) := by rfl

@[simp] theorem consoleListed_step_0x2a664 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run consoleListed [0x2a684] (n+1) ⟨s,f,0x2a664⟩ =
      (X86Routine.execute (.control (.block (.lea 0 ⟨none,some 2,3,0⟩))) ⟨s,f,0x2a66b⟩).bind (X86Routine.run consoleListed [0x2a684] n) := by rfl

@[simp] theorem consoleListed_step_0x2a66b (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run consoleListed [0x2a684] (n+1) ⟨s,f,0x2a66b⟩ =
      (X86Routine.execute (.control (.block (.arithmetic (.add 0 2)))) ⟨s,f,0x2a66d⟩).bind (X86Routine.run consoleListed [0x2a684] n) := by rfl

@[simp] theorem consoleListed_step_0x2a66d (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run consoleListed [0x2a684] (n+1) ⟨s,f,0x2a66d⟩ =
      (X86Routine.execute (.control (.block (.lea 0 ⟨none,some 0,2,0⟩))) ⟨s,f,0x2a674⟩).bind (X86Routine.run consoleListed [0x2a684] n) := by rfl

@[simp] theorem consoleListed_step_0x2a674 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run consoleListed [0x2a684] (n+1) ⟨s,f,0x2a674⟩ =
      (X86Routine.execute (.control (.block (.arithmetic (.sub 0 2)))) ⟨s,f,0x2a676⟩).bind (X86Routine.run consoleListed [0x2a684] n) := by rfl

@[simp] theorem consoleListed_step_0x2a676 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run consoleListed [0x2a684] (n+1) ⟨s,f,0x2a676⟩ =
      (X86Routine.execute (.control (.block (.lea 0 ⟨none,some 0,3,0⟩))) ⟨s,f,0x2a67d⟩).bind (X86Routine.run consoleListed [0x2a684] n) := by rfl

@[simp] theorem consoleListed_step_0x2a67d (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run consoleListed [0x2a684] (n+1) ⟨s,f,0x2a67d⟩ =
      (X86Routine.execute (.addImmediate 0 0x2ae78) ⟨s,f,0x2a682⟩).bind (X86Routine.run consoleListed [0x2a684] n) := by rfl

@[simp] theorem consoleListed_step_0x2a682 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run consoleListed [0x2a684] (n+1) ⟨s,f,0x2a682⟩ =
      (X86Routine.execute (.compareRegisters 5 0) ⟨s,f,0x2a684⟩).bind (X86Routine.run consoleListed [0x2a684] n) := by rfl

@[simp] theorem consoleListed_stop_0x2a684 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run consoleListed [0x2a684] n ⟨s,f,0x2a684⟩ = some ⟨s,f,0x2a684⟩ := by cases n <;> rfl
theorem consoleListed_contained (pc : Nat) (h : consoleListed pc ≠ none) : setupListed pc = consoleListed pc := by
  fun_cases consoleListed pc <;> simp_all [consoleListed,setupListed]
theorem consoleListed_active (pc : Nat) (h : consoleListed pc ≠ none) : pc ∉ [0x2a695,0x2a69a] := by
  fun_cases consoleListed pc <;> simp_all [consoleListed]

def branchListed : X86Routine.Program
  | 0x2a684 => some (.control (.jumpZero false 20),2)
  | 0x2a686 => some (.immediate 0 40,5)
  | 0x2a68b => some (.control (.block (.arithmetic (.add 3 3))),2)
  | 0x2a68d => some (.immediate 2 10,5)
  | 0x2a692 => some (.addImmediate 3 40,3)
  | _ => none

@[simp] theorem branchListed_step_0x2a684 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run branchListed [0x2a695,0x2a69a] (n+1) ⟨s,f,0x2a684⟩ =
      (X86Routine.execute (.control (.jumpZero false 20)) ⟨s,f,0x2a686⟩).bind (X86Routine.run branchListed [0x2a695,0x2a69a] n) := by rfl

@[simp] theorem branchListed_step_0x2a686 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run branchListed [0x2a695,0x2a69a] (n+1) ⟨s,f,0x2a686⟩ =
      (X86Routine.execute (.immediate 0 40) ⟨s,f,0x2a68b⟩).bind (X86Routine.run branchListed [0x2a695,0x2a69a] n) := by rfl

@[simp] theorem branchListed_step_0x2a68b (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run branchListed [0x2a695,0x2a69a] (n+1) ⟨s,f,0x2a68b⟩ =
      (X86Routine.execute (.control (.block (.arithmetic (.add 3 3)))) ⟨s,f,0x2a68d⟩).bind (X86Routine.run branchListed [0x2a695,0x2a69a] n) := by rfl

@[simp] theorem branchListed_step_0x2a68d (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run branchListed [0x2a695,0x2a69a] (n+1) ⟨s,f,0x2a68d⟩ =
      (X86Routine.execute (.immediate 2 10) ⟨s,f,0x2a692⟩).bind (X86Routine.run branchListed [0x2a695,0x2a69a] n) := by rfl

@[simp] theorem branchListed_step_0x2a692 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run branchListed [0x2a695,0x2a69a] (n+1) ⟨s,f,0x2a692⟩ =
      (X86Routine.execute (.addImmediate 3 40) ⟨s,f,0x2a695⟩).bind (X86Routine.run branchListed [0x2a695,0x2a69a] n) := by rfl

@[simp] theorem branchListed_stop_0x2a695 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run branchListed [0x2a695,0x2a69a] n ⟨s,f,0x2a695⟩ = some ⟨s,f,0x2a695⟩ := by cases n <;> rfl
@[simp] theorem branchListed_stop_0x2a69a (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run branchListed [0x2a695,0x2a69a] n ⟨s,f,0x2a69a⟩ = some ⟨s,f,0x2a69a⟩ := by cases n <;> rfl
theorem branchListed_contained (pc : Nat) (h : branchListed pc ≠ none) : setupListed pc = branchListed pc := by
  fun_cases branchListed pc <;> simp_all [branchListed,setupListed]
theorem branchListed_active (pc : Nat) (h : branchListed pc ≠ none) : pc ∉ [0x2a695,0x2a69a] := by
  fun_cases branchListed pc <;> simp_all [branchListed]

def capCore (s : X86Memory.State) := put s 3 (if (s.regs 7).toInt < 100 then s.regs 7 else (100#32))
def capResult (s : X86Memory.State) : X86Control.State := ⟨capCore s,some (compare32 (s.regs 7) 100),0x2a65e⟩
def consoleCore (s : X86Memory.State) := put (put s 2 (load32 s.memory (0x2b3dc#32))) 0 (console s)
def consoleResult (s : X86Memory.State) : X86Control.State :=
  ⟨consoleCore s,some (compare32 (s.regs 5) (console s)),0x2a684⟩
def branchResult (s : X86Memory.State) : X86Control.State :=
  if s.regs 5 = s.regs 0 then
    ⟨put (put (put s 0 (40#32)) 2 (10#32)) 3 (s.regs 3+s.regs 3+(40#32)),none,0x2a695⟩
  else ⟨s,some (compare32 (s.regs 5) (s.regs 0)),0x2a69a⟩
def setupResult (s : X86Memory.State) := branchResult (consoleCore (capCore s))

theorem cap_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run capListed [0x2a65e] 4 ⟨s,f,0x2a650⟩ = some (capResult s) := by
  by_cases cap : (s.regs 7).toInt < 100 <;>
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      put,write,blockPreservesFlags,PlayerHeight.cmp_ge_prop,← Int.not_lt,cap,capResult,capCore]

theorem console_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run consoleListed [0x2a684] 8 ⟨s,f,0x2a65e⟩ = some (consoleResult s) := by
  simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
    put,write,blockPreservesFlags,X86Block.Address.eval,consoleResult,consoleCore,console,
    BitVec.sub_eq_add_neg,BitVec.add_assoc]
  funext r
  by_cases r0 : r=0 <;> by_cases r2 : r=2 <;> simp [write,r0,r2]

theorem branch_execution (s : X86Memory.State) :
    X86Routine.run branchListed [0x2a695,0x2a69a] 5 ⟨s,some (compare32 (s.regs 5) (s.regs 0)),0x2a684⟩ =
      some (branchResult s) := by
  by_cases loc : s.regs 5 = s.regs 0
  all_goals
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
      put,write,blockPreservesFlags,cmp32_zero,loc,branchResult]
    all_goals funext r; by_cases r0 : r=0 <;> by_cases r2 : r=2 <;> by_cases r3 : r=3 <;> simp [write,r0,r2,r3]

theorem setup_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run setupListed [0x2a695,0x2a69a] 17 ⟨s,f,0x2a650⟩ = some (setupResult s) := by
  obtain ⟨n,hn,path,_⟩ := X86Routine.run_path (cap_execution s f)
  have path := path.transfer setupListed [0x2a695,0x2a69a] capListed_contained capListed_active
  obtain ⟨k,hk,cpath,_⟩ := X86Routine.run_path (console_execution (capCore s) (capResult s).flags)
  have cpath := cpath.transfer setupListed [0x2a695,0x2a69a] consoleListed_contained consoleListed_active
  have b := branch_execution (consoleCore (capCore s))
  have flags : (consoleResult (capCore s)).flags =
      some (compare32 ((consoleCore (capCore s)).regs 5) ((consoleCore (capCore s)).regs 0)) := by
    simp [consoleResult,consoleCore,put,write]
  rw [← flags] at b
  obtain ⟨j,hj,bpath,done⟩ := X86Routine.run_path b
  have bpath := bpath.transfer setupListed [0x2a695,0x2a69a] branchListed_contained branchListed_active
  have tail : X86Routine.run setupListed [0x2a695,0x2a69a] 5 (consoleResult (capCore s)) = some (setupResult s) :=
    bpath.finish (fuel := 0) (by simp [X86Routine.run,done,setupResult]) 5 (by omega)
  exact path.finish (cpath.finish tail 13 (by omega)) 17 (by omega)

def returned (s : X86Memory.State) : X86Control.State :=
  ⟨⟨s.regs,saved s⟩,some (compare32 0 0),0x2a69a⟩

theorem call_prefix (s : X86Memory.State) (f : Option Flags) (h : Inputs s) :
    X86Routine.Prefix callListed [0x2a69a] 13 ⟨s,f,0x2a695⟩ (returned s) := by
  have flag : load32 (saved s) (0x2923c#32) = (0#32) := (saved_frame s _ h.flagSafe).trans h.disabled
  simp [saved,BitVec.sub_eq_add_neg,BitVec.add_assoc] at flag
  have reads (a b : Fin 4) (ne : a ≠ b) (m : Memory) (v : Word) :=
    load_store_apart m (s.regs 4-BitVec.ofNat 32 (4*(b.val+1)))
      (s.regs 4-BitVec.ofNat 32 (4*(a.val+1))) v (stack_apart (s.regs 4) a b ne)
  have r01 (m : Memory) (v : Word) :
      load32 (store32 m (s.regs 4-(8#32)) v) (s.regs 4-(4#32)) =
        load32 m (s.regs 4-(4#32)) := reads 0 1 (by decide) m v
  have r02 (m : Memory) (v : Word) :
      load32 (store32 m (s.regs 4-(12#32)) v) (s.regs 4-(4#32)) =
        load32 m (s.regs 4-(4#32)) := reads 0 2 (by decide) m v
  have r03 (m : Memory) (v : Word) :
      load32 (store32 m (s.regs 4-(16#32)) v) (s.regs 4-(4#32)) =
        load32 m (s.regs 4-(4#32)) := reads 0 3 (by decide) m v
  have r12 (m : Memory) (v : Word) :
      load32 (store32 m (s.regs 4-(12#32)) v) (s.regs 4-(8#32)) =
        load32 m (s.regs 4-(8#32)) := reads 1 2 (by decide) m v
  have r13 (m : Memory) (v : Word) :
      load32 (store32 m (s.regs 4-(16#32)) v) (s.regs 4-(8#32)) =
        load32 m (s.regs 4-(8#32)) := reads 1 3 (by decide) m v
  have r23 (m : Memory) (v : Word) :
      load32 (store32 m (s.regs 4-(16#32)) v) (s.regs 4-(12#32)) =
        load32 m (s.regs 4-(12#32)) := reads 2 3 (by decide) m v
  simp [BitVec.sub_eq_add_neg,BitVec.add_assoc] at r01 r02 r03 r12 r13 r23
  let c := X86Routine.pushWord s (0x2a69a#32)
  let p1 := X86Routine.pushWord c (s.regs 1)
  let p2 := X86Routine.pushWord p1 (s.regs 6)
  let p3 := X86Routine.pushWord p2 (s.regs 7)
  let p4 := put p3 6 (s.regs 0)
  let p5 := put p4 1 (s.regs 2)
  let p6 := put p5 7 (s.regs 3)
  let p7 := put (put p6 4 (s.regs 4-(12#32))) 7 (s.regs 7)
  let p8 := put (put p7 4 (s.regs 4-(8#32))) 6 (s.regs 6)
  let p9 := put (put p8 4 (s.regs 4-(4#32))) 1 (s.regs 1)
  let p10 := put p9 4 (s.regs 4)
  apply X86Routine.Prefix.step (middle := ⟨c,f,0x1bb50⟩) (by simp)
    (show callListed 0x2a695 = some (.call (-60234),5) from by decide) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        X86Block.Address.eval,blockPreservesFlags,p10,p9,p8,p7,p6,p5,p4,p3,p2,p1,c,
        X86Routine.pushWord,put,write,cmp32_zero,flag,r01,r02,r03,r12,r13,r23,load_store,
        BitVec.sub_sub,BitVec.sub_eq_add_neg,BitVec.add_assoc])
  apply X86Routine.Prefix.step (middle := ⟨p1,f,0x1bb51⟩) (by simp)
    (show callListed 0x1bb50 = some (.push 1,1) from by decide) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        X86Block.Address.eval,blockPreservesFlags,p10,p9,p8,p7,p6,p5,p4,p3,p2,p1,c,
        X86Routine.pushWord,put,write,cmp32_zero,flag,r01,r02,r03,r12,r13,r23,load_store,
        BitVec.sub_sub,BitVec.sub_eq_add_neg,BitVec.add_assoc])
  apply X86Routine.Prefix.step (middle := ⟨p2,f,0x1bb52⟩) (by simp)
    (show callListed 0x1bb51 = some (.push 6,1) from by decide) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        X86Block.Address.eval,blockPreservesFlags,p10,p9,p8,p7,p6,p5,p4,p3,p2,p1,c,
        X86Routine.pushWord,put,write,cmp32_zero,flag,r01,r02,r03,r12,r13,r23,load_store,
        BitVec.sub_sub,BitVec.sub_eq_add_neg,BitVec.add_assoc])
  apply X86Routine.Prefix.step (middle := ⟨p3,f,0x1bb53⟩) (by simp)
    (show callListed 0x1bb52 = some (.push 7,1) from by decide) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        X86Block.Address.eval,blockPreservesFlags,p10,p9,p8,p7,p6,p5,p4,p3,p2,p1,c,
        X86Routine.pushWord,put,write,cmp32_zero,flag,r01,r02,r03,r12,r13,r23,load_store,
        BitVec.sub_sub,BitVec.sub_eq_add_neg,BitVec.add_assoc])
  apply X86Routine.Prefix.step (middle := ⟨p4,f,0x1bb55⟩) (by simp)
    (show callListed 0x1bb53 = some (.control (.block (.legacy (.mov 6 0))),2) from by decide) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        X86Block.Address.eval,blockPreservesFlags,p10,p9,p8,p7,p6,p5,p4,p3,p2,p1,c,
        X86Routine.pushWord,put,write,cmp32_zero,flag,r01,r02,r03,r12,r13,r23,load_store,
        BitVec.sub_sub,BitVec.sub_eq_add_neg,BitVec.add_assoc])
  apply X86Routine.Prefix.step (middle := ⟨p5,f,0x1bb57⟩) (by simp)
    (show callListed 0x1bb55 = some (.control (.block (.legacy (.mov 1 2))),2) from by decide) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        X86Block.Address.eval,blockPreservesFlags,p10,p9,p8,p7,p6,p5,p4,p3,p2,p1,c,
        X86Routine.pushWord,put,write,cmp32_zero,flag,r01,r02,r03,r12,r13,r23,load_store,
        BitVec.sub_sub,BitVec.sub_eq_add_neg,BitVec.add_assoc])
  apply X86Routine.Prefix.step (middle := ⟨p6,f,0x1bb59⟩) (by simp)
    (show callListed 0x1bb57 = some (.control (.block (.legacy (.mov 7 3))),2) from by decide) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        X86Block.Address.eval,blockPreservesFlags,p10,p9,p8,p7,p6,p5,p4,p3,p2,p1,c,
        X86Routine.pushWord,put,write,cmp32_zero,flag,r01,r02,r03,r12,r13,r23,load_store,
        BitVec.sub_sub,BitVec.sub_eq_add_neg,BitVec.add_assoc])
  apply X86Routine.Prefix.step (middle := ⟨p6,some (compare32 0 0),0x1bb60⟩) (by simp)
    (show callListed 0x1bb59 = some (.control (.cmpImmediate ⟨none,none,0,0x2923c⟩ 0),7) from by decide) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        X86Block.Address.eval,blockPreservesFlags,p10,p9,p8,p7,p6,p5,p4,p3,p2,p1,c,
        X86Routine.pushWord,put,write,cmp32_zero,flag,r01,r02,r03,r12,r13,r23,load_store,
        BitVec.sub_sub,BitVec.sub_eq_add_neg,BitVec.add_assoc])
  apply X86Routine.Prefix.step (middle := ⟨p6,some (compare32 0 0),0x1bc41⟩) (by simp)
    (show callListed 0x1bb60 = some (.control (.jumpZero true 219),6) from by decide) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        X86Block.Address.eval,blockPreservesFlags,p10,p9,p8,p7,p6,p5,p4,p3,p2,p1,c,
        X86Routine.pushWord,put,write,cmp32_zero,flag,r01,r02,r03,r12,r13,r23,load_store,
        BitVec.sub_sub,BitVec.sub_eq_add_neg,BitVec.add_assoc])
  apply X86Routine.Prefix.step (middle := ⟨p7,some (compare32 0 0),0x1bc42⟩) (by simp)
    (show callListed 0x1bc41 = some (.pop 7,1) from by decide) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        X86Block.Address.eval,blockPreservesFlags,p10,p9,p8,p7,p6,p5,p4,p3,p2,p1,c,
        X86Routine.pushWord,put,write,cmp32_zero,flag,r01,r02,r03,r12,r13,r23,load_store,
        BitVec.sub_sub,BitVec.sub_eq_add_neg,BitVec.add_assoc])
  apply X86Routine.Prefix.step (middle := ⟨p8,some (compare32 0 0),0x1bc43⟩) (by simp)
    (show callListed 0x1bc42 = some (.pop 6,1) from by decide) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        X86Block.Address.eval,blockPreservesFlags,p10,p9,p8,p7,p6,p5,p4,p3,p2,p1,c,
        X86Routine.pushWord,put,write,cmp32_zero,flag,r01,r02,r03,r12,r13,r23,load_store,
        BitVec.sub_sub,BitVec.sub_eq_add_neg,BitVec.add_assoc])
  apply X86Routine.Prefix.step (middle := ⟨p9,some (compare32 0 0),0x1bc44⟩) (by simp)
    (show callListed 0x1bc43 = some (.pop 1,1) from by decide) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        X86Block.Address.eval,blockPreservesFlags,p10,p9,p8,p7,p6,p5,p4,p3,p2,p1,c,
        X86Routine.pushWord,put,write,cmp32_zero,flag,r01,r02,r03,r12,r13,r23,load_store,
        BitVec.sub_sub,BitVec.sub_eq_add_neg,BitVec.add_assoc])
  apply X86Routine.Prefix.step (middle := ⟨p10,some (compare32 0 0),0x2a69a⟩) (by simp)
    (show callListed 0x1bc44 = some (.ret,1) from by decide) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        X86Block.Address.eval,blockPreservesFlags,p10,p9,p8,p7,p6,p5,p4,p3,p2,p1,c,
        X86Routine.pushWord,put,write,cmp32_zero,flag,r01,r02,r03,r12,r13,r23,load_store,
        BitVec.sub_sub,BitVec.sub_eq_add_neg,BitVec.add_assoc])
  have eq : p10 = (returned s).core := by
    simp [p10,p9,p8,p7,p6,p5,p4,p3,p2,p1,c,returned,saved,X86Routine.pushWord,put,write,
      BitVec.sub_sub,BitVec.sub_eq_add_neg,BitVec.add_assoc]
    funext r
    by_cases r1 : r=1 <;> by_cases r4 : r=4 <;> by_cases r6 : r=6 <;> by_cases r7 : r=7 <;>
      simp [write,r1,r4,r6,r7]
  rw [eq]
  exact X86Routine.Prefix.nil _

theorem call_execution (s : X86Memory.State) (f : Option Flags) (h : Inputs s) :
    X86Routine.run callListed [0x2a69a] 13 ⟨s,f,0x2a695⟩ = some (returned s) :=
  (call_prefix s f h).finish (fuel := 0) (by simp [X86Routine.run,returned]) 13 (by decide)

def bodyResult (s : X86Memory.State) : X86Control.State :=
  let hp := load32 s.memory (s.regs 6+(108#32))-s.regs 7
  ⟨⟨write s.regs 3 hp,store32 s.memory (s.regs 6+(108#32)) hp⟩,some (logical32 hp),
    if 0 < hp.toInt then 0x2a6b6 else 0x2a6a6⟩

theorem body_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run bodyListed [0x2a6a6,0x2a6b6] 5 ⟨s,f,0x2a69a⟩ = some (bodyResult s) := by
  by_cases alive : 0 < (load32 s.memory (s.regs 6+(108#32))-s.regs 7).toInt
  all_goals
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
      put,write,blockPreservesFlags,X86Block.Address.eval,PlayerHeight.logical_le,← Int.not_lt,
      alive,bodyResult,-BitVec.toInt_sub]
    all_goals funext r; by_cases r3 : r=3 <;> simp [write,r3]

theorem execution (s : X86Memory.State) (f : Option Flags) (h : Inputs s) :
    (X86Routine.run listed [0x2a6a6,0x2a6b6] 35 ⟨s,f,0x2a650⟩).map
      (fun t => (t.core.memory,t.core.regs 5,t.core.regs 4,t.core.regs 6,t.core.regs 7,t.pc)) =
      some (resultMemory s,s.regs 5,s.regs 4,s.regs 6,s.regs 7,exitPC s) := by
  have setup := setup_execution s f
  obtain ⟨n,hn,path,_⟩ := X86Routine.run_path setup
  have path := path.transfer listed [0x2a6a6,0x2a6b6] setupListed_contained setupListed_active
  let g := setupResult s
  have normalized : g =
      let capped := if (s.regs 7).toInt < 100 then s.regs 7 else (100#32)
      let rs := write (write (write s.regs 3 capped) 2 (load32 s.memory (0x2b3dc#32))) 0 (console s)
      if localPlayer s then
        ⟨⟨write (write (write rs 0 (40#32)) 2 (10#32)) 3 (capped+capped+(40#32)),s.memory⟩,none,0x2a695⟩
      else ⟨⟨rs,s.memory⟩,some (compare32 (s.regs 5) (console s)),0x2a69a⟩ := by
    simp only [g,setupResult,branchResult,consoleCore,show console (capCore s) = console s from rfl]
    simp [capCore,put,write,localPlayer]
  by_cases loc : localPlayer s
  · have gp : g.pc = 0x2a695 := by simp only [normalized,if_pos loc]
    have sameMemory : g.core.memory = s.memory := by simp only [normalized,if_pos loc]
    have regs (r : Reg) (ne0 : r ≠ 0) (ne2 : r ≠ 2) (ne3 : r ≠ 3) : g.core.regs r = s.regs r := by
      simp only [normalized,if_pos loc]
      simp [write,ne0,ne2,ne3]
    have sp := regs 4 (by decide) (by decide) (by decide)
    have obj := regs 6 (by decide) (by decide) (by decide)
    have dmg := regs 7 (by decide) (by decide) (by decide)
    have player := regs 5 (by decide) (by decide) (by decide)
    have ecx := regs 1 (by decide) (by decide) (by decide)
    have hi : Inputs g.core := by
      constructor
      · rw [sameMemory]; exact h.disabled
      · simpa [slots,sp] using h.flagSafe
    have call := call_execution g.core g.flags hi
    rw [← gp] at call
    obtain ⟨k,hk,cpath,_⟩ := X86Routine.run_path call
    have cpath := cpath.transfer listed [0x2a6a6,0x2a6b6] callListed_contained callListed_active
    have body := body_execution (returned g.core).core (returned g.core).flags
    obtain ⟨j,hj,bpath,done⟩ := X86Routine.run_path body
    have bpath := bpath.transfer listed [0x2a6a6,0x2a6b6] bodyListed_contained bodyListed_active
    have finalRun : X86Routine.run listed [0x2a6a6,0x2a6b6] 5 (returned g.core) =
        some (bodyResult (returned g.core).core) :=
      bpath.finish (fuel := 0) (by simp [X86Routine.run,done]) 5 (by omega)
    have allRun := path.finish (cpath.finish finalRun 18 (by omega)) 35 (by omega)
    rw [allRun]
    simp only [resultMemory,exitPC,remainingHealth,beforeHealth,if_pos loc]
    simp [bodyResult,returned,saved,
      sp,obj,dmg,player,ecx,sameMemory,write]
  · have gp : g.pc = 0x2a69a := by simp [normalized,loc]
    have body := body_execution g.core g.flags
    rw [← gp] at body
    obtain ⟨j,hj,bpath,done⟩ := X86Routine.run_path body
    have bpath := bpath.transfer listed [0x2a6a6,0x2a6b6] bodyListed_contained bodyListed_active
    have finalRun : X86Routine.run listed [0x2a6a6,0x2a6b6] 5 g = some (bodyResult g.core) :=
      bpath.finish (fuel := 0) (by simp [X86Routine.run,done]) 5 (by omega)
    have allRun := path.finish finalRun 35 (by omega)
    rw [allRun]
    simp only [resultMemory,exitPC,remainingHealth,beforeHealth,if_neg loc,normalized]
    simp [bodyResult,write]

theorem original_execution (s : X86Memory.State) (f : Option Flags) (h : Inputs s) :
    (X86Routine.run program [0x2a6a6,0x2a6b6] 35 ⟨s,f,0x2a650⟩).map
      (fun t => (t.core.memory,t.core.regs 5,t.core.regs 4,t.core.regs 6,t.core.regs 7,t.pc)) =
      some (resultMemory s,s.regs 5,s.regs 4,s.regs 6,s.regs 7,exitPC s) := by
  have run := execution s f h
  have valid : X86Routine.run listed [0x2a6a6,0x2a6b6] 35 ⟨s,f,0x2a650⟩ ≠ none := by
    intro hn; rw [hn] at run; contradiction
  rw [X86Routine.run_sound program listed decoded _ _ _ valid]
  exact run

def writes (s : X86Memory.State) := slots s ++ [s.regs 6+(108#32)]
theorem memory_frame (s : X86Memory.State) : PlayerHeight.Frame s.memory (resultMemory s) (writes s) := by
  intro a safe
  rw [resultMemory,load_store_apart _ _ _ _ (safe _ (by simp [writes]))]
  unfold beforeHealth
  split
  · exact saved_frame s a (fun b hb => safe b (by simp [writes,hb]))
  · rfl

theorem health_value (s : X86Memory.State) (hp : Word)
    (encoded : load32 s.memory (s.regs 6+(108#32)) = hp)
    (safe : ∀ a, a ∈ slots s → Apart (s.regs 6+(108#32)) a) :
    remainingHealth s = hp-s.regs 7 := by
  unfold remainingHealth beforeHealth
  split
  · rw [saved_frame s _ safe,encoded]
  · rw [encoded]

def joined (pc : Nat) : Option (X86Routine.Op × Nat) :=
  if (0x2a650 ≤ pc ∧ pc < 0x2a6a6) ∨ (0x1bb50 ≤ pc ∧ pc < 0x1bb66) ∨
      (0x1bc41 ≤ pc ∧ pc < 0x1bc45) then program pc else PlayerHealth.joined pc

theorem contains_health (pc : Nat) (h : PlayerHealth.joined pc ≠ none) :
    joined pc = PlayerHealth.joined pc := by
  unfold joined
  split
  next bounds =>
    have b1 : ¬(0x2a616 ≤ pc ∧ pc < 0x2a650) := by omega
    have b2 : ¬(0x2a460 ≤ pc ∧ pc < 0x2a5d5) := by omega
    have b3 : ¬(0x2a5d5 ≤ pc ∧ pc < 0x2a616) := by omega
    simp [PlayerHealth.joined,PlayerDamageEntry.program,PlayerDamageEntry.bytesProgram,b1,b2,b3,
      show pc ≠ 0x2fb76 by omega,show pc ≠ 0x2fba0 by omega,show pc ≠ 0x2fbd2 by omega] at h
  next => rfl

theorem health_active (pc : Nat) (h : PlayerHealth.joined pc ≠ none) : pc ∉ [0x2a6a6,0x2a6b6,0x2a747] := by
  intro mem
  simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at mem
  rcases mem with rfl | rfl | rfl <;> contradiction

theorem contains_actor (pc : Nat) (h : program pc ≠ none) : joined pc = program pc := by
  unfold joined
  split
  next => rfl
  next hn =>
    simp only [program,bytesProgram] at h
    have b1 : ¬(0x2a650 ≤ pc ∧ pc < 0x2a6a6) := by omega
    have b2 : ¬(0x1bb50 ≤ pc ∧ pc < 0x1bb66) := by omega
    have b3 : ¬(0x1bc41 ≤ pc ∧ pc < 0x1bc45) := by omega
    simp [b1,b2,b3] at h

theorem actor_active (pc : Nat) (h : program pc ≠ none) : pc ∉ [0x2a6a6,0x2a6b6,0x2a747] := by
  intro mem
  simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at mem
  rcases mem with rfl | rfl | rfl <;> contradiction

/-- Tactile stack slots measured from the initial floor CALL boundary. -/
def callSlots (s : X86Memory.State) : List Word :=
  [s.regs 4-(32#32),s.regs 4-(36#32),s.regs 4-(40#32),s.regs 4-(44#32)]
def fields (s : X86Memory.State) : List Word :=
  let p := PlayerDamageEntry.inputPlayer s
  [p+(36#32),p+(40#32),p+(32#32),p+(220#32),p+(228#32)]

structure JoinedInputs (s : X86Memory.State) (v : PlayerDamage.State) (d : Int32) (baby : Bool)
    extends toHealth : PlayerHealth.Inputs s v d baby where
  tactileDisabled : load32 s.memory (0x2923c#32) = 0
  earlierSafe : ∀ a, a ∈ [s.regs 0+(108#32),(0x2923c#32)] →
    ∀ b, b ∈ PlayerHealth.writes s → Apart a b
  tactileSafe : ∀ a, a ∈ (s.regs 0+(108#32)) :: (0x2923c#32) :: fields s →
    ∀ b, b ∈ callSlots s → Apart a b
  actorSafe : ∀ a, a ∈ fields s → Apart a (s.regs 0+(108#32))

def observation (s : X86Memory.State) (t : X86Control.State) :=
  (PlayerHealth.observation s t,
    if t.pc = 0x2a747 then none else some
      (load32 t.core.memory (s.regs 0+(108#32)),decide (t.pc = 0x2a6a6)))
def answer (v : PlayerDamage.State) (d : Int32) (baby : Bool) :=
  (PlayerHealth.answer v d baby,
    if PlayerDamageEntry.accepted v d baby then
      let a := PlayerDamage.absorbArmor v (PlayerDamageEntry.skillDamage d baby)
      some ((v.health-a.2).toBitVec,decide (v.health-a.2 ≤ 0))
    else none)
def joinedWrites (s : X86Memory.State) := PlayerHealth.writes s ++ callSlots s ++ [s.regs 0+(108#32)]

def afterWrites (s : X86Memory.State) := PlayerHealth.afterWrites s ++ callSlots s ++ [s.regs 0+(108#32)]

/-- Continuous run ending immediately before the death continuation or pain
continuation. No RNG or kill routine is silently executed by this theorem. -/
theorem joined_execution_detailed (s : X86Memory.State) (f : Option Flags) (pc : Nat)
    (site : pc ∈ PlayerDamageEntry.sites) (v : PlayerDamage.State) (d : Int32) (baby : Bool)
    (h : JoinedInputs s v d baby) :
    ∃ t, X86Routine.run joined [0x2a6a6,0x2a6b6,0x2a747] 108 ⟨s,f,pc⟩ = some t ∧
      observation s t = answer v d baby ∧ t.core.regs 4 = s.regs 4-(28#32) ∧
      t.core.regs 6 = s.regs 0 ∧ PlayerHeight.Frame s.memory t.core.memory (joinedWrites s) ∧
      PlayerHeight.Frame (PlayerDamageEntry.saved s pc) t.core.memory (afterWrites s) := by
  obtain ⟨g,grun,gobs,gpc,gsp,gobj,gframe,gplayer,gsaved⟩ :=
    PlayerHealth.joined_execution_detailed s f pc site v d baby h.toHealth
  obtain ⟨n,hn,path,_⟩ := X86Routine.run_path grun
  have path := path.transfer joined [0x2a6a6,0x2a6b6,0x2a747] contains_health health_active
  by_cases accept : PlayerDamageEntry.accepted v d baby = true
  · simp only [accept,if_true] at gpc
    have stack : slots g.core = callSlots s := by
      simp [slots,callSlots,gsp,BitVec.sub_sub]
    have ins : Inputs g.core := by
      constructor
      · exact (gframe _ (h.earlierSafe _ (by simp))).trans h.tactileDisabled
      · intro a ha
        rw [stack] at ha
        exact h.tactileSafe _ (by simp) a ha
    have body : load32 g.core.memory (g.core.regs 6+(108#32)) = v.health.toBitVec := by
      rw [gobj,gframe _ (h.earlierSafe _ (by simp))]
      exact h.health
    have bodySafe : ∀ a, a ∈ slots g.core → Apart (g.core.regs 6+(108#32)) a := by
      intro a ha
      rw [stack] at ha
      rw [gobj]
      exact h.tactileSafe _ (by simp) a ha
    have damage : g.core.regs 7 =
        (PlayerDamage.absorbArmor v (PlayerDamageEntry.skillDamage d baby)).2.toBitVec := by
      have obs := gobs
      simp only [PlayerHealth.observation,PlayerHealth.answer,gpc,accept,if_true,
        show (0x2a650:Nat) ≠ 0x2a747 by decide,if_false,Option.some.injEq,Prod.mk.injEq] at obs
      exact obs.1
    have value := health_value g.core v.health.toBitVec body bodySafe
    rw [damage,← Int32.toBitVec_sub] at value
    have run := original_execution g.core g.flags ins
    rw [← gpc] at run
    cases hr : X86Routine.run program [0x2a6a6,0x2a6b6] 35 g with
    | none => simp [hr] at run
    | some t =>
      obtain ⟨k,hk,tail,_⟩ := X86Routine.run_path hr
      have tail := tail.transfer joined [0x2a6a6,0x2a6b6,0x2a747] contains_actor actor_active
      simp only [hr,Option.map_some,Option.some.injEq,Prod.mk.injEq] at run
      rcases run with ⟨tm,tp,ts,to,td,tpc⟩
      have endmem : t.pc ∈ [0x2a6a6,0x2a6b6,0x2a747] := by
        rw [tpc]; unfold exitPC; split <;> simp
      have rest : X86Routine.run joined [0x2a6a6,0x2a6b6,0x2a747] 35 g = some t :=
        tail.finish (fuel := 0) (by simp [X86Routine.run,endmem]) 35 (by omega)
      have keep (a : Word) (mem : a ∈ fields s) : load32 t.core.memory a = load32 g.core.memory a := by
        rw [tm]
        apply memory_frame
        intro b hb
        simp only [writes,List.mem_append,List.mem_singleton] at hb
        rcases hb with slot | rfl
        · rw [stack] at slot
          exact h.tactileSafe a (by simp [mem]) b slot
        · rw [gobj]; exact h.actorSafe a mem
      have keep36 := keep (PlayerDamageEntry.inputPlayer s+(36#32)) (by simp [fields])
      have keep40 := keep (PlayerDamageEntry.inputPlayer s+(40#32)) (by simp [fields])
      have keep32 := keep (PlayerDamageEntry.inputPlayer s+(32#32)) (by simp [fields])
      have keep220 := keep (PlayerDamageEntry.inputPlayer s+(220#32)) (by simp [fields])
      have keep228 := keep (PlayerDamageEntry.inputPlayer s+(228#32)) (by simp [fields])
      have observed : PlayerHealth.observation s t = PlayerHealth.observation s g := by
        have npc : t.pc ≠ 0x2a747 := by rw [tpc]; unfold exitPC; split <;> decide
        simp [PlayerHealth.observation,npc,gpc,td,
          keep36,keep40,keep32,keep220,keep228]
      refine ⟨t,path.finish rest 108 (by omega),?_,ts.trans gsp,to.trans gobj,?_,?_⟩
      · rw [observation,observed,gobs]
        simp only [answer,accept,if_true,tm,tpc]
        have health : load32 (resultMemory g.core) (s.regs 0+(108#32)) = remainingHealth g.core := by
          rw [← gobj,resultMemory,load_store]
        rw [health,value]
        simp only [exitPC,value,Int32.toInt_toBitVec]
        by_cases alive : 0 < (v.health-(PlayerDamage.absorbArmor v (PlayerDamageEntry.skillDamage d baby)).2).toInt
        · have notdead : ¬(v.health-(PlayerDamage.absorbArmor v (PlayerDamageEntry.skillDamage d baby)).2) ≤ 0 := by
            rw [Int32.le_iff_toInt_le]; exact Int.not_le.mpr alive
          simp [alive,notdead,-Int32.toInt_sub]
        · have dead : (v.health-(PlayerDamage.absorbArmor v (PlayerDamageEntry.skillDamage d baby)).2) ≤ 0 := by
            rw [Int32.le_iff_toInt_le]; exact Int.not_lt.mp alive
          simp [alive,dead,-Int32.toInt_sub]
      · intro a safe
        rw [tm,memory_frame g.core a]
        · exact gframe a (fun b hb => safe b (by simp [joinedWrites,hb]))
        · intro b hb
          apply safe
          simpa [joinedWrites,writes,stack,gobj] using Or.inr hb
      · intro a safe
        rw [tm,memory_frame g.core a]
        · exact gsaved a (fun b hb => safe b (by simp [afterWrites,hb]))
        · intro b hb
          apply safe
          simpa [afterWrites,writes,stack,gobj] using Or.inr hb
  · have reject : PlayerDamageEntry.accepted v d baby = false := by simpa using accept
    simp only [reject,Bool.false_eq_true,if_false] at gpc
    refine ⟨g,path.finish (fuel := 0) (by simp [X86Routine.run,gpc]) 108 (by omega),
      ?_,gsp,gobj,?_,?_⟩
    · simp [observation,answer,gobs,reject,gpc]
    · intro a safe
      exact gframe a (fun b hb => safe b (by simp [joinedWrites,hb]))

    · intro a safe
      exact gsaved a (fun b hb => safe b (by simp [afterWrites,hb]))

theorem joined_execution (s : X86Memory.State) (f : Option Flags) (pc : Nat)
    (site : pc ∈ PlayerDamageEntry.sites) (v : PlayerDamage.State) (d : Int32) (baby : Bool)
    (h : JoinedInputs s v d baby) :
    ∃ t, X86Routine.run joined [0x2a6a6,0x2a6b6,0x2a747] 108 ⟨s,f,pc⟩ = some t ∧
      observation s t = answer v d baby ∧ t.core.regs 4 = s.regs 4-(28#32) ∧
      t.core.regs 6 = s.regs 0 ∧ PlayerHeight.Frame s.memory t.core.memory (joinedWrites s) := by
  obtain ⟨t,run,obs,sp,obj,frame,_⟩ := joined_execution_detailed s f pc site v d baby h
  exact ⟨t,run,obs,sp,obj,frame⟩

def liveObservation (v : PlayerDamage.State) (out : PlayerDamage.Result) :=
  (PlayerHealth.liveObservation v out,
    if out.applied then some (out.state.health.toBitVec,out.killed) else none)

theorem finish_actor (v : PlayerDamage.State) (d : Int32) (rng : DoomRandom) :
    (if (PlayerDamage.finish v d rng).applied then
      some ((PlayerDamage.finish v d rng).state.health.toBitVec,(PlayerDamage.finish v d rng).killed) else none) =
      let a := PlayerDamage.absorbArmor v d
      some ((v.health-a.2).toBitVec,decide (v.health-a.2 ≤ 0)) := by
  have health : (PlayerDamage.absorbArmor v d).1.health = v.health := by
    unfold PlayerDamage.absorbArmor
    split <;> rfl
  unfold PlayerDamage.finish
  simp only [Id.run,pure,bind,PlayerDamage.bookkeep,health]
  split <;> simp_all

theorem live_answer (v : PlayerDamage.State) (d : Int32) (baby : Bool) (rng : DoomRandom)
    (skull : v.skullFly = false) (ordinary : v.sectorSpecial ≠ 11) :
    liveObservation v (PlayerDamage.apply v d none false baby rng) = answer v d baby := by
  unfold liveObservation answer
  rw [PlayerHealth.live_answer v d baby rng skull ordinary]
  apply congrArg (fun x => (PlayerHealth.answer v d baby,x))
  rw [PlayerDamageEntry.live_entry v d baby false rng skull ordinary]
  by_cases h : PlayerDamageEntry.accepted v d baby = true
  · simp only [h,if_true,finish_actor]
  · simp [h]

/-- The original health store and death/survival branch agree with actual live
player damage under the initial ordinary-floor and disabled-device contract. -/
theorem live_correspondence (s : X86Memory.State) (f : Option Flags) (pc : Nat)
    (site : pc ∈ PlayerDamageEntry.sites) (v : PlayerDamage.State) (d : Int32)
    (baby : Bool) (rng : DoomRandom) (h : JoinedInputs s v d baby) :
    (X86Routine.run joined [0x2a6a6,0x2a6b6,0x2a747] 108 ⟨s,f,pc⟩).map (observation s) =
      some (liveObservation v (PlayerDamage.apply v d none false baby rng)) := by
  obtain ⟨t,run,obs,_⟩ := joined_execution s f pc site v d baby h
  rw [live_answer v d baby rng h.liveSkull h.liveOrdinary]
  simp [run,obs]

end Doom.Proofs.ActorHealth
