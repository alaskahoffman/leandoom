import Doom.Proofs.E1M1WeaponFire
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.WeaponFallback
open Verification X86 X86Memory X86Control BlockSummary
def code : List UInt8 := [0x31,0xd2,0xbb,0x2,0x0,0x0,0x0,0x3b,0x90,0x8c,0x0,0x0,0x0,0x74,0x1c,0x3b,0x90,0xa4,0x0,0x0,0x0,0x74,0x14,0x3b,0x15,0xac,0xa3,0x2,0x0,0x75,0xc,0xc7,0x40,0x74,0x5,0x0,0x0,0x0,0xe9,0xbc,0x0,0x0,0x0,0x3b,0x90,0x98,0x0,0x0,0x0,0x74,0x1c,0x3b,0x98,0xa0,0x0,0x0,0x0,0x7d,0x14,0x3b,0x15,0xbc,0xa3,0x2,0x0,0x74,0xc,0xc7,0x40,0x74,0x8,0x0,0x0,0x0,0xe9,0x98,0x0,0x0,0x0,0x3b,0x90,0x84,0x0,0x0,0x0,0x74,0x14,0x3b,0x90,0x9c,0x0,0x0,0x0,0x74,0xc,0xc7,0x40,0x74,0x3,0x0,0x0,0x0,0xe9,0x7c,0x0,0x0,0x0,0x3b,0x90,0x80,0x0,0x0,0x0,0x74,0x10,0x3b,0x90,0xa0,0x0,0x0,0x0,0x74,0x8,0x89,0x58,0x74,0xe9,0x64,0x0,0x0,0x0,0x8b,0x88,0x9c,0x0,0x0,0x0,0x39,0xca,0x74,0x9,0xc7,0x40,0x74,0x1,0x0,0x0,0x0,0xeb,0x51,0x8b,0xb0,0x94,0x0,0x0,0x0,0x39,0xf1,0x74,0x9,0xc7,0x40,0x74,0x7,0x0,0x0,0x0,0xeb,0x3e,0x3b,0xb0,0x88,0x0,0x0,0x0,0x74,0x11,0x3b,0xb0,0xa8,0x0,0x0,0x0,0x74,0x9,0xc7,0x40,0x74,0x4,0x0,0x0,0x0,0xeb,0x25,0x3b,0x90,0x90,0x0,0x0,0x0,0x74,0x1a,0x83,0xb8,0xa4,0x0,0x0,0x0,0x28,0x7e,0x11,0x3b,0x15,0xac,0xa3,0x2,0x0,0x75,0x9,0xc7,0x40,0x74,0x6,0x0,0x0,0x0,0xeb,0x3,0x89,0x50,0x74,0x83,0x78,0x74,0xa,0xf,0x84,0x16,0xff,0xff,0xff,0x8b,0x58,0x70,0x8d,0x14,0x9d,0x0,0x0,0x0,0x0,0x29,0xda,0x8b,0x1c,0xd5,0x98,0x2d,0x1,0x0,0x31,0xd2,0xe8,0x96,0xfd,0xff,0xff,0x31,0xc0,0x5e,0x5a,0x59,0x5b,0xc3]
def bytesProgram (bs : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2d19f ≤ pc ∧ pc < 0x2d2b1 then X86Routine.decodeAt bs (pc-0x2d19f) else none
def program := bytesProgram code
/-- Only instructions on the supported-inventory path are listed here. Other
inventory branches are neither replaced nor treated as successful exits. -/
def listed : X86Routine.Program
  | 0x2d19f => some (.xorRegister 2 2,2)
  | 0x2d1a1 => some (.immediate 3 2,5)
  | 0x2d1a6 => some (.control (.cmpMemory 2 ⟨some 0,none,0,140⟩),6)
  | 0x2d1ac => some (.control (.jumpZero true 28),2)
  | 0x2d1ca => some (.control (.cmpMemory 2 ⟨some 0,none,0,152⟩),6)
  | 0x2d1d0 => some (.control (.jumpZero true 28),2)
  | 0x2d1ee => some (.control (.cmpMemory 2 ⟨some 0,none,0,132⟩),6)
  | 0x2d1f4 => some (.control (.jumpZero true 20),2)
  | 0x2d20a => some (.control (.cmpMemory 2 ⟨some 0,none,0,128⟩),6)
  | 0x2d210 => some (.control (.jumpZero true 16),2)
  | 0x2d212 => some (.control (.cmpMemory 2 ⟨some 0,none,0,160⟩),6)
  | 0x2d218 => some (.control (.jumpZero true 8),2)
  | 0x2d21a => some (.control (.block (.store ⟨some 0,none,0,116⟩ 3)),3)
  | 0x2d21d => some (.jump 100,5)
  | 0x2d222 => some (.control (.block (.load 1 ⟨some 0,none,0,156⟩)),6)
  | 0x2d228 => some (.compareRegisters 2 1,2)
  | 0x2d22a => some (.control (.jumpZero true 9),2)
  | 0x2d22c => some (.storeImmediate ⟨some 0,none,0,116⟩ 1,7)
  | 0x2d233 => some (.jump 81,2)
  | 0x2d235 => some (.control (.block (.load 6 ⟨some 0,none,0,148⟩)),6)
  | 0x2d23b => some (.compareRegisters 1 6,2)
  | 0x2d23d => some (.control (.jumpZero true 9),2)
  | 0x2d248 => some (.control (.cmpMemory 6 ⟨some 0,none,0,136⟩),6)
  | 0x2d24e => some (.control (.jumpZero true 17),2)
  | 0x2d261 => some (.control (.cmpMemory 2 ⟨some 0,none,0,144⟩),6)
  | 0x2d267 => some (.control (.jumpZero true 26),2)
  | 0x2d283 => some (.control (.block (.store ⟨some 0,none,0,116⟩ 2)),3)
  | 0x2d286 => some (.control (.cmpImmediate ⟨some 0,none,0,116⟩ 10),4)
  | 0x2d28a => some (.control (.jumpZero true (-234)),6)
  | 0x2d290 => some (.control (.block (.legacy (.load 3 0 112))),3)
  | 0x2d293 => some (.control (.block (.lea 2 ⟨none,some 3,2,0⟩)),7)
  | 0x2d29a => some (.control (.block (.arithmetic (.sub 2 3))),2)
  | 0x2d29c => some (.control (.block (.load 3 ⟨none,some 2,3,0x12d98⟩)),7)
  | 0x2d2a3 => some (.xorRegister 2 2,2)
  | 0x2d2a5 => some (.call (-618),5)
  | 0x2d2aa => some (.xorRegister 0 0,2)
  | 0x2d2ac => some (.pop 6,1)
  | 0x2d2ad => some (.pop 2,1)
  | 0x2d2ae => some (.pop 1,1)
  | 0x2d2af => some (.pop 3,1)
  | 0x2d2b0 => some (.ret,1)
  | _ => none
theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide
@[local simp] theorem step_2d19f (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d20a] (n+1) ⟨s,f,0x2d19f⟩ =
      (X86Routine.execute (.xorRegister 2 2) ⟨s,f,0x2d1a1⟩).bind (X86Routine.run listed [0x2d20a] n) := by rfl
@[local simp] theorem step_2d1a1 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d20a] (n+1) ⟨s,f,0x2d1a1⟩ =
      (X86Routine.execute (.immediate 3 2) ⟨s,f,0x2d1a6⟩).bind (X86Routine.run listed [0x2d20a] n) := by rfl
@[local simp] theorem step_2d1a6 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d20a] (n+1) ⟨s,f,0x2d1a6⟩ =
      (X86Routine.execute (.control (.cmpMemory 2 ⟨some 0,none,0,140⟩)) ⟨s,f,0x2d1ac⟩).bind (X86Routine.run listed [0x2d20a] n) := by rfl
@[local simp] theorem step_2d1ac (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d20a] (n+1) ⟨s,f,0x2d1ac⟩ =
      (X86Routine.execute (.control (.jumpZero true 28)) ⟨s,f,0x2d1ae⟩).bind (X86Routine.run listed [0x2d20a] n) := by rfl
@[local simp] theorem step_2d1ca (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d20a] (n+1) ⟨s,f,0x2d1ca⟩ =
      (X86Routine.execute (.control (.cmpMemory 2 ⟨some 0,none,0,152⟩)) ⟨s,f,0x2d1d0⟩).bind (X86Routine.run listed [0x2d20a] n) := by rfl
@[local simp] theorem step_2d1d0 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d20a] (n+1) ⟨s,f,0x2d1d0⟩ =
      (X86Routine.execute (.control (.jumpZero true 28)) ⟨s,f,0x2d1d2⟩).bind (X86Routine.run listed [0x2d20a] n) := by rfl
@[local simp] theorem step_2d1ee (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d20a] (n+1) ⟨s,f,0x2d1ee⟩ =
      (X86Routine.execute (.control (.cmpMemory 2 ⟨some 0,none,0,132⟩)) ⟨s,f,0x2d1f4⟩).bind (X86Routine.run listed [0x2d20a] n) := by rfl
@[local simp] theorem step_2d1f4 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d20a] (n+1) ⟨s,f,0x2d1f4⟩ =
      (X86Routine.execute (.control (.jumpZero true 20)) ⟨s,f,0x2d1f6⟩).bind (X86Routine.run listed [0x2d20a] n) := by rfl
@[local simp] theorem stop_2d20a (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d20a] n ⟨s,f,0x2d20a⟩=some ⟨s,f,0x2d20a⟩ := by cases n <;> rfl
@[local simp] theorem step_2d20a (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d286] (n+1) ⟨s,f,0x2d20a⟩ =
      (X86Routine.execute (.control (.cmpMemory 2 ⟨some 0,none,0,128⟩)) ⟨s,f,0x2d210⟩).bind (X86Routine.run listed [0x2d286] n) := by rfl
@[local simp] theorem step_2d210 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d286] (n+1) ⟨s,f,0x2d210⟩ =
      (X86Routine.execute (.control (.jumpZero true 16)) ⟨s,f,0x2d212⟩).bind (X86Routine.run listed [0x2d286] n) := by rfl
@[local simp] theorem step_2d212 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d286] (n+1) ⟨s,f,0x2d212⟩ =
      (X86Routine.execute (.control (.cmpMemory 2 ⟨some 0,none,0,160⟩)) ⟨s,f,0x2d218⟩).bind (X86Routine.run listed [0x2d286] n) := by rfl
@[local simp] theorem step_2d218 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d286] (n+1) ⟨s,f,0x2d218⟩ =
      (X86Routine.execute (.control (.jumpZero true 8)) ⟨s,f,0x2d21a⟩).bind (X86Routine.run listed [0x2d286] n) := by rfl
@[local simp] theorem step_2d21a (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d286] (n+1) ⟨s,f,0x2d21a⟩ =
      (X86Routine.execute (.control (.block (.store ⟨some 0,none,0,116⟩ 3))) ⟨s,f,0x2d21d⟩).bind (X86Routine.run listed [0x2d286] n) := by rfl
@[local simp] theorem step_2d21d (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d286] (n+1) ⟨s,f,0x2d21d⟩ =
      (X86Routine.execute (.jump 103) ⟨s,f,0x2d21f⟩).bind (X86Routine.run listed [0x2d286] n) := by rfl
@[local simp] theorem step_2d222 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d286] (n+1) ⟨s,f,0x2d222⟩ =
      (X86Routine.execute (.control (.block (.load 1 ⟨some 0,none,0,156⟩))) ⟨s,f,0x2d228⟩).bind (X86Routine.run listed [0x2d286] n) := by rfl
@[local simp] theorem step_2d228 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d286] (n+1) ⟨s,f,0x2d228⟩ =
      (X86Routine.execute (.compareRegisters 2 1) ⟨s,f,0x2d22a⟩).bind (X86Routine.run listed [0x2d286] n) := by rfl
@[local simp] theorem step_2d22a (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d286] (n+1) ⟨s,f,0x2d22a⟩ =
      (X86Routine.execute (.control (.jumpZero true 9)) ⟨s,f,0x2d22c⟩).bind (X86Routine.run listed [0x2d286] n) := by rfl
@[local simp] theorem step_2d22c (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d286] (n+1) ⟨s,f,0x2d22c⟩ =
      (X86Routine.execute (.storeImmediate ⟨some 0,none,0,116⟩ 1) ⟨s,f,0x2d233⟩).bind (X86Routine.run listed [0x2d286] n) := by rfl
@[local simp] theorem step_2d233 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d286] (n+1) ⟨s,f,0x2d233⟩ =
      (X86Routine.execute (.jump 81) ⟨s,f,0x2d235⟩).bind (X86Routine.run listed [0x2d286] n) := by rfl
@[local simp] theorem step_2d235 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d286] (n+1) ⟨s,f,0x2d235⟩ =
      (X86Routine.execute (.control (.block (.load 6 ⟨some 0,none,0,148⟩))) ⟨s,f,0x2d23b⟩).bind (X86Routine.run listed [0x2d286] n) := by rfl
@[local simp] theorem step_2d23b (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d286] (n+1) ⟨s,f,0x2d23b⟩ =
      (X86Routine.execute (.compareRegisters 1 6) ⟨s,f,0x2d23d⟩).bind (X86Routine.run listed [0x2d286] n) := by rfl
@[local simp] theorem step_2d23d (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d286] (n+1) ⟨s,f,0x2d23d⟩ =
      (X86Routine.execute (.control (.jumpZero true 9)) ⟨s,f,0x2d23f⟩).bind (X86Routine.run listed [0x2d286] n) := by rfl
@[local simp] theorem step_2d248 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d286] (n+1) ⟨s,f,0x2d248⟩ =
      (X86Routine.execute (.control (.cmpMemory 6 ⟨some 0,none,0,136⟩)) ⟨s,f,0x2d24e⟩).bind (X86Routine.run listed [0x2d286] n) := by rfl
@[local simp] theorem step_2d24e (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d286] (n+1) ⟨s,f,0x2d24e⟩ =
      (X86Routine.execute (.control (.jumpZero true 17)) ⟨s,f,0x2d250⟩).bind (X86Routine.run listed [0x2d286] n) := by rfl
@[local simp] theorem step_2d261 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d286] (n+1) ⟨s,f,0x2d261⟩ =
      (X86Routine.execute (.control (.cmpMemory 2 ⟨some 0,none,0,144⟩)) ⟨s,f,0x2d267⟩).bind (X86Routine.run listed [0x2d286] n) := by rfl
@[local simp] theorem step_2d267 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d286] (n+1) ⟨s,f,0x2d267⟩ =
      (X86Routine.execute (.control (.jumpZero true 26)) ⟨s,f,0x2d269⟩).bind (X86Routine.run listed [0x2d286] n) := by rfl
@[local simp] theorem step_2d283 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d286] (n+1) ⟨s,f,0x2d283⟩ =
      (X86Routine.execute (.control (.block (.store ⟨some 0,none,0,116⟩ 2))) ⟨s,f,0x2d286⟩).bind (X86Routine.run listed [0x2d286] n) := by rfl
@[local simp] theorem stop_2d286 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d286] n ⟨s,f,0x2d286⟩=some ⟨s,f,0x2d286⟩ := by cases n <;> rfl
@[local simp] theorem step_2d286 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d290] (n+1) ⟨s,f,0x2d286⟩ =
      (X86Routine.execute (.control (.cmpImmediate ⟨some 0,none,0,116⟩ 10)) ⟨s,f,0x2d28a⟩).bind (X86Routine.run listed [0x2d290] n) := by rfl
@[local simp] theorem step_2d28a (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d290] (n+1) ⟨s,f,0x2d28a⟩ =
      (X86Routine.execute (.control (.jumpZero true (-234))) ⟨s,f,0x2d290⟩).bind (X86Routine.run listed [0x2d290] n) := by rfl
@[local simp] theorem stop_2d290 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2d290] n ⟨s,f,0x2d290⟩=some ⟨s,f,0x2d290⟩ := by cases n <;> rfl

def field (s : X86Memory.State) (off : Word) := load32 s.memory (s.regs 0+off)
structure Inventory (s : X86Memory.State) : Prop where
  plasma : field s (140#32)=(0#32)
  superShotgun : field s (152#32)=(0#32)
  chaingun : field s (132#32)=(0#32)
  chainsaw : field s (148#32)=(0#32)
  rocket : field s (136#32)=(0#32)
  bfg : field s (144#32)=(0#32)

def prepared (s : X86Memory.State) := put (put s 2 0) 3 2

theorem prepare_execution (s : X86Memory.State) (f : Option Flags) (h : Inventory s) :
    X86Routine.run program [0x2d20a] 8 ⟨s,f,0x2d19f⟩=some ⟨prepared s,some (compare32 0 0),0x2d20a⟩ := by
  have hp := h.plasma; have hs := h.superShotgun; have hc := h.chaingun
  simp only [field] at hp hs hc
  have run : X86Routine.run listed [0x2d20a] 8 ⟨s,f,0x2d19f⟩=some ⟨prepared s,some (compare32 0 0),0x2d20a⟩ := by
    simp [X86Routine.execute,X86Control.execute,X86Block.Address.eval,prepared,put,write,cmp32_zero,hp,hs,hc]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

def owned (s : X86Memory.State) := field s (128#32)
def shells (s : X86Memory.State) := field s (160#32)
def bullets (s : X86Memory.State) := field s (156#32)
abbrev hasShotgun (s : X86Memory.State) : Prop := owned s≠(0#32) ∧ shells s≠(0#32)
def selected (s : X86Memory.State) : Word := if hasShotgun s then 2 else if bullets s≠(0#32) then 1 else 0
def storePending (s : X86Memory.State) (w : Word) : X86Memory.State :=
  {s with memory := store32 s.memory (s.regs 0+(116#32)) w}
def chosen (s : X86Memory.State) : X86Control.State :=
  if hasShotgun s then ⟨storePending s 2,some (compare32 0 (shells s)),0x2d286⟩
  else if bullets s≠(0#32) then ⟨storePending (put s 1 (bullets s)) 1,some (compare32 0 (bullets s)),0x2d286⟩
  else ⟨storePending (put (put s 1 0) 6 0) 0,some (compare32 0 0),0x2d286⟩

private theorem zero_left (v : Word) : (0#32)=v ↔ v=(0#32) := eq_comm

theorem choose_execution (s : X86Memory.State) (f : Option Flags) (h : Inventory s)
    (dx : s.regs 2=(0#32)) (bx : s.regs 3=(2#32)) :
    X86Routine.run program [0x2d286] 16 ⟨s,f,0x2d20a⟩=some (chosen s) := by
  have hc := h.chainsaw; have hr := h.rocket; have hb := h.bfg
  simp only [field] at hc hr hb
  have run : X86Routine.run listed [0x2d286] 16 ⟨s,f,0x2d20a⟩=some (chosen s) := by
    by_cases own : owned s=(0#32) <;> by_cases sh : shells s=(0#32) <;> by_cases bu : bullets s=(0#32) <;>
      simp only [owned,shells,bullets,field] at own sh bu <;>
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,
        chosen,hasShotgun,owned,shells,bullets,field,storePending,put,write,blockPreservesFlags,cmp32_zero,
        dx,bx,hc,hr,hb,own,sh,bu,zero_left]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

theorem prepared_inventory (s : X86Memory.State) (h : Inventory s) : Inventory (prepared s) := by
  exact ⟨h.plasma,h.superShotgun,h.chaingun,h.chainsaw,h.rocket,h.bfg⟩

theorem chosen_pending (s : X86Memory.State) :
    load32 (chosen s).core.memory ((chosen s).core.regs 0+(116#32))=selected s := by
  by_cases own : owned s=(0#32) <;> by_cases sh : shells s=(0#32) <;> by_cases bu : bullets s=(0#32) <;>
    simp [chosen,selected,hasShotgun,own,sh,bu,storePending,put,write,load_store]

theorem selected_not_sentinel (s : X86Memory.State) : selected s≠(10#32) := by
  unfold selected; split <;> try decide
  split <;> decide

def weapon (s : X86Memory.State) := field s (112#32)
def downState (s : X86Memory.State) := load32 s.memory ((((weapon s <<< 2)-weapon s) <<< 3)+(0x12d98#32))
def lowered (s : X86Memory.State) : X86Control.State :=
  ⟨X86Routine.pushWord (put (put s 2 0) 3 (downState s)) 0x2d2aa,some (logical32 0),0x2d040⟩
theorem call_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x2d040] 6 ⟨s,f,0x2d290⟩=some (lowered s) := by
  have run : X86Routine.run listed [0x2d040] 6 ⟨s,f,0x2d290⟩=some (lowered s) := by
    simp [X86Routine.run,listed,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      X86.execute,X86Block.Address.eval,put,write,lowered,downState,weapon,field,
      X86Routine.pushWord,blockPreservesFlags,logical32,BitVec.sub_eq_add_neg]
    funext r
    by_cases h2 : r=2 <;> by_cases h3 : r=3 <;> by_cases h4 : r=4 <;> simp_all [write]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

theorem retry_execution (s : X86Memory.State) (f : Option Flags)
    (pending : field s (116#32)≠(10#32)) :
    X86Routine.run program [0x2d290] 2 ⟨s,f,0x2d286⟩=some ⟨s,some (compare32 (field s 116) 10),0x2d290⟩ := by
  have run : X86Routine.run listed [0x2d290] 2 ⟨s,f,0x2d286⟩=some ⟨s,some (compare32 (field s 116) 10),0x2d290⟩ := by
    simp only [field] at pending
    simp [X86Routine.execute,X86Control.execute,X86Block.Address.eval,field,cmp32_zero,pending]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

private theorem prefix_trans {p stops n m s t u}
    (a : X86Routine.Prefix p stops n s t) (b : X86Routine.Prefix p stops m t u) :
    X86Routine.Prefix p stops (n+m) s u := by
  induction a with
  | nil => simpa using b
  | @step n s middle last op len active decoded executed rest ih =>
    simpa only [Nat.succ_add] using X86Routine.Prefix.step active decoded executed (ih b)

def result (s : X86Memory.State) := lowered (chosen (prepared s)).core

theorem execution (s : X86Memory.State) (f : Option Flags) (h : Inventory s) :
    ∃ n, n≤32 ∧ X86Routine.Prefix program [] n ⟨s,f,0x2d19f⟩ (result s) := by
  obtain ⟨n,hn,a,_⟩ := X86Routine.run_path (prepare_execution s f h)
  obtain ⟨m,hm,b,_⟩ := X86Routine.run_path (choose_execution (prepared s) (some (compare32 0 0)) (prepared_inventory s h) (by simp [prepared,put,write]) (by simp [prepared,put,write]))
  have pending : field (chosen (prepared s)).core (116#32)≠(10#32) := by
    rw [field,chosen_pending]; exact selected_not_sentinel _
  obtain ⟨k,hk,c,_⟩ := X86Routine.run_path (retry_execution (chosen (prepared s)).core (chosen (prepared s)).flags pending)
  have eq : chosen (prepared s)=⟨(chosen (prepared s)).core,(chosen (prepared s)).flags,0x2d286⟩ := by
    unfold chosen; split <;> try rfl
    split <;> rfl
  rw [←eq] at c
  obtain ⟨j,hj,d,_⟩ := X86Routine.run_path (call_execution (chosen (prepared s)).core (some (compare32 (field (chosen (prepared s)).core 116) 10)))
  exact ⟨n+m+k+j,by omega,prefix_trans (prefix_trans (prefix_trans
    (a.transfer program [] (by intros; rfl) (by simp))
    (b.transfer program [] (by intros; rfl) (by simp)))
    (c.transfer program [] (by intros; rfl) (by simp)))
    (d.transfer program [] (by intros; rfl) (by simp))⟩

/-- Actual false return after the lowering setter returns; no setter is stubbed. -/
def returned (s : X86Memory.State) : X86Control.State :=
  let t := PspriteLoop.popped (PspriteLoop.popped (PspriteLoop.popped (PspriteLoop.popped (put s 0 0) 6) 2) 1) 3
  ⟨put t 4 (t.regs 4+4),some (logical32 0),(load32 t.memory (t.regs 4)).toNat⟩
theorem return_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 6 ⟨s,f,0x2d2aa⟩ (returned s) := by
  let a := put s 0 0
  let b := PspriteLoop.popped a 6
  let c := PspriteLoop.popped b 2
  let d := PspriteLoop.popped c 1
  let e := PspriteLoop.popped d 3
  have p : X86Routine.Prefix listed [] 6 ⟨s,f,0x2d2aa⟩ (returned s) := by
    apply X86Routine.Prefix.step (middle := ⟨a,some (logical32 0),0x2d2ac⟩) (by simp) (by rfl) (by simp [X86Routine.execute,put,write,a,logical32])
    apply X86Routine.Prefix.step (middle := ⟨b,some (logical32 0),0x2d2ad⟩) (by simp) (by rfl) rfl
    apply X86Routine.Prefix.step (middle := ⟨c,some (logical32 0),0x2d2ae⟩) (by simp) (by rfl) rfl
    apply X86Routine.Prefix.step (middle := ⟨d,some (logical32 0),0x2d2af⟩) (by simp) (by rfl) rfl
    apply X86Routine.Prefix.step (middle := ⟨e,some (logical32 0),0x2d2b0⟩) (by simp) (by rfl) rfl
    apply X86Routine.Prefix.step (middle := returned s) (by simp) (by rfl) rfl
    exact X86Routine.Prefix.nil _
  exact p.transfer program [] decoded (by simp)

structure Inputs (s : X86Memory.State) (ownedShotgun : Bool) (sh bu : Int32) : Prop where
  ownedValue : (owned s≠(0#32)) ↔ ownedShotgun=true
  shellsValue : shells s=sh.toBitVec
  bulletsValue : bullets s=bu.toBitVec
  shellsNonnegative : 0≤sh.toInt
  bulletsNonnegative : 0≤bu.toInt

theorem live_choice (s : X86Memory.State) (own : Bool) (sh bu : Int32) (h : Inputs s own sh bu) :
    selected s=BitVec.ofNat 32 (Weapon.fallbackWeapon own sh bu).val := by
  have shell : shells s≠(0#32) ↔ 0<sh.toInt := by
    rw [h.shellsValue]
    have zero : sh.toBitVec=(0#32) ↔ sh.toInt=0 := by
      simp [←BitVec.toInt_inj,Int32.toInt_toBitVec]
    simp only [ne_eq,zero]
    have hs := h.shellsNonnegative
    have hb := h.bulletsNonnegative
    omega
  have bullet : bullets s≠(0#32) ↔ 0<bu.toInt := by
    rw [h.bulletsValue]
    have zero : bu.toBitVec=(0#32) ↔ bu.toInt=0 := by
      simp [←BitVec.toInt_inj,Int32.toInt_toBitVec]
    simp only [ne_eq,zero]
    have hs := h.shellsNonnegative
    have hb := h.bulletsNonnegative
    omega
  simp [selected,hasShotgun,h.ownedValue,shell,bullet,Weapon.fallbackWeapon,Int32.lt_iff_toInt_lt]
  split <;> try rfl
  split <;> rfl


/-- The actual CALL's return-address write preserves the selected pending
weapon when the caller supplies the required stack/player separation. -/
theorem lowered_pending (s : X86Memory.State)
    (safe : Apart (s.regs 0+(116#32)) (s.regs 4-(4#32))) :
    field (lowered s).core (116#32)=field s (116#32) := by
  simp [lowered,field,X86Routine.pushWord,put,write,load_store_apart _ _ _ _ safe]

theorem result_pending (s : X86Memory.State)
    (safe : Apart ((chosen (prepared s)).core.regs 0+(116#32)) ((chosen (prepared s)).core.regs 4-(4#32))) :
    field (result s).core (116#32)=selected s := by
  rw [result,lowered_pending _ safe,field,chosen_pending]
  rfl

theorem call_live (s : X86Memory.State) (w : Fin 3)
    (hw : weapon s=BitVec.ofNat 32 w.val)
    (table : load32 s.memory (0x12d98+24*BitVec.ofNat 32 w.val)=BitVec.ofNat 32 (Weapon.down w.val)) :
    (lowered s).core.regs 0=s.regs 0 ∧ (lowered s).core.regs 2=0 ∧
    (lowered s).core.regs 3=BitVec.ofNat 32 (Weapon.down w.val) ∧
    load32 (lowered s).core.memory ((lowered s).core.regs 4)=0x2d2aa := by
  have cases : w.val=0 ∨ w.val=1 ∨ w.val=2 := by omega
  rcases cases with h | h | h <;>
    simp [h] at hw table ⊢ <;>
    simpa [lowered,downState,hw,put,write,X86Routine.pushWord,load_store] using table
end Doom.Proofs.WeaponFallback
