import Doom.Proofs.OriginalPainSetter

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.DamageReturn
open Verification X86 X86Memory X86Control BlockSummary

def code : List UInt8 := [0x8b,0xae,0x80,0x0,0x0,0x0,0xc7,0x46,0x7c,0x0,0x0,0x0,0x0,0x85,0xed,0x74,0x6,0x83,0x7e,0x58,0x3,0x75,0x51,0x8b,0x54,0x24,0x4,0x85,0xd2,0x74,0x49,0x39,0xd6,0x74,0x45,0x83,0x7a,0x58,0x3,0x74,0x3f,0x89,0x56,0x78,0x8b,0x56,0x5c,0xc7,0x86,0x80,0x0,0x0,0x0,0x64,0x0,0x0,0x0,0x8b,0x5a,0x4,0x8d,0x4,0xdd,0x0,0x0,0x0,0x0,0x29,0xd8,0x8d,0x4,0x85,0x0,0x0,0x0,0x0,0x8b,0x7e,0x64,0x5,0x28,0x5a,0x1,0x0,0x39,0xf8,0x75,0x10,0x8b,0x6a,0xc,0x85,0xed,0x74,0x9,0x89,0xea,0x89,0xf0,0xe8,0x59,0x67,0x0,0x0,0x83,0xc4,0xc,0x5d,0x5f,0x5e,0xc3]
def bytesProgram (bytes : List UInt8) (pc : Nat) : Option (X86Routine.Op × Nat) :=
  if 0x2a6df ≤ pc ∧ pc < 0x2a74e then X86Routine.decodeAt bytes (pc-0x2a6df) else none
def program := bytesProgram code

def listed : X86Routine.Program
  | 0x2a6df => some (.control (.block (.load 5 ⟨some 6,none,0,128⟩)),6)
  | 0x2a6e5 => some (.storeImmediate ⟨some 6,none,0,124⟩ 0,7)
  | 0x2a6ec => some (.control (.testWord 5 5),2)
  | 0x2a6ee => some (.control (.jumpZero true 6),2)
  | 0x2a6f0 => some (.control (.cmpImmediate ⟨some 6,none,0,88⟩ 3),4)
  | 0x2a6f4 => some (.control (.jumpZero false 81),2)
  | 0x2a6f6 => some (.control (.block (.load 2 ⟨some 4,none,0,4⟩)),4)
  | 0x2a6fa => some (.control (.testWord 2 2),2)
  | 0x2a6fc => some (.control (.jumpZero true 73),2)
  | 0x2a747 => some (.addImmediate 4 12,3)
  | 0x2a74a => some (.pop 5,1)
  | 0x2a74b => some (.pop 7,1)
  | 0x2a74c => some (.pop 6,1)
  | 0x2a74d => some (.ret,1)
  | _ => none

theorem decoded (pc : Nat) (h : listed pc ≠ none) : program pc = listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def reaction (s : X86Memory.State) := s.regs 6+(124#32)
def threshold (s : X86Memory.State) := load32 s.memory (s.regs 6+(128#32))
def resetMemory (s : X86Memory.State) := store32 s.memory (reaction s) 0
structure Inputs (s : X86Memory.State) : Prop where
  playerKind : load32 s.memory (s.regs 6+(88#32)) = 0
  source : load32 s.memory (s.regs 4+(4#32)) = 0
  sourceSafe : Apart (s.regs 4+(4#32)) (reaction s)

def beforePops (s : X86Memory.State) : X86Control.State :=
  ⟨⟨write (write (write s.regs 5 (threshold s)) 2
    (if threshold s=0 then 0 else s.regs 2)) 4 (s.regs 4+(12#32)),resetMemory s⟩,none,0x2a74a⟩
@[simp] theorem step_0x2a6df (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2a74a] (n+1) ⟨s,f,0x2a6df⟩ =
      (X86Routine.execute (.control (.block (.load 5 ⟨some 6,none,0,128⟩))) ⟨s,f,0x2a6e5⟩).bind (X86Routine.run listed [0x2a74a] n) := by rfl
@[simp] theorem step_0x2a6e5 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2a74a] (n+1) ⟨s,f,0x2a6e5⟩ =
      (X86Routine.execute (.storeImmediate ⟨some 6,none,0,124⟩ 0) ⟨s,f,0x2a6ec⟩).bind (X86Routine.run listed [0x2a74a] n) := by rfl
@[simp] theorem step_0x2a6ec (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2a74a] (n+1) ⟨s,f,0x2a6ec⟩ =
      (X86Routine.execute (.control (.testWord 5 5)) ⟨s,f,0x2a6ee⟩).bind (X86Routine.run listed [0x2a74a] n) := by rfl
@[simp] theorem step_0x2a6ee (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2a74a] (n+1) ⟨s,f,0x2a6ee⟩ =
      (X86Routine.execute (.control (.jumpZero true 6)) ⟨s,f,0x2a6f0⟩).bind (X86Routine.run listed [0x2a74a] n) := by rfl
@[simp] theorem step_0x2a6f0 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2a74a] (n+1) ⟨s,f,0x2a6f0⟩ =
      (X86Routine.execute (.control (.cmpImmediate ⟨some 6,none,0,88⟩ 3)) ⟨s,f,0x2a6f4⟩).bind (X86Routine.run listed [0x2a74a] n) := by rfl
@[simp] theorem step_0x2a6f4 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2a74a] (n+1) ⟨s,f,0x2a6f4⟩ =
      (X86Routine.execute (.control (.jumpZero false 81)) ⟨s,f,0x2a6f6⟩).bind (X86Routine.run listed [0x2a74a] n) := by rfl
@[simp] theorem step_0x2a6f6 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2a74a] (n+1) ⟨s,f,0x2a6f6⟩ =
      (X86Routine.execute (.control (.block (.load 2 ⟨some 4,none,0,4⟩))) ⟨s,f,0x2a6fa⟩).bind (X86Routine.run listed [0x2a74a] n) := by rfl
@[simp] theorem step_0x2a6fa (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2a74a] (n+1) ⟨s,f,0x2a6fa⟩ =
      (X86Routine.execute (.control (.testWord 2 2)) ⟨s,f,0x2a6fc⟩).bind (X86Routine.run listed [0x2a74a] n) := by rfl
@[simp] theorem step_0x2a6fc (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2a74a] (n+1) ⟨s,f,0x2a6fc⟩ =
      (X86Routine.execute (.control (.jumpZero true 73)) ⟨s,f,0x2a6fe⟩).bind (X86Routine.run listed [0x2a74a] n) := by rfl
@[simp] theorem step_0x2a747 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2a74a] (n+1) ⟨s,f,0x2a747⟩ =
      (X86Routine.execute (.addImmediate 4 12) ⟨s,f,0x2a74a⟩).bind (X86Routine.run listed [0x2a74a] n) := by rfl

theorem reset_execution (s : X86Memory.State) (f : Option Flags) (h : Inputs s) :
    X86Routine.run listed [0x2a74a] 10 ⟨s,f,0x2a6df⟩ = some (beforePops s) := by
  have kind : load32 (resetMemory s) (s.regs 6+(88#32)) = 0 := by
    rw [resetMemory,load_store_apart]; exact h.playerKind
    exact PlayerHealth.offsets_apart _ 88 124 (by decide)
  have source : load32 (resetMemory s) (s.regs 4+(4#32)) = 0 := by
    rw [resetMemory,load_store_apart _ _ _ _ h.sourceSafe,h.source]
  by_cases zero : threshold s=0 <;>
    simp [beforePops,threshold,resetMemory,reaction] at zero kind source ⊢ <;>
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      X86Block.Address.eval,put,write,blockPreservesFlags,logical32,compare32,
      kind,source,zero] <;>
    simp [X86Routine.run,listed]
  funext r
  simp [write]; split <;> simp_all

def restored (s : X86Memory.State) (f : Option Flags) : X86Control.State :=
  ⟨⟨write (write (write (write s.regs 5 (load32 s.memory (s.regs 4)))
    7 (load32 s.memory (s.regs 4+(4#32))))
    6 (load32 s.memory (s.regs 4+(8#32)))) 4 (s.regs 4+(16#32)),s.memory⟩,
    f,(load32 s.memory (s.regs 4+(12#32))).toNat⟩

theorem epilogue (s : X86Memory.State) (f : Option Flags)
    (outside : 0x2a74e ≤ (load32 s.memory (s.regs 4+(12#32))).toNat) :
    X86Routine.run listed [(load32 s.memory (s.regs 4+(12#32))).toNat] 4
      ⟨s,f,0x2a74a⟩ = some (restored s f) := by
  have n0 : 0x2a74a ≠ (load32 s.memory (s.regs 4+(12#32))).toNat := by omega
  have n1 : 0x2a74b ≠ (load32 s.memory (s.regs 4+(12#32))).toNat := by omega
  have n2 : 0x2a74c ≠ (load32 s.memory (s.regs 4+(12#32))).toNat := by omega
  have n3 : 0x2a74d ≠ (load32 s.memory (s.regs 4+(12#32))).toNat := by omega
  simp [X86Routine.run,listed,X86Routine.execute,put,write,restored,
    n0,n1,n2,n3,BitVec.add_assoc]
  funext r
  by_cases h4 : r=4 <;> by_cases h5 : r=5 <;> by_cases h6 : r=6 <;> by_cases h7 : r=7 <;> simp_all [write]

def result (s : X86Memory.State) := restored (beforePops s).core none

theorem listed_active (pc stop : Nat) (h : listed pc ≠ none) (outside : 0x2a74e ≤ stop) : pc ∉ [stop] := by
  fun_cases listed pc <;> simp_all [listed] <;> omega

theorem execution (s : X86Memory.State) (f : Option Flags) (h : Inputs s)
    (outside : 0x2a74e ≤ (result s).pc) :
    X86Routine.run listed [(result s).pc] 14 ⟨s,f,0x2a6df⟩ = some (result s) := by
  obtain ⟨n,hn,path,_⟩ := X86Routine.run_path (reset_execution s f h)
  have path := path.transfer listed [(result s).pc] (fun _ _ => rfl)
    (fun pc h => listed_active pc _ h outside)
  have tail := epilogue (beforePops s).core none outside
  exact path.finish tail 14 (by omega)

theorem original_execution (s : X86Memory.State) (f : Option Flags) (h : Inputs s)
    (outside : 0x2a74e ≤ (result s).pc) :
    X86Routine.run program [(result s).pc] 14 ⟨s,f,0x2a6df⟩ = some (result s) := by
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [execution s f h outside]; simp)]
  exact execution s f h outside

theorem memory_frame (s : X86Memory.State) :
    PlayerHeight.Frame s.memory (result s).core.memory [reaction s] := by
  intro a safe
  exact load_store_apart _ _ _ _ (safe _ (by simp))

theorem reaction_zero (s : X86Memory.State) :
    load32 (result s).core.memory (reaction s) = 0 := load_store _ _ _

theorem stack_apart (sp : Word) (a b : Fin 8) (h : a ≠ b) :
    Apart (sp-BitVec.ofNat 32 (4*a.val)) (sp-BitVec.ofNat 32 (4*b.val)) := by
  intro i j eq
  have aa := a.isLt; have bb := b.isLt; have ii := i.isLt; have jj := j.isLt
  have h' : a.val ≠ b.val := fun e => h (Fin.ext e)
  rw [BitVec.sub_eq_add_neg,BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.add_assoc] at eq
  have eq := (BitVec.add_right_inj sp).mp eq
  have eq' := congrArg BitVec.toNat eq
  simp only [BitVec.toNat_add,BitVec.toNat_neg,BitVec.toNat_ofNat] at eq'
  omega

theorem saved_slots (s : X86Memory.State) (pc : Nat) :
    load32 (PlayerDamageEntry.saved s pc) (s.regs 4-(4#32)) = BitVec.ofNat 32 (pc+5) ∧
    load32 (PlayerDamageEntry.saved s pc) (s.regs 4-(8#32)) = s.regs 6 ∧
    load32 (PlayerDamageEntry.saved s pc) (s.regs 4-(12#32)) = s.regs 7 ∧
    load32 (PlayerDamageEntry.saved s pc) (s.regs 4-(16#32)) = s.regs 5 ∧
    load32 (PlayerDamageEntry.saved s pc) (s.regs 4-(24#32)) = s.regs 3 := by
  have k12 (m : Memory) (v : Word) :
      load32 (store32 m (s.regs 4-(8#32)) v) (s.regs 4-(4#32)) = load32 m (s.regs 4-(4#32)) :=
    load_store_apart _ _ _ _ (stack_apart (s.regs 4) 1 2 (by decide))
  have k13 (m : Memory) (v : Word) :
      load32 (store32 m (s.regs 4-(12#32)) v) (s.regs 4-(4#32)) = load32 m (s.regs 4-(4#32)) :=
    load_store_apart _ _ _ _ (stack_apart (s.regs 4) 1 3 (by decide))
  have k14 (m : Memory) (v : Word) :
      load32 (store32 m (s.regs 4-(16#32)) v) (s.regs 4-(4#32)) = load32 m (s.regs 4-(4#32)) :=
    load_store_apart _ _ _ _ (stack_apart (s.regs 4) 1 4 (by decide))
  have k17 (m : Memory) (v : Word) :
      load32 (store32 m (s.regs 4-(28#32)) v) (s.regs 4-(4#32)) = load32 m (s.regs 4-(4#32)) :=
    load_store_apart _ _ _ _ (stack_apart (s.regs 4) 1 7 (by decide))
  have k16 (m : Memory) (v : Word) :
      load32 (store32 m (s.regs 4-(24#32)) v) (s.regs 4-(4#32)) = load32 m (s.regs 4-(4#32)) :=
    load_store_apart _ _ _ _ (stack_apart (s.regs 4) 1 6 (by decide))
  have k21 (m : Memory) (v : Word) :
      load32 (store32 m (s.regs 4-(4#32)) v) (s.regs 4-(8#32)) = load32 m (s.regs 4-(8#32)) :=
    load_store_apart _ _ _ _ (stack_apart (s.regs 4) 2 1 (by decide))
  have k23 (m : Memory) (v : Word) :
      load32 (store32 m (s.regs 4-(12#32)) v) (s.regs 4-(8#32)) = load32 m (s.regs 4-(8#32)) :=
    load_store_apart _ _ _ _ (stack_apart (s.regs 4) 2 3 (by decide))
  have k24 (m : Memory) (v : Word) :
      load32 (store32 m (s.regs 4-(16#32)) v) (s.regs 4-(8#32)) = load32 m (s.regs 4-(8#32)) :=
    load_store_apart _ _ _ _ (stack_apart (s.regs 4) 2 4 (by decide))
  have k27 (m : Memory) (v : Word) :
      load32 (store32 m (s.regs 4-(28#32)) v) (s.regs 4-(8#32)) = load32 m (s.regs 4-(8#32)) :=
    load_store_apart _ _ _ _ (stack_apart (s.regs 4) 2 7 (by decide))
  have k26 (m : Memory) (v : Word) :
      load32 (store32 m (s.regs 4-(24#32)) v) (s.regs 4-(8#32)) = load32 m (s.regs 4-(8#32)) :=
    load_store_apart _ _ _ _ (stack_apart (s.regs 4) 2 6 (by decide))
  have k31 (m : Memory) (v : Word) :
      load32 (store32 m (s.regs 4-(4#32)) v) (s.regs 4-(12#32)) = load32 m (s.regs 4-(12#32)) :=
    load_store_apart _ _ _ _ (stack_apart (s.regs 4) 3 1 (by decide))
  have k32 (m : Memory) (v : Word) :
      load32 (store32 m (s.regs 4-(8#32)) v) (s.regs 4-(12#32)) = load32 m (s.regs 4-(12#32)) :=
    load_store_apart _ _ _ _ (stack_apart (s.regs 4) 3 2 (by decide))
  have k34 (m : Memory) (v : Word) :
      load32 (store32 m (s.regs 4-(16#32)) v) (s.regs 4-(12#32)) = load32 m (s.regs 4-(12#32)) :=
    load_store_apart _ _ _ _ (stack_apart (s.regs 4) 3 4 (by decide))
  have k37 (m : Memory) (v : Word) :
      load32 (store32 m (s.regs 4-(28#32)) v) (s.regs 4-(12#32)) = load32 m (s.regs 4-(12#32)) :=
    load_store_apart _ _ _ _ (stack_apart (s.regs 4) 3 7 (by decide))
  have k36 (m : Memory) (v : Word) :
      load32 (store32 m (s.regs 4-(24#32)) v) (s.regs 4-(12#32)) = load32 m (s.regs 4-(12#32)) :=
    load_store_apart _ _ _ _ (stack_apart (s.regs 4) 3 6 (by decide))
  have k41 (m : Memory) (v : Word) :
      load32 (store32 m (s.regs 4-(4#32)) v) (s.regs 4-(16#32)) = load32 m (s.regs 4-(16#32)) :=
    load_store_apart _ _ _ _ (stack_apart (s.regs 4) 4 1 (by decide))
  have k42 (m : Memory) (v : Word) :
      load32 (store32 m (s.regs 4-(8#32)) v) (s.regs 4-(16#32)) = load32 m (s.regs 4-(16#32)) :=
    load_store_apart _ _ _ _ (stack_apart (s.regs 4) 4 2 (by decide))
  have k43 (m : Memory) (v : Word) :
      load32 (store32 m (s.regs 4-(12#32)) v) (s.regs 4-(16#32)) = load32 m (s.regs 4-(16#32)) :=
    load_store_apart _ _ _ _ (stack_apart (s.regs 4) 4 3 (by decide))
  have k47 (m : Memory) (v : Word) :
      load32 (store32 m (s.regs 4-(28#32)) v) (s.regs 4-(16#32)) = load32 m (s.regs 4-(16#32)) :=
    load_store_apart _ _ _ _ (stack_apart (s.regs 4) 4 7 (by decide))
  have k46 (m : Memory) (v : Word) :
      load32 (store32 m (s.regs 4-(24#32)) v) (s.regs 4-(16#32)) = load32 m (s.regs 4-(16#32)) :=
    load_store_apart _ _ _ _ (stack_apart (s.regs 4) 4 6 (by decide))
  have k61 (m : Memory) (v : Word) :
      load32 (store32 m (s.regs 4-(4#32)) v) (s.regs 4-(24#32)) = load32 m (s.regs 4-(24#32)) :=
    load_store_apart _ _ _ _ (stack_apart (s.regs 4) 6 1 (by decide))
  have k62 (m : Memory) (v : Word) :
      load32 (store32 m (s.regs 4-(8#32)) v) (s.regs 4-(24#32)) = load32 m (s.regs 4-(24#32)) :=
    load_store_apart _ _ _ _ (stack_apart (s.regs 4) 6 2 (by decide))
  have k63 (m : Memory) (v : Word) :
      load32 (store32 m (s.regs 4-(12#32)) v) (s.regs 4-(24#32)) = load32 m (s.regs 4-(24#32)) :=
    load_store_apart _ _ _ _ (stack_apart (s.regs 4) 6 3 (by decide))
  have k64 (m : Memory) (v : Word) :
      load32 (store32 m (s.regs 4-(16#32)) v) (s.regs 4-(24#32)) = load32 m (s.regs 4-(24#32)) :=
    load_store_apart _ _ _ _ (stack_apart (s.regs 4) 6 4 (by decide))
  have k67 (m : Memory) (v : Word) :
      load32 (store32 m (s.regs 4-(28#32)) v) (s.regs 4-(24#32)) = load32 m (s.regs 4-(24#32)) :=
    load_store_apart _ _ _ _ (stack_apart (s.regs 4) 6 7 (by decide))
  simp only [PlayerDamageEntry.saved,k12,k13,k14,k17,k16,k21,k23,k24,k27,k26,k31,k32,k34,k37,k36,k41,k42,k43,k47,k46,k61,k62,k63,k64,k67,load_store,and_self]

def joined (pc : Nat) :=
  if 0x2a6df ≤ pc ∧ pc < 0x2a74e then program pc else PainSetter.joined pc

def exits : List Nat := [0x2a6a6,0x2fb7b,0x2fba5,0x2fbd7]

theorem contains_previous (pc : Nat) (h : PainSetter.joined pc ≠ none) : joined pc = PainSetter.joined pc := by
  unfold joined
  split
  next bounds =>
    have b0 : ¬(0x2a650 ≤ pc ∧ pc < 0x2a6a6) := by omega
    have b1 : ¬(0x1bb50 ≤ pc ∧ pc < 0x1bb66) := by omega
    have b2 : ¬(0x1bc41 ≤ pc ∧ pc < 0x1bc45) := by omega
    have b3 : ¬(0x2a616 ≤ pc ∧ pc < 0x2a650) := by omega
    have b4 : ¬(0x2a460 ≤ pc ∧ pc < 0x2a5d5) := by omega
    have b5 : ¬(0x2a5d5 ≤ pc ∧ pc < 0x2a616) := by omega
    have b6 : ¬(0x2a6b6 ≤ pc ∧ pc < 0x2a6c9) := by omega
    have b7 : ¬(0x24160 ≤ pc ∧ pc < 0x2417c) := by omega
    have b8 : ¬(0x2a6c9 ≤ pc ∧ pc < 0x2a6df) := by omega
    have b9 : ¬(0x30ea0 ≤ pc ∧ pc < 0x30efb) := by omega
    simp [PainSetter.joined,PainHandoff.joined,PlayerPain.joined,ActorHealth.joined,PlayerHealth.joined,
      PlayerDamageEntry.program,PlayerDamageEntry.bytesProgram,b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,
      show pc ≠ 0x2fb76 by omega,show pc ≠ 0x2fba0 by omega,show pc ≠ 0x2fbd2 by omega] at h
  next => rfl

theorem previous_active (pc : Nat) (h : PainSetter.joined pc ≠ none) : pc ∉ exits := by
  intro hm
  simp only [exits,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl <;> contradiction

theorem contains_tail (pc : Nat) (h : program pc ≠ none) : joined pc = program pc := by
  unfold joined
  split
  next => rfl
  next hn => simp [program,bytesProgram,hn] at h

theorem tail_active (pc : Nat) (h : program pc ≠ none) : pc ∉ exits := by
  intro hm
  simp only [exits,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl <;> contradiction

def savedReads (s : X86Memory.State) :=
  [s.regs 4-(4#32),s.regs 4-(8#32),s.regs 4-(12#32),s.regs 4-(16#32),s.regs 4-(24#32)]
def retained (s : X86Memory.State) := PainSetter.retained s ++ PainSetter.fields (s.regs 0) ++
  [s.regs 0+(120#32),s.regs 0+(128#32)]

structure JoinedInputs (s : X86Memory.State) (v : PlayerDamage.State) (d : Int32) (baby : Bool) (i : UInt8)
    extends toSetter : PainSetter.JoinedInputs s v d baby i where
  playerKind : load32 s.memory (s.regs 0+(88#32)) = 0
  kindSafe : ∀ b, b ∈ PainSetter.joinedWrites s → Apart (s.regs 0+(88#32)) b
  savedSafe : ∀ a, a ∈ savedReads s → ∀ b, b ∈ PainSetter.afterWrites s → Apart a b
  reactionStackSafe : ∀ a, a ∈ savedReads s → Apart a (s.regs 0+(124#32))
  reactionRetainedSafe : ∀ a, a ∈ retained s → Apart a (s.regs 0+(124#32))

def joinedWrites (s : X86Memory.State) := PainSetter.joinedWrites s ++ [s.regs 0+(124#32)]

/-- Continuous surviving-damage execution. The earlier observation is retained
in memory; the handler returns through its original CALL-written stack word. -/
theorem joined_execution (s : X86Memory.State) (f : Option Flags) (pc : Nat)
    (site : pc ∈ PlayerDamageEntry.sites) (v : PlayerDamage.State) (d : Int32) (baby : Bool)
    (rng : DoomRandom) (h : JoinedInputs s v d baby rng.play)
    (applied : (PlayerDamage.apply v d none false baby rng).applied = true)
    (alive : (PlayerDamage.apply v d none false baby rng).killed = false) :
    ∃ g t, X86Routine.run PainSetter.joined PainSetter.exits 152 ⟨s,f,pc⟩ = some g ∧
      PainSetter.observation s g = PainSetter.liveObservation s v (PlayerDamage.apply v d none false baby rng) ∧
      X86Routine.run joined exits 166 ⟨s,f,pc⟩ = some t ∧
      t.pc = pc+5 ∧ t.core.regs 4 = s.regs 4 ∧
      t.core.regs 5 = s.regs 5 ∧ t.core.regs 6 = s.regs 6 ∧ t.core.regs 7 = s.regs 7 ∧
      load32 t.core.memory (s.regs 0+(124#32)) = 0 ∧
      (∀ a, a ∈ retained s → load32 t.core.memory a = load32 g.core.memory a) ∧
      PlayerHeight.Frame s.memory t.core.memory (joinedWrites s) := by
  obtain ⟨g,grun,gobs,gsp,gobj,gframe,gsaved⟩ :=
    PainSetter.joined_execution_detailed s f pc site v d baby rng.play h.toSetter
  rw [← PainSetter.live_answer s v d baby rng h.liveSkull h.liveOrdinary] at gobs
  obtain ⟨n,hn,path,gexit⟩ := X86Routine.run_path grun
  have gp : g.pc=0x2a6df := by
    have obs := congrArg (fun x => x.1.1.2) gobs
    simp only [PainSetter.observation,PainSetter.liveObservation,ActorHealth.observation,
      ActorHealth.liveObservation,applied,if_true,alive] at obs
    simp only [PainSetter.exits,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at gexit
    rcases gexit with eq | eq | eq <;> simp_all
  have path := path.transfer joined exits contains_previous previous_active
  have keep (a : Word) (ha : a ∈ savedReads s) := gsaved a (h.savedSafe a ha)
  have slots := saved_slots s pc
  have a4 : g.core.regs 4+(4#32) = s.regs 4-(24#32) := by
    rw [gsp]; simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  have a12 : g.core.regs 4+(12#32) = s.regs 4-(16#32) := by
    rw [gsp]; simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  have a16 : g.core.regs 4+(16#32) = s.regs 4-(12#32) := by
    rw [gsp]; simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  have a20 : g.core.regs 4+(20#32) = s.regs 4-(8#32) := by
    rw [gsp]; simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  have a24 : g.core.regs 4+(24#32) = s.regs 4-(4#32) := by
    rw [gsp]; simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  have source : load32 g.core.memory (g.core.regs 4+(4#32)) = 0 := by
    rw [a4]
    rw [keep _ (by simp [savedReads]),slots.2.2.2.2,h.source]
  have ins : Inputs g.core := by
    refine ⟨?_,source,?_⟩
    · rw [gobj,gframe _ h.kindSafe,h.playerKind]
    · simpa [reaction,gobj,gsp,BitVec.sub_eq_add_neg,BitVec.add_assoc] using
        h.reactionStackSafe (s.regs 4-(24#32)) (by simp [savedReads])
  have retread (a : Word) (ha : a ∈ savedReads s) :
      load32 (resetMemory g.core) a = load32 (PlayerDamageEntry.saved s pc) a := by
    rw [resetMemory,load_store_apart]
    · exact keep a ha
    · simpa [reaction,gobj] using h.reactionStackSafe a ha
  have retpc : (result g.core).pc = pc+5 := by
    have view : (result g.core).pc = (load32 (resetMemory g.core) (g.core.regs 4+(24#32))).toNat := by
      simp [result,restored,beforePops,write,BitVec.add_assoc]
    rw [view,a24]
    rw [retread _ (by simp [savedReads]),slots.1]
    simp only [PlayerDamageEntry.sites,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at site
    rcases site with rfl | rfl | rfl <;> decide
  have outside : 0x2a74e ≤ (result g.core).pc := by
    rw [retpc]; simp only [PlayerDamageEntry.sites,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at site; omega
  have trun := original_execution g.core g.flags ins outside
  rw [← gp] at trun
  obtain ⟨k,hk,tail,_⟩ := X86Routine.run_path trun
  have tail := tail.transfer joined exits contains_tail tail_active
  have done : (result g.core).pc ∈ exits := by
    rw [retpc]; simp only [PlayerDamageEntry.sites,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at site
    rcases site with rfl | rfl | rfl <;> decide
  have rest : X86Routine.run joined exits 14 g = some (result g.core) :=
    tail.finish (fuel := 0) (by simp [X86Routine.run,done]) 14 (by omega)
  refine ⟨g,result g.core,grun,gobs,path.finish rest 166 (by omega),retpc,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [result,restored,beforePops,write,gsp,BitVec.sub_eq_add_neg,BitVec.add_assoc]
  · change load32 (resetMemory g.core) (g.core.regs 4+(12#32)) = s.regs 5
    rw [a12]
    rw [retread _ (by simp [savedReads]),slots.2.2.2.1]
  · have view : (result g.core).core.regs 6 = load32 (resetMemory g.core) (g.core.regs 4+(20#32)) := by
      simp [result,restored,beforePops,write,BitVec.add_assoc]
    rw [view]
    rw [a20]
    rw [retread _ (by simp [savedReads]),slots.2.1]
  · have view : (result g.core).core.regs 7 = load32 (resetMemory g.core) (g.core.regs 4+(16#32)) := by
      simp [result,restored,beforePops,write,BitVec.add_assoc]
    rw [view]
    rw [a16]
    rw [retread _ (by simp [savedReads]),slots.2.2.1]
  · rw [← gobj]; exact reaction_zero g.core
  · intro a ha; apply memory_frame
    intro b hb; simp only [List.mem_singleton] at hb; subst b
    simpa [reaction,gobj] using h.reactionRetainedSafe a ha
  · intro a safe
    rw [memory_frame g.core a]
    · exact gframe a (fun b hb => safe b (by simp [joinedWrites,hb]))
    · intro b hb; simp only [List.mem_singleton] at hb; subst b
      exact safe _ (by simp [joinedWrites,reaction,gobj])

def memoryFields (s : X86Memory.State) (m : Memory) :=
  let p := PlayerDamageEntry.inputPlayer s
  ((load32 m (p+(36#32)),load32 m (p+(40#32)),load32 m (p+(32#32)),
    load32 m (p+(220#32)),load32 m (p+(228#32))),
   load32 m (s.regs 0+(108#32)),load32 m (0x12720#32),
   load32 m (s.regs 0+(104#32)),PainSetter.observeFields m (s.regs 0))
def liveFields (s : X86Memory.State) (out : PlayerDamage.Result) :=
  ((out.state.armor.toBitVec,out.state.armorType.toBitVec,out.state.playerHealth.toBitVec,
    out.state.damageCount.toBitVec,(0#32)),out.state.health.toBitVec,BitVec.ofNat 32 out.rng.play.toNat,
    load32 s.memory (s.regs 0+(104#32)) ||| (if out.pain then (64#32) else (0#32)),
    if out.pain then PainSetter.painFields else PainSetter.observeFields s.memory (s.regs 0))

theorem memory_observation (s : X86Memory.State) (g : X86Control.State) (v : PlayerDamage.State)
    (out : PlayerDamage.Result) (applied : out.applied=true)
    (obs : PainSetter.observation s g = PainSetter.liveObservation s v out) :
    memoryFields s g.core.memory = liveFields s out := by
  have mapped := congrArg (fun x => (x.1.1.1.map Prod.snd,x.1.1.2.map Prod.fst,x.1.2,x.2.1,x.2.2)) obs
  by_cases gp : g.pc=0x2a747
  · simp [PainSetter.observation,PainSetter.liveObservation,ActorHealth.observation,
      ActorHealth.liveObservation,PlayerHealth.observation,PlayerHealth.liveObservation,gp,applied] at mapped
  · simpa [memoryFields,liveFields,PainSetter.observation,PainSetter.liveObservation,
      ActorHealth.observation,ActorHealth.liveObservation,PlayerHealth.observation,PlayerHealth.liveObservation,
      gp,applied] using mapped

def observation (s : X86Memory.State) (t : X86Control.State) :=
  (memoryFields s t.core.memory,load32 t.core.memory (s.regs 0+(124#32)))
def liveObservation (s : X86Memory.State) (out : PlayerDamage.Result) :=
  (liveFields s out,(out.reactionTime (Int32.ofBitVec (load32 s.memory (s.regs 0+(124#32))))).toBitVec)

/-- The return-boundary observation reads memory after the real RET; scratch
registers and the pre-return PC are not used to reconstruct gameplay results. -/
theorem live_correspondence (s : X86Memory.State) (f : Option Flags) (pc : Nat)
    (site : pc ∈ PlayerDamageEntry.sites) (v : PlayerDamage.State) (d : Int32) (baby : Bool)
    (rng : DoomRandom) (h : JoinedInputs s v d baby rng.play)
    (applied : (PlayerDamage.apply v d none false baby rng).applied = true)
    (alive : (PlayerDamage.apply v d none false baby rng).killed = false) :
    (X86Routine.run joined exits 166 ⟨s,f,pc⟩).map (observation s) =
      some (liveObservation s (PlayerDamage.apply v d none false baby rng)) := by
  obtain ⟨g,t,_,obs,run,_,_,_,_,_,zero,keep,_⟩ := joined_execution s f pc site v d baby rng h applied alive
  have mem : memoryFields s t.core.memory = memoryFields s g.core.memory := by
    unfold memoryFields PainSetter.observeFields
    dsimp only
    repeat rw [keep _ (by simp [retained,PainSetter.retained,PainHandoff.retained,ActorHealth.fields,PainSetter.fields])]
  rw [run,Option.map_some]
  congr 1
  unfold observation liveObservation
  rw [mem,memory_observation s g v _ applied obs,zero]
  simp [PlayerDamage.Result.reactionTime,applied,alive]

end Doom.Proofs.DamageReturn
