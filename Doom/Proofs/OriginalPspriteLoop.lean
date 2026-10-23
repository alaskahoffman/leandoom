import Doom.Proofs.E1M1PspriteStep
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.PspriteLoop
open Verification X86 X86Memory X86Control BlockSummary

def code : List UInt8 := [0x46,0x83,0xc1,0x10,0x83,0xfe,0x2,0x7c,0xd1,0x8b,0x9f,0xfc,0x0,0x0,0x0,0x89,0x9f,0xc,0x1,0x0,0x0,0x8b,0x9f,0x0,0x1,0x0,0x0,0x89,0x9f,0x10,0x1,0x0,0x0,0x5f,0x5e,0x5a,0x59,0x5b,0xc3]
def bytesProgram (bytes : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2dc95 ≤ pc ∧ pc < 0x2dcbc then X86Routine.decodeAt bytes (pc-0x2dc95) else none
def program := bytesProgram code
def listed : X86Routine.Program
  | 0x2dc95 => some (.addImmediate 6 1,1)
  | 0x2dc96 => some (.addImmediate 1 16,3)
  | 0x2dc99 => some (.compareRegister 6 2,3)
  | 0x2dc9c => some (.jumpSigned 3 (-47),2)
  | 0x2dc9e => some (.control (.block (.load 3 ⟨some 7,none,0,252⟩)),6)
  | 0x2dca4 => some (.control (.block (.store ⟨some 7,none,0,268⟩ 3)),6)
  | 0x2dcaa => some (.control (.block (.load 3 ⟨some 7,none,0,256⟩)),6)
  | 0x2dcb0 => some (.control (.block (.store ⟨some 7,none,0,272⟩ 3)),6)
  | 0x2dcb6 => some (.pop 7,1)
  | 0x2dcb7 => some (.pop 6,1)
  | 0x2dcb8 => some (.pop 2,1)
  | 0x2dcb9 => some (.pop 1,1)
  | 0x2dcba => some (.pop 3,1)
  | 0x2dcbb => some (.ret,1)
  | _ => none

theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def advanced (s : X86Memory.State) : X86Control.State :=
  ⟨put (put s 6 (s.regs 6+1)) 1 (s.regs 1+16),some (compare32 (s.regs 6+1) 2),
    if (s.regs 6+1).toInt < 2 then 0x2dc6f else 0x2dc9e⟩

/-- The counter wraps as a machine word; the loop comparison is signed. INC
flags are discarded by the model and overwritten by CMP before any branch. -/
theorem advance_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x2dc6f,0x2dc9e] 4 ⟨s,f,0x2dc95⟩=some (advanced s) := by
  have run : X86Routine.run listed [0x2dc6f,0x2dc9e] 4 ⟨s,f,0x2dc95⟩=some (advanced s) := by
    by_cases h : (s.regs 6+(1#32)).toInt < 2 <;>
    simp [X86Routine.run,listed,X86Routine.execute,advanced,put,write,PlayerArmor.cmp_lt,PlayerHeight.cmp_ge_prop,←Int.not_lt,h,-BitVec.toInt_add]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

theorem slot_order (s : X86Memory.State) (i : Fin 2) (index : s.regs 6=BitVec.ofNat 32 i.val) :
    (advanced s).pc=(if i.val=0 then 0x2dc6f else 0x2dc9e) ∧
    (advanced s).core.regs 6=BitVec.ofNat 32 (i.val+1) ∧
    (advanced s).core.regs 1=s.regs 1+16 := by
  have cases : i=0 ∨ i=1 := by omega
  rcases cases with e | e <;> subst i <;> simp [advanced,index,put,write]

def copyX (s : X86Memory.State) : X86Memory.State :=
  let x := load32 s.memory (s.regs 7+252)
  {put s 3 x with memory := store32 s.memory (s.regs 7+268) x}
def copied (s : X86Memory.State) : X86Memory.State :=
  let t := copyX s
  let y := load32 t.memory (t.regs 7+256)
  {put t 3 y with memory := store32 t.memory (t.regs 7+272) y}

/-- Flash coordinates are copied after both slots, using the updated weapon
coordinates. Loads and stores retain their original order. -/
theorem copy_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x2dcb6] 4 ⟨s,f,0x2dc9e⟩=some ⟨copied s,f,0x2dcb6⟩ := by
  let c1 := put s 3 (load32 s.memory (s.regs 7+252))
  let c2 := copyX s
  let c3 := put c2 3 (load32 c2.memory (c2.regs 7+256))
  have path : X86Routine.Prefix listed [0x2dcb6] 4 ⟨s,f,0x2dc9e⟩ ⟨copied s,f,0x2dcb6⟩ := by
    apply X86Routine.Prefix.step (middle := ⟨c1,f,0x2dca4⟩) (by simp) rfl (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,c1])
    apply X86Routine.Prefix.step (middle := ⟨c2,f,0x2dcaa⟩) (by simp) rfl (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,c1,c2,copyX,put,write])
    apply X86Routine.Prefix.step (middle := ⟨c3,f,0x2dcb0⟩) (by simp) rfl (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,c3])
    apply X86Routine.Prefix.step (middle := ⟨copied s,f,0x2dcb6⟩) (by simp) rfl (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,copied,c3,c2,put,write,copyX])
    exact X86Routine.Prefix.nil _
  have run := path.run 0
  have run : X86Routine.run listed [0x2dcb6] 4 ⟨s,f,0x2dc9e⟩=some ⟨copied s,f,0x2dcb6⟩ := by
    simpa [X86Routine.run] using run
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

def popped (s : X86Memory.State) (r : Reg) : X86Memory.State :=
  put (put s 4 (s.regs 4+4)) r (load32 s.memory (s.regs 4))
def restored (s : X86Memory.State) : X86Memory.State :=
  popped (popped (popped (popped (popped s 7) 6) 2) 1) 3
def returned (s : X86Memory.State) (f : Option Flags) : X86Control.State :=
  let t := restored s
  ⟨put t 4 (t.regs 4+4),f,(load32 t.memory (t.regs 4)).toNat⟩

/-- Actual POPs and RET, reading the real current stack. No assumed return
address or separation contract is needed in the flat machine model. -/
theorem return_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 6 ⟨s,f,0x2dcb6⟩ (returned s f) := by
  have path : X86Routine.Prefix listed [] 6 ⟨s,f,0x2dcb6⟩ (returned s f) := by
    apply X86Routine.Prefix.step (middle := ⟨popped s 7,f,0x2dcb7⟩) (by simp) rfl rfl
    apply X86Routine.Prefix.step (middle := ⟨popped (popped s 7) 6,f,0x2dcb8⟩) (by simp) rfl rfl
    apply X86Routine.Prefix.step (middle := ⟨popped (popped (popped s 7) 6) 2,f,0x2dcb9⟩) (by simp) rfl rfl
    apply X86Routine.Prefix.step (middle := ⟨popped (popped (popped (popped s 7) 6) 2) 1,f,0x2dcba⟩) (by simp) rfl rfl
    apply X86Routine.Prefix.step (middle := ⟨restored s,f,0x2dcbb⟩) (by simp) rfl rfl
    apply X86Routine.Prefix.step (middle := returned s f) (by simp) rfl rfl
    exact X86Routine.Prefix.nil _
  exact path.transfer program [] decoded (by simp)

theorem copied_coordinates (s : X86Memory.State) :
    load32 (copied s).memory (s.regs 7+268)=load32 s.memory (s.regs 7+252) ∧
    load32 (copied s).memory (s.regs 7+272)=load32 s.memory (s.regs 7+256) := by
  have xy : Apart (s.regs 7+(256#32)) (s.regs 7+(268#32)) := by
    have h := PlayerHealth.offsets_apart (s.regs 7+(252#32)) 4 16 (by decide)
    change Apart ((s.regs 7+(252#32))+(4#32)) ((s.regs 7+(252#32))+(16#32)) at h
    simpa [BitVec.add_assoc] using h
  have dest : Apart (s.regs 7+(268#32)) (s.regs 7+(272#32)) := by
    have h := PlayerHealth.offsets_apart (s.regs 7+(252#32)) 16 20 (by decide)
    change Apart ((s.regs 7+(252#32))+(16#32)) ((s.regs 7+(252#32))+(20#32)) at h
    simpa [BitVec.add_assoc] using h
  simp [copied,copyX,put,write,load_store,load_store_apart _ _ _ _ xy,load_store_apart _ _ _ _ dest]

theorem return_stack (s : X86Memory.State) (f : Option Flags) :
    (returned s f).pc=(load32 s.memory (s.regs 4+20)).toNat ∧
    (returned s f).core.regs 4=s.regs 4+24 ∧
    (returned s f).core.memory=s.memory ∧ (returned s f).flags=f := by
  simp [returned,restored,popped,put,write,BitVec.add_assoc]

end Doom.Proofs.PspriteLoop
