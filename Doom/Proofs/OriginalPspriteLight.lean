import Doom.Proofs.E1M1PspriteChain
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
namespace Doom.Proofs.PspriteLight
open Verification X86 X86Memory X86Control BlockSummary

def entry (i : Fin 3) : Nat := 0x2db40+16*i.val
def code (i : Fin 3) : List UInt8 := [0xc7,0x80,0xe8,0,0,0,UInt8.ofNat i.val,0,0,0,0xc3]
def bytesProgram (bytes : Fin 3 → List UInt8) : X86Routine.Program := fun pc =>
  if 0x2db40 ≤ pc ∧ pc < 0x2db4b then X86Routine.decodeAt (bytes 0) (pc-0x2db40)
  else if 0x2db50 ≤ pc ∧ pc < 0x2db5b then X86Routine.decodeAt (bytes 1) (pc-0x2db50)
  else if 0x2db60 ≤ pc ∧ pc < 0x2db6b then X86Routine.decodeAt (bytes 2) (pc-0x2db60)
  else none
def program := bytesProgram code

theorem decoded_store (i : Fin 3) : program (entry i)=some (.storeImmediate ⟨some 0,none,0,232⟩ (BitVec.ofNat 32 i.val),10) := by
  rcases i with ⟨i,hi⟩; have h : i=0 ∨ i=1 ∨ i=2 := by omega
  rcases h with rfl|rfl|rfl <;> simp only [entry,Fin.val_mk] <;> decide

theorem decoded_return (i : Fin 3) : program (entry i+10)=some (.ret,1) := by
  rcases i with ⟨i,hi⟩; have h : i=0 ∨ i=1 ∨ i=2 := by omega
  rcases h with rfl|rfl|rfl <;> simp only [entry,Fin.val_mk] <;> decide

def written (i : Fin 3) (s : X86Memory.State) : X86Memory.State :=
  {s with memory := store32 s.memory (s.regs 0+232) (BitVec.ofNat 32 i.val)}
def result (i : Fin 3) (s : X86Memory.State) (f : Option Flags) : X86Control.State :=
  let t := written i s
  ⟨put t 4 (s.regs 4+4),f,(load32 t.memory (s.regs 4)).toNat⟩

/-- All three original light actions: a full-word write and the actual RET.
No stack separation is silently assumed: the RET sees the updated memory. -/
theorem execution (i : Fin 3) (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 2 ⟨s,f,entry i⟩ (result i s f) := by
  apply X86Routine.Prefix.step (middle := ⟨written i s,f,entry i+10⟩) (by simp) (decoded_store i) (by
    simp [X86Routine.execute,X86Block.Address.eval,written])
  apply X86Routine.Prefix.step (middle := result i s f) (by simp) (decoded_return i) rfl
  exact X86Routine.Prefix.nil _

theorem effect (i : Fin 3) (s : X86Memory.State) (f : Option Flags) :
    load32 (result i s f).core.memory (s.regs 0+232)=BitVec.ofNat 32 i.val ∧
    (result i s f).core.regs=write s.regs 4 (s.regs 4+4) ∧
    (result i s f).flags=f := by
  simp [result,written,put,load_store]

theorem frame (i : Fin 3) (s : X86Memory.State) (f : Option Flags)
    (a : Word) (safe : Apart a (s.regs 0+232)) :
    load32 (result i s f).core.memory a=load32 s.memory a :=
  load_store_apart _ _ _ _ safe

theorem return_address (i : Fin 3) (s : X86Memory.State) (f : Option Flags)
    (safe : Apart (s.regs 4) (s.regs 0+232)) :
    (result i s f).pc=(load32 s.memory (s.regs 4)).toNat := by
  simp only [result,written]
  rw [load_store_apart _ _ _ _ safe]


/-- Original IDs for LIGHTDONE, pistol flash, and both shotgun flashes. -/
def stateId (i : Fin 4) : Nat := match i.val with
  | 0 => 1 | 1 => 17 | 2 => 30 | _ => 31
def stateLight (i : Fin 4) : Fin 3 := match i.val with
  | 0 => 0 | 3 => 2 | _ => 1

theorem live_actions (i : Fin 4) :
    (WeaponData.frames[stateId i]!).action=
      (if stateLight i=0 then "A_Light0" else if stateLight i=1 then "A_Light1" else "A_Light2") := by
  rcases i with ⟨i,hi⟩; have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;> simp only [stateId,stateLight,Fin.val_mk] <;> decide

end Doom.Proofs.PspriteLight
