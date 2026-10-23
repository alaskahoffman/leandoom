import Doom.Proofs.OriginalMoveMotion
import Doom.Verification.X86Routine
import Doom.PlayerAnim

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 3200000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs
open Verification X86 X86Memory X86Control BlockSummary
namespace PlayerAnimation
open X86Routine

/-- The only instruction addresses used by the walking-entry path. Omitted
branches (null state, actions and zero-tic chaining) fail closed if reached. -/
def caller : X86Routine.Program
  | 0 => some (.compareByte ⟨some 6,none,0,0⟩ 0,3)
  | 3 => some (.control (.jumpZero false 6),2)
  | 5 => some (.compareByte ⟨some 6,none,0,1⟩ 0,4)
  | 9 => some (.control (.jumpZero true 21),2)
  | 11 => some (.control (.block (.legacy (.load 0 1 0))),2)
  | 13 => some (.control (.cmpImmediate ⟨some 0,none,0,100⟩ 0x16a74),7)
  | 20 => some (.control (.jumpZero false 10),2)
  | 22 => some (.immediate 2 150,5)
  | 27 => some (.call (-9150),5)
  | _ => none

def callee : X86Routine.Program
  | 0 => some (.push 3,1)
  | 1 => some (.push 6,1)
  | 2 => some (.control (.block (.legacy (.mov 3 0))),2)
  | 4 => some (.control (.testWord 2 2),2)
  | 6 => some (.control (.jumpZero false 19),2)
  | 27 => some (.multiplyImmediate 2 2 28,3)
  | 30 => some (.addImmediate 2 0x15a28,6)
  | 36 => some (.control (.block (.store ⟨some 3,none,0,100⟩ 2)),3)
  | 39 => some (.control (.block (.legacy (.load 0 2 8))),3)
  | 42 => some (.control (.block (.store ⟨some 3,none,0,96⟩ 0)),3)
  | 45 => some (.control (.block (.legacy (.load 0 2 0))),2)
  | 47 => some (.control (.block (.store ⟨some 3,none,0,36⟩ 0)),3)
  | 50 => some (.control (.block (.legacy (.load 0 2 4))),3)
  | 53 => some (.control (.block (.store ⟨some 3,none,0,40⟩ 0)),3)
  | 56 => some (.control (.cmpImmediate ⟨some 2,none,0,12⟩ 0),4)
  | 60 => some (.control (.jumpZero true 5),2)
  | 67 => some (.control (.block (.legacy (.load 6 3 96))),3)
  | 70 => some (.control (.block (.legacy (.load 2 2 16))),3)
  | 73 => some (.control (.testWord 6 6),2)
  | 75 => some (.control (.jumpZero false 6),2)
  | 83 => some (.immediate 0 1,5)
  | 88 => some (.pop 6,1)
  | 89 => some (.pop 3,1)
  | 90 => some (.ret,1)
  | _ => none

def program : X86Routine.Program := fun pc =>
  if 0x3323e ≤ pc then caller (pc-0x3323e)
  else if 0x30ea0 ≤ pc then callee (pc-0x30ea0) else none

/-- Decode both original regions at their DOS code-object offsets. Callee entry
is 0x30ea0, caller entry is 0x3323e, and the saved return PC is 0x3325e.
Data operands remain data-object-relative; code loading is external. -/
def bytesProgram (caller callee : List UInt8) : X86Routine.Program := fun pc =>
  if 0x3323e ≤ pc ∧ pc < 0x3323e + caller.length then X86Routine.decodeAt caller (pc-0x3323e)
  else if 0x30ea0 ≤ pc ∧ pc < 0x30ea0 + callee.length then X86Routine.decodeAt callee (pc-0x30ea0)
  else none

theorem caller_decoded (pc : Nat) (h : caller pc ≠ none) :
    X86Routine.decodeAt Doom19.playerAnimationBytes pc = caller pc := by
  fun_cases caller pc <;> simp_all [caller] <;> rfl

theorem callee_decoded (pc : Nat) (h : callee pc ≠ none) :
    X86Routine.decodeAt Doom19.setMobjStateBytes pc = callee pc := by
  fun_cases callee pc <;> simp_all [callee] <;> rfl

theorem caller_bound (pc : Nat) (h : caller pc ≠ none) : pc < 32 := by
  fun_cases caller pc <;> simp_all [caller] <;> omega

theorem callee_bound (pc : Nat) (h : callee pc ≠ none) : pc < 91 := by
  fun_cases callee pc <;> simp_all [callee] <;> omega

theorem decoded (pc : Nat) (h : program pc ≠ none) :
    bytesProgram Doom19.playerAnimationBytes Doom19.setMobjStateBytes pc = program pc := by
  by_cases hp : 0x3323e ≤ pc
  · simp only [program,hp,↓reduceIte] at h ⊢
    have bound := caller_bound _ h
    unfold bytesProgram
    rw [if_pos (show 0x3323e ≤ pc ∧ pc < 0x3323e + Doom19.playerAnimationBytes.length by change _ ∧ pc < 0x3323e + 32; omega)]
    exact caller_decoded _ h
  · by_cases hc : 0x30ea0 ≤ pc
    · simp only [program,hp,hc,↓reduceIte] at h ⊢
      have bound := callee_bound _ h
      unfold bytesProgram
      rw [if_neg (by omega),if_pos (show 0x30ea0 ≤ pc ∧ pc < 0x30ea0 + Doom19.setMobjStateBytes.length by change _ ∧ pc < 0x30ea0 + 91; omega)]
      exact callee_decoded _ h
    · simp [program,hp,hc] at h

def fields (obj : Word) : List Word := [obj+(100#32),obj+(96#32),obj+(36#32),obj+(40#32)]
def tableWords : List Word := [0x16a90,0x16a94,0x16a98,0x16a9c,0x16aa0]

structure RunTable (m : Memory) : Prop where
  sprite : load32 m (0x16a90#32) = 28
  frame : load32 m (0x16a94#32) = 0
  tics : load32 m (0x16a98#32) = 4
  action : load32 m (0x16a9c#32) = 0
  next : load32 m (0x16aa0#32) = 151

/-- Callee-entry relation for the specific non-null, non-zero-tic, no-action
walking state. The saved return address is part of ordinary stack memory. -/
structure SetterInputs (s : X86Memory.State) : Prop where
  state : s.regs 2 = 150
  table : RunTable s.memory
  returnAddress : load32 s.memory (s.regs 4) = 0x3325e
  tableSafe : ∀ a, a ∈ tableWords → ∀ b, b ∈ fields (s.regs 0) ++ [s.regs 4-(4#32),s.regs 4-(8#32)] → Apart a b
  stackSafe : ∀ a, a ∈ [s.regs 4,s.regs 4-(4#32),s.regs 4-(8#32)] →
    ∀ b, b ∈ fields (s.regs 0) → Apart a b

def savedMemory (s : X86Memory.State) : Memory :=
  store32 (store32 s.memory (s.regs 4-(4#32)) (s.regs 3)) (s.regs 4-(8#32)) (s.regs 6)

def entryMemory (m : Memory) (obj : Word) : Memory :=
  store32 (store32 (store32 (store32 m (obj+(100#32)) 0x16a90)
    (obj+(96#32)) 4) (obj+(36#32)) 28) (obj+(40#32)) 0

def setterEnd (s : X86Memory.State) : X86Control.State :=
  ⟨⟨write (write (write s.regs 0 1) 2 151) 4 (s.regs 4+(4#32)),
    entryMemory (savedMemory s) (s.regs 0)⟩,some (logical32 4),0x3325e⟩

private theorem apart_offsets (base a b : Word) (h : ∀ i j : Fin 4,
    a + BitVec.ofNat 32 i.val ≠ b + BitVec.ofNat 32 j.val) : Apart (base+a) (base+b) := by
  intro i j eq
  apply h i j
  apply (BitVec.add_right_inj base).mp
  simpa only [BitVec.add_assoc] using eq

theorem stack_apart (sp : Word) : Apart sp (sp-(4#32)) ∧ Apart sp (sp-(8#32)) ∧
    Apart (sp-(4#32)) (sp-(8#32)) := by
  have a : Apart (sp+(0#32)) (sp+(-4#32)) := apart_offsets sp 0 (-4) (by decide)
  have b : Apart (sp+(0#32)) (sp+(-8#32)) := apart_offsets sp 0 (-8) (by decide)
  have c : Apart (sp+(-4#32)) (sp+(-8#32)) := apart_offsets sp (-4) (-8) (by decide)
  simpa only [BitVec.add_zero,BitVec.sub_eq_add_neg] using And.intro a (And.intro b c)

theorem tics_apart (obj : Word) : Apart (obj+(96#32)) (obj+(36#32)) ∧ Apart (obj+(96#32)) (obj+(40#32)) :=
  ⟨apart_offsets obj 96 36 (by decide),apart_offsets obj 96 40 (by decide)⟩

private theorem at_30ea0 : program 0x30ea0 = callee 0 := by decide
private theorem at_30ea1 : program 0x30ea1 = callee 1 := by decide
private theorem at_30ea2 : program 0x30ea2 = callee 2 := by decide
private theorem at_30ea4 : program 0x30ea4 = callee 4 := by decide
private theorem at_30ea6 : program 0x30ea6 = callee 6 := by decide
private theorem at_30ebb : program 0x30ebb = callee 27 := by decide
private theorem at_30ebe : program 0x30ebe = callee 30 := by decide
private theorem at_30ec4 : program 0x30ec4 = callee 36 := by decide
private theorem at_30ec7 : program 0x30ec7 = callee 39 := by decide
private theorem at_30eca : program 0x30eca = callee 42 := by decide
private theorem at_30ecd : program 0x30ecd = callee 45 := by decide
private theorem at_30ecf : program 0x30ecf = callee 47 := by decide
private theorem at_30ed2 : program 0x30ed2 = callee 50 := by decide
private theorem at_30ed5 : program 0x30ed5 = callee 53 := by decide
private theorem at_30ed8 : program 0x30ed8 = callee 56 := by decide
private theorem at_30edc : program 0x30edc = callee 60 := by decide
private theorem at_30ee3 : program 0x30ee3 = callee 67 := by decide
private theorem at_30ee6 : program 0x30ee6 = callee 70 := by decide
private theorem at_30ee9 : program 0x30ee9 = callee 73 := by decide
private theorem at_30eeb : program 0x30eeb = callee 75 := by decide
private theorem at_30ef3 : program 0x30ef3 = callee 83 := by decide
private theorem at_30ef8 : program 0x30ef8 = callee 88 := by decide
private theorem at_30ef9 : program 0x30ef9 = callee 89 := by decide
private theorem at_30efa : program 0x30efa = callee 90 := by decide

def prologueEnd (s : X86Memory.State) : X86Control.State :=
  ⟨⟨write (write s.regs 4 (s.regs 4-(8#32))) 3 (s.regs 0),savedMemory s⟩,
    some (logical32 150),0x30ebb⟩

def bodyEnd (s : X86Memory.State) : X86Control.State :=
  ⟨⟨write (write (write (write (write s.regs 4 (s.regs 4-(8#32))) 3 (s.regs 0)) 0 0) 6 4) 2 151,
    entryMemory (savedMemory s) (s.regs 0)⟩,some (logical32 4),0x30ef3⟩

theorem setter_prologue (s : X86Memory.State) (flags : Option Flags) (state : s.regs 2 = 150) :
    X86Routine.run program [0x30ebb] 5 ⟨s,flags,0x30ea0⟩ = some (prologueEnd s) := by
  let s1 := X86Routine.pushWord s (s.regs 3)
  let s2 := X86Routine.pushWord s1 (s.regs 6)
  let s3 := put s2 3 (s.regs 0)
  have path : X86Routine.Prefix program [0x30ebb] 5 ⟨s,flags,0x30ea0⟩
      ⟨s3,some (logical32 150),0x30ebb⟩ := by
    apply X86Routine.Prefix.step (middle := ⟨s1,flags,0x30ea1⟩) (by change ¬((0x30ea0:Nat) ∈ [0x30ebb]); decide)
      (show program 0x30ea0 = some (.push 3,1) from by decide) (by rfl)
    apply X86Routine.Prefix.step (middle := ⟨s2,flags,0x30ea2⟩) (by change ¬((0x30ea1:Nat) ∈ [0x30ebb]); decide)
      (show program 0x30ea1 = some (.push 6,1) from by decide) (by
        simp [X86Routine.execute,s1,s2,X86Routine.pushWord,put,write])
    apply X86Routine.Prefix.step (middle := ⟨s3,flags,0x30ea4⟩) (by change ¬((0x30ea2:Nat) ∈ [0x30ebb]); decide)
      (show program 0x30ea2 = some (.control (.block (.legacy (.mov 3 0))),2) from by decide) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
          blockPreservesFlags,s3,s2,s1,X86Routine.pushWord,put,write])
    apply X86Routine.Prefix.step (middle := ⟨s3,some (logical32 150),0x30ea6⟩) (by change ¬((0x30ea4:Nat) ∈ [0x30ebb]); decide)
      (show program 0x30ea4 = some (.control (.testWord 2 2),2) from by decide) (by
        simp [X86Routine.execute,X86Control.execute,s3,s2,s1,X86Routine.pushWord,put,write,state])
    apply X86Routine.Prefix.step (middle := ⟨s3,some (logical32 150),0x30ebb⟩) (by change ¬((0x30ea6:Nat) ∈ [0x30ebb]); decide)
      (show program 0x30ea6 = some (.control (.jumpZero false 19),2) from by decide) (by
        simp [X86Routine.execute,X86Control.execute,logical32])
    exact X86Routine.Prefix.nil _
  rw [show 5 = 5+0 from rfl,path.run 0]
  simp [X86Routine.run,prologueEnd,s3,s2,s1,savedMemory,X86Routine.pushWord,put,write,BitVec.sub_sub]
  funext r
  by_cases h3 : r = 3 <;> by_cases h4 : r = 4 <;> simp_all [write]

theorem setter_body (s : X86Memory.State) (h : SetterInputs s) :
    X86Routine.run program [0x30ef3] 15 (prologueEnd s) = some (bodyEnd s) := by
  have active_27 : (0x30ebb:Nat) ∉ [0x30ef3] := by decide
  have active_30 : (0x30ebe:Nat) ∉ [0x30ef3] := by decide
  have active_36 : (0x30ec4:Nat) ∉ [0x30ef3] := by decide
  have active_39 : (0x30ec7:Nat) ∉ [0x30ef3] := by decide
  have active_42 : (0x30eca:Nat) ∉ [0x30ef3] := by decide
  have active_45 : (0x30ecd:Nat) ∉ [0x30ef3] := by decide
  have active_47 : (0x30ecf:Nat) ∉ [0x30ef3] := by decide
  have active_50 : (0x30ed2:Nat) ∉ [0x30ef3] := by decide
  have active_53 : (0x30ed5:Nat) ∉ [0x30ef3] := by decide
  have active_56 : (0x30ed8:Nat) ∉ [0x30ef3] := by decide
  have active_60 : (0x30edc:Nat) ∉ [0x30ef3] := by decide
  have active_67 : (0x30ee3:Nat) ∉ [0x30ef3] := by decide
  have active_70 : (0x30ee6:Nat) ∉ [0x30ef3] := by decide
  have active_73 : (0x30ee9:Nat) ∉ [0x30ef3] := by decide
  have active_75 : (0x30eeb:Nat) ∉ [0x30ef3] := by decide

  have tableLoad (m : Memory) (a b v : Word) (ha : a ∈ tableWords)
      (hb : b ∈ fields (s.regs 0) ++ [s.regs 4-(4#32),s.regs 4-(8#32)]) :=
    load_store_apart m b a v (h.tableSafe a ha b hb)
  have stackLoad (m : Memory) (a b v : Word)
      (ha : a ∈ [s.regs 4,s.regs 4-(4#32),s.regs 4-(8#32)]) (hb : b ∈ fields (s.regs 0)) :=
    load_store_apart m b a v (h.stackSafe a ha b hb)
  have st := stack_apart (s.regs 4)
  have ti := tics_apart (s.regs 0)
  have addback : s.regs 4-(8#32)+(4#32) = s.regs 4-(4#32) := by bv_decide
  let c0 := (prologueEnd s).core
  let c1 : X86Memory.State := put c0 2 4200
  let c2 : X86Memory.State := put c1 2 0x16a90
  let c3 : X86Memory.State := {c2 with memory := store32 c2.memory (s.regs 0+100) 0x16a90}
  let c4 : X86Memory.State := put c3 0 4
  let c5 : X86Memory.State := {c4 with memory := store32 c4.memory (s.regs 0+96) 4}
  let c6 : X86Memory.State := put c5 0 28
  let c7 : X86Memory.State := {c6 with memory := store32 c6.memory (s.regs 0+36) 28}
  let c8 : X86Memory.State := put c7 0 0
  let c9 : X86Memory.State := {c8 with memory := store32 c8.memory (s.regs 0+40) 0}
  let c10 : X86Memory.State := c9
  let c11 : X86Memory.State := c10
  let c12 : X86Memory.State := put c11 6 4
  let c13 : X86Memory.State := put c12 2 151
  let c14 : X86Memory.State := c13
  let c15 : X86Memory.State := c14
  have path : X86Routine.Prefix program [0x30ef3] 15 (prologueEnd s)
      ⟨c15,some (logical32 4),0x30ef3⟩ := by
    apply X86Routine.Prefix.step (middle := ⟨c1,none,0x30ebe⟩)
      (by change ¬((0x30ebb:Nat) ∈ [0x30ef3]); decide)
      (show program 0x30ebb = some (.multiplyImmediate 2 2 28,3) from by decide) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,put,write,blockPreservesFlags,h.state,logical32,compare32,tableLoad,fields,tableWords,load_store_apart _ _ _ _ ti.1,load_store_apart _ _ _ _ ti.2,load_store,h.table.sprite,h.table.frame,h.table.tics,h.table.action,h.table.next,prologueEnd,savedMemory,c1,c0])
    apply X86Routine.Prefix.step (middle := ⟨c2,none,0x30ec4⟩)
      (by change ¬((0x30ebe:Nat) ∈ [0x30ef3]); decide)
      (show program 0x30ebe = some (.addImmediate 2 0x15a28,6) from by decide) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,put,write,blockPreservesFlags,h.state,logical32,compare32,tableLoad,fields,tableWords,load_store_apart _ _ _ _ ti.1,load_store_apart _ _ _ _ ti.2,load_store,h.table.sprite,h.table.frame,h.table.tics,h.table.action,h.table.next,prologueEnd,savedMemory,c2,c1,c0])
    apply X86Routine.Prefix.step (middle := ⟨c3,none,0x30ec7⟩)
      (by change ¬((0x30ec4:Nat) ∈ [0x30ef3]); decide)
      (show program 0x30ec4 = some (.control (.block (.store ⟨some 3,none,0,100⟩ 2)),3) from by decide) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,put,write,blockPreservesFlags,h.state,logical32,compare32,tableLoad,fields,tableWords,load_store_apart _ _ _ _ ti.1,load_store_apart _ _ _ _ ti.2,load_store,h.table.sprite,h.table.frame,h.table.tics,h.table.action,h.table.next,prologueEnd,savedMemory,c3,c2,c1,c0])
    apply X86Routine.Prefix.step (middle := ⟨c4,none,0x30eca⟩)
      (by change ¬((0x30ec7:Nat) ∈ [0x30ef3]); decide)
      (show program 0x30ec7 = some (.control (.block (.legacy (.load 0 2 8))),3) from by decide) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,put,write,blockPreservesFlags,h.state,logical32,compare32,tableLoad,fields,tableWords,load_store_apart _ _ _ _ ti.1,load_store_apart _ _ _ _ ti.2,load_store,h.table.sprite,h.table.frame,h.table.tics,h.table.action,h.table.next,prologueEnd,savedMemory,c4,c3,c2,c1,c0])
    apply X86Routine.Prefix.step (middle := ⟨c5,none,0x30ecd⟩)
      (by change ¬((0x30eca:Nat) ∈ [0x30ef3]); decide)
      (show program 0x30eca = some (.control (.block (.store ⟨some 3,none,0,96⟩ 0)),3) from by decide) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,put,write,blockPreservesFlags,h.state,logical32,compare32,tableLoad,fields,tableWords,load_store_apart _ _ _ _ ti.1,load_store_apart _ _ _ _ ti.2,load_store,h.table.sprite,h.table.frame,h.table.tics,h.table.action,h.table.next,prologueEnd,savedMemory,c5,c4,c3,c2,c1,c0])
    apply X86Routine.Prefix.step (middle := ⟨c6,none,0x30ecf⟩)
      (by change ¬((0x30ecd:Nat) ∈ [0x30ef3]); decide)
      (show program 0x30ecd = some (.control (.block (.legacy (.load 0 2 0))),2) from by decide) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,put,write,blockPreservesFlags,h.state,logical32,compare32,tableLoad,fields,tableWords,load_store_apart _ _ _ _ ti.1,load_store_apart _ _ _ _ ti.2,load_store,h.table.sprite,h.table.frame,h.table.tics,h.table.action,h.table.next,prologueEnd,savedMemory,c6,c5,c4,c3,c2,c1,c0])
    apply X86Routine.Prefix.step (middle := ⟨c7,none,0x30ed2⟩)
      (by change ¬((0x30ecf:Nat) ∈ [0x30ef3]); decide)
      (show program 0x30ecf = some (.control (.block (.store ⟨some 3,none,0,36⟩ 0)),3) from by decide) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,put,write,blockPreservesFlags,h.state,logical32,compare32,tableLoad,fields,tableWords,load_store_apart _ _ _ _ ti.1,load_store_apart _ _ _ _ ti.2,load_store,h.table.sprite,h.table.frame,h.table.tics,h.table.action,h.table.next,prologueEnd,savedMemory,c7,c6,c5,c4,c3,c2,c1,c0])
    apply X86Routine.Prefix.step (middle := ⟨c8,none,0x30ed5⟩)
      (by change ¬((0x30ed2:Nat) ∈ [0x30ef3]); decide)
      (show program 0x30ed2 = some (.control (.block (.legacy (.load 0 2 4))),3) from by decide) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,put,write,blockPreservesFlags,h.state,logical32,compare32,tableLoad,fields,tableWords,load_store_apart _ _ _ _ ti.1,load_store_apart _ _ _ _ ti.2,load_store,h.table.sprite,h.table.frame,h.table.tics,h.table.action,h.table.next,prologueEnd,savedMemory,c8,c7,c6,c5,c4,c3,c2,c1,c0])
    apply X86Routine.Prefix.step (middle := ⟨c9,none,0x30ed8⟩)
      (by change ¬((0x30ed5:Nat) ∈ [0x30ef3]); decide)
      (show program 0x30ed5 = some (.control (.block (.store ⟨some 3,none,0,40⟩ 0)),3) from by decide) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,put,write,blockPreservesFlags,h.state,logical32,compare32,tableLoad,fields,tableWords,load_store_apart _ _ _ _ ti.1,load_store_apart _ _ _ _ ti.2,load_store,h.table.sprite,h.table.frame,h.table.tics,h.table.action,h.table.next,prologueEnd,savedMemory,c9,c8,c7,c6,c5,c4,c3,c2,c1,c0])
    apply X86Routine.Prefix.step (middle := ⟨c10,some (compare32 0 0),0x30edc⟩)
      (by change ¬((0x30ed8:Nat) ∈ [0x30ef3]); decide)
      (show program 0x30ed8 = some (.control (.cmpImmediate ⟨some 2,none,0,12⟩ 0),4) from by decide) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,put,write,blockPreservesFlags,h.state,logical32,compare32,tableLoad,fields,tableWords,load_store_apart _ _ _ _ ti.1,load_store_apart _ _ _ _ ti.2,load_store,h.table.sprite,h.table.frame,h.table.tics,h.table.action,h.table.next,prologueEnd,savedMemory,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,c0])
    apply X86Routine.Prefix.step (middle := ⟨c11,some (compare32 0 0),0x30ee3⟩)
      (by change ¬((0x30edc:Nat) ∈ [0x30ef3]); decide)
      (show program 0x30edc = some (.control (.jumpZero true 5),2) from by decide) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,put,write,blockPreservesFlags,h.state,logical32,compare32,tableLoad,fields,tableWords,load_store_apart _ _ _ _ ti.1,load_store_apart _ _ _ _ ti.2,load_store,h.table.sprite,h.table.frame,h.table.tics,h.table.action,h.table.next,prologueEnd,savedMemory,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,c0])
    apply X86Routine.Prefix.step (middle := ⟨c12,some (compare32 0 0),0x30ee6⟩)
      (by change ¬((0x30ee3:Nat) ∈ [0x30ef3]); decide)
      (show program 0x30ee3 = some (.control (.block (.legacy (.load 6 3 96))),3) from by decide) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,put,write,blockPreservesFlags,h.state,logical32,compare32,tableLoad,fields,tableWords,load_store_apart _ _ _ _ ti.1,load_store_apart _ _ _ _ ti.2,load_store,h.table.sprite,h.table.frame,h.table.tics,h.table.action,h.table.next,prologueEnd,savedMemory,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,c0])
    apply X86Routine.Prefix.step (middle := ⟨c13,some (compare32 0 0),0x30ee9⟩)
      (by change ¬((0x30ee6:Nat) ∈ [0x30ef3]); decide)
      (show program 0x30ee6 = some (.control (.block (.legacy (.load 2 2 16))),3) from by decide) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,put,write,blockPreservesFlags,h.state,logical32,compare32,tableLoad,fields,tableWords,load_store_apart _ _ _ _ ti.1,load_store_apart _ _ _ _ ti.2,load_store,h.table.sprite,h.table.frame,h.table.tics,h.table.action,h.table.next,prologueEnd,savedMemory,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,c0])
    apply X86Routine.Prefix.step (middle := ⟨c14,some (logical32 4),0x30eeb⟩)
      (by change ¬((0x30ee9:Nat) ∈ [0x30ef3]); decide)
      (show program 0x30ee9 = some (.control (.testWord 6 6),2) from by decide) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,put,write,blockPreservesFlags,h.state,logical32,compare32,tableLoad,fields,tableWords,load_store_apart _ _ _ _ ti.1,load_store_apart _ _ _ _ ti.2,load_store,h.table.sprite,h.table.frame,h.table.tics,h.table.action,h.table.next,prologueEnd,savedMemory,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,c0])
    apply X86Routine.Prefix.step (middle := ⟨c15,some (logical32 4),0x30ef3⟩)
      (by change ¬((0x30eeb:Nat) ∈ [0x30ef3]); decide)
      (show program 0x30eeb = some (.control (.jumpZero false 6),2) from by decide) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,put,write,blockPreservesFlags,h.state,logical32,compare32,tableLoad,fields,tableWords,load_store_apart _ _ _ _ ti.1,load_store_apart _ _ _ _ ti.2,load_store,h.table.sprite,h.table.frame,h.table.tics,h.table.action,h.table.next,prologueEnd,savedMemory,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,c0])
    exact X86Routine.Prefix.nil _
  rw [show 15 = 15+0 from rfl,path.run 0]
  simp [X86Routine.run,bodyEnd,entryMemory,prologueEnd,put,write,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,c0]
  funext r
  by_cases h0 : r = 0 <;> by_cases h2 : r = 2 <;> by_cases h3 : r = 3 <;>
    by_cases h4 : r = 4 <;> by_cases h6 : r = 6 <;> simp_all [write]

theorem setter_epilogue (s : X86Memory.State) (h : SetterInputs s) :
    X86Routine.run program [0x3325e] 4 (bodyEnd s) = some (setterEnd s) := by
  have active_83 : (0x30ef3:Nat) ∉ [0x3325e] := by decide
  have active_88 : (0x30ef8:Nat) ∉ [0x3325e] := by decide
  have active_89 : (0x30ef9:Nat) ∉ [0x3325e] := by decide
  have active_90 : (0x30efa:Nat) ∉ [0x3325e] := by decide

  have tableLoad (m : Memory) (a b v : Word) (ha : a ∈ tableWords)
      (hb : b ∈ fields (s.regs 0) ++ [s.regs 4-(4#32),s.regs 4-(8#32)]) :=
    load_store_apart m b a v (h.tableSafe a ha b hb)
  have stackLoad (m : Memory) (a b v : Word)
      (ha : a ∈ [s.regs 4,s.regs 4-(4#32),s.regs 4-(8#32)]) (hb : b ∈ fields (s.regs 0)) :=
    load_store_apart m b a v (h.stackSafe a ha b hb)
  have st := stack_apart (s.regs 4)
  have ti := tics_apart (s.regs 0)
  have addback : s.regs 4-(8#32)+(4#32) = s.regs 4-(4#32) := by bv_decide
  let c0 := (bodyEnd s).core
  let c1 : X86Memory.State := put c0 0 1
  let c2 : X86Memory.State := put (put c1 4 (s.regs 4-4)) 6 (s.regs 6)
  let c3 : X86Memory.State := put (put c2 4 (s.regs 4)) 3 (s.regs 3)
  let c4 : X86Memory.State := put c3 4 (s.regs 4+4)
  have path : X86Routine.Prefix program [0x3325e] 4 (bodyEnd s) ⟨c4,some (logical32 4),0x3325e⟩ := by
    apply X86Routine.Prefix.step (middle := ⟨c1,some (logical32 4),0x30ef8⟩)
      (by change ¬((0x30ef3:Nat) ∈ [0x3325e]); decide)
      (show program 0x30ef3 = some (.immediate 0 1,5) from by decide) (by
        simp [active_83,active_88,active_89,active_90,at_30ea0,at_30ea1,at_30ea2,at_30ea4,at_30ea6,at_30ebb,at_30ebe,at_30ec4,at_30ec7,at_30eca,at_30ecd,at_30ecf,at_30ed2,at_30ed5,at_30ed8,at_30edc,at_30ee3,at_30ee6,at_30ee9,at_30eeb,at_30ef3,at_30ef8,at_30ef9,at_30efa,callee,X86Routine.execute,X86Control.execute,X86Block.execute,
    X86Memory.execute,X86Block.Address.eval,X86Routine.pushWord,put,write,
    blockPreservesFlags,logical32,compare32,h.state,BitVec.sub_sub,addback,BitVec.sub_add_cancel,tableLoad,stackLoad,
    fields,tableWords,load_store_apart _ _ _ _ st.1,load_store_apart _ _ _ _ st.2.1,
    load_store_apart _ _ _ _ st.2.2,load_store_apart _ _ _ _ ti.1,
    load_store_apart _ _ _ _ ti.2,load_store,h.table.sprite,h.table.frame,h.table.tics,
    h.table.action,h.table.next,h.returnAddress,bodyEnd,setterEnd,entryMemory,savedMemory,eax,c1,c0])
    apply X86Routine.Prefix.step (middle := ⟨c2,some (logical32 4),0x30ef9⟩)
      (by change ¬((0x30ef8:Nat) ∈ [0x3325e]); decide)
      (show program 0x30ef8 = some (.pop 6,1) from by decide) (by
        simp [active_83,active_88,active_89,active_90,at_30ea0,at_30ea1,at_30ea2,at_30ea4,at_30ea6,at_30ebb,at_30ebe,at_30ec4,at_30ec7,at_30eca,at_30ecd,at_30ecf,at_30ed2,at_30ed5,at_30ed8,at_30edc,at_30ee3,at_30ee6,at_30ee9,at_30eeb,at_30ef3,at_30ef8,at_30ef9,at_30efa,callee,X86Routine.execute,X86Control.execute,X86Block.execute,
    X86Memory.execute,X86Block.Address.eval,X86Routine.pushWord,put,write,
    blockPreservesFlags,logical32,compare32,h.state,BitVec.sub_sub,addback,BitVec.sub_add_cancel,tableLoad,stackLoad,
    fields,tableWords,load_store_apart _ _ _ _ st.1,load_store_apart _ _ _ _ st.2.1,
    load_store_apart _ _ _ _ st.2.2,load_store_apart _ _ _ _ ti.1,
    load_store_apart _ _ _ _ ti.2,load_store,h.table.sprite,h.table.frame,h.table.tics,
    h.table.action,h.table.next,h.returnAddress,bodyEnd,setterEnd,entryMemory,savedMemory,eax,c2,c1,c0])
    apply X86Routine.Prefix.step (middle := ⟨c3,some (logical32 4),0x30efa⟩)
      (by change ¬((0x30ef9:Nat) ∈ [0x3325e]); decide)
      (show program 0x30ef9 = some (.pop 3,1) from by decide) (by
        simp [active_83,active_88,active_89,active_90,at_30ea0,at_30ea1,at_30ea2,at_30ea4,at_30ea6,at_30ebb,at_30ebe,at_30ec4,at_30ec7,at_30eca,at_30ecd,at_30ecf,at_30ed2,at_30ed5,at_30ed8,at_30edc,at_30ee3,at_30ee6,at_30ee9,at_30eeb,at_30ef3,at_30ef8,at_30ef9,at_30efa,callee,X86Routine.execute,X86Control.execute,X86Block.execute,
    X86Memory.execute,X86Block.Address.eval,X86Routine.pushWord,put,write,
    blockPreservesFlags,logical32,compare32,h.state,BitVec.sub_sub,addback,BitVec.sub_add_cancel,tableLoad,stackLoad,
    fields,tableWords,load_store_apart _ _ _ _ st.1,load_store_apart _ _ _ _ st.2.1,
    load_store_apart _ _ _ _ st.2.2,load_store_apart _ _ _ _ ti.1,
    load_store_apart _ _ _ _ ti.2,load_store,h.table.sprite,h.table.frame,h.table.tics,
    h.table.action,h.table.next,h.returnAddress,bodyEnd,setterEnd,entryMemory,savedMemory,eax,c3,c2,c1,c0])
    apply X86Routine.Prefix.step (middle := ⟨c4,some (logical32 4),0x3325e⟩)
      (by change ¬((0x30efa:Nat) ∈ [0x3325e]); decide)
      (show program 0x30efa = some (.ret,1) from by decide) (by
        simp [active_83,active_88,active_89,active_90,at_30ea0,at_30ea1,at_30ea2,at_30ea4,at_30ea6,at_30ebb,at_30ebe,at_30ec4,at_30ec7,at_30eca,at_30ecd,at_30ecf,at_30ed2,at_30ed5,at_30ed8,at_30edc,at_30ee3,at_30ee6,at_30ee9,at_30eeb,at_30ef3,at_30ef8,at_30ef9,at_30efa,callee,X86Routine.execute,X86Control.execute,X86Block.execute,
    X86Memory.execute,X86Block.Address.eval,X86Routine.pushWord,put,write,
    blockPreservesFlags,logical32,compare32,h.state,BitVec.sub_sub,addback,BitVec.sub_add_cancel,tableLoad,stackLoad,
    fields,tableWords,load_store_apart _ _ _ _ st.1,load_store_apart _ _ _ _ st.2.1,
    load_store_apart _ _ _ _ st.2.2,load_store_apart _ _ _ _ ti.1,
    load_store_apart _ _ _ _ ti.2,load_store,h.table.sprite,h.table.frame,h.table.tics,
    h.table.action,h.table.next,h.returnAddress,bodyEnd,setterEnd,entryMemory,savedMemory,eax,c4,c3,c2,c1,c0])
    exact X86Routine.Prefix.nil _
  rw [show 4 = 4+0 from rfl,path.run 0]
  simp [X86Routine.run,setterEnd,bodyEnd,put,write,c4,c3,c2,c1,c0]
  funext r
  by_cases h0 : r = 0 <;> by_cases h2 : r = 2 <;> by_cases h3 : r = 3 <;>
    by_cases h4 : r = 4 <;> by_cases h6 : r = 6 <;> simp_all [write]

theorem exit_active (pc : Nat) (h : program pc ≠ none) : pc ∉ [0x3325e] := by
  simp only [List.mem_singleton]
  intro eq; subst pc
  exact h (by rfl)

theorem setter_program (s : X86Memory.State) (flags : Option Flags) (h : SetterInputs s) :
    X86Routine.run program [0x3325e] 24 ⟨s,flags,0x30ea0⟩ = some (setterEnd s) := by
  obtain ⟨k,hk,p,_⟩ := X86Routine.run_path (setter_prologue s flags h.state)
  obtain ⟨j,hj,q,_⟩ := X86Routine.run_path (setter_body s h)
  have p := p.transfer program [0x3325e] (fun _ _ => rfl) exit_active
  have q := q.transfer program [0x3325e] (fun _ _ => rfl) exit_active
  have tail := q.finish (setter_epilogue s h) 19 (by omega)
  exact p.finish tail 24 (by omega)

def object (s : X86Memory.State) : Word := load32 s.memory (s.regs 1)
def moving (s : X86Memory.State) : Prop := s.memory (s.regs 6) ≠ (0#8) ∨ s.memory (s.regs 6+(1#32)) ≠ (0#8)
instance (s : X86Memory.State) : Decidable (moving s) := inferInstanceAs (Decidable (_ ∨ _))
def standing (s : X86Memory.State) : Prop := load32 s.memory (object s+(100#32)) = 0x16a74
instance (s : X86Memory.State) : Decidable (standing s) := inferInstanceAs (Decidable (_ = _))

def callCore (s : X86Memory.State) : X86Memory.State :=
  X86Routine.pushWord (put (put s 0 (object s)) 2 150) 0x3325e

structure Inputs (s : X86Memory.State) : Prop where
  table : RunTable s.memory
  tableSafe : ∀ a, a ∈ tableWords → ∀ b,
    b ∈ fields (object s) ++ [s.regs 4-(4#32),s.regs 4-(8#32),s.regs 4-(12#32)] → Apart a b
  stackSafe : ∀ a, a ∈ [s.regs 4-(4#32),s.regs 4-(8#32),s.regs 4-(12#32)] →
    ∀ b, b ∈ fields (object s) → Apart a b

theorem call_establishes_setter (s : X86Memory.State) (h : Inputs s) : SetterInputs (callCore s) := by
  have keep (a : Word) (ha : a ∈ tableWords) :
      load32 (callCore s).memory a = load32 s.memory a := by
    change load32 (store32 s.memory (s.regs 4-(4#32)) (0x3325e#32)) a = _
    exact load_store_apart _ _ _ _ (h.tableSafe a ha _ (by simp))
  constructor
  · simp [callCore,X86Routine.pushWord,put,write]
  · constructor
    · rw [keep _ (by simp [tableWords])]; exact h.table.sprite
    · rw [keep _ (by simp [tableWords])]; exact h.table.frame
    · rw [keep _ (by simp [tableWords])]; exact h.table.tics
    · rw [keep _ (by simp [tableWords])]; exact h.table.action
    · rw [keep _ (by simp [tableWords])]; exact h.table.next
  · simp [callCore,X86Routine.pushWord,put,write,load_store]
  · intro a ha b hb
    apply h.tableSafe a ha b
    simp [callCore,X86Routine.pushWord,put,write,BitVec.sub_sub] at hb ⊢
    rcases hb with hb | hb | hb <;> simp_all
  · intro a ha b hb
    apply h.stackSafe a
    · simpa [callCore,X86Routine.pushWord,put,write,BitVec.sub_sub] using ha
    · simpa [callCore,X86Routine.pushWord,put,write] using hb

private theorem caller_at_0 : program 0x3323e = caller 0 := by decide
private theorem caller_at_3 : program 0x33241 = caller 3 := by decide
private theorem caller_at_5 : program 0x33243 = caller 5 := by decide
private theorem caller_at_9 : program 0x33247 = caller 9 := by decide
private theorem caller_at_11 : program 0x33249 = caller 11 := by decide
private theorem caller_at_13 : program 0x3324b = caller 13 := by decide
private theorem caller_at_20 : program 0x33252 = caller 20 := by decide
private theorem caller_at_22 : program 0x33254 = caller 22 := by decide
private theorem caller_at_27 : program 0x33259 = caller 27 := by decide

def selectedEnd (s : X86Memory.State) : X86Control.State :=
  if moving s then
    if standing s then ⟨callCore s,some (compare32 0x16a74 0x16a74),0x30ea0⟩
    else ⟨put s 0 (object s),some (compare32 (load32 s.memory (object s+(100#32))) 0x16a74),0x3325e⟩
  else ⟨s,some (X86Routine.compare8 0 0),0x3325e⟩

theorem selector_program (s : X86Memory.State) (flags : Option Flags) :
    X86Routine.run program [0x30ea0,0x3325e] 9 ⟨s,flags,0x3323e⟩ = some (selectedEnd s) := by
  by_cases hf : s.memory (s.regs 6) = (0#8) <;>
    by_cases hs : s.memory (s.regs 6+(1#32)) = (0#8) <;>
    by_cases hp : load32 s.memory (object s+(100#32)) = (0x16a74#32)
  · have hp' := hp
    dsimp only [object] at hp'
    have path : X86Routine.Prefix program [0x30ea0,0x3325e] 4 ⟨s,flags,0x3323e⟩
        ⟨s,some (X86Routine.compare8 0 0),0x3325e⟩ := by
      apply X86Routine.Prefix.step (middle := ⟨s,some (X86Routine.compare8 0 0),0x33241⟩)
        (by change ¬((0x3323e:Nat) ∈ [0x30ea0,0x3325e]); decide)
        (show program 0x3323e = some (.compareByte ⟨some 6,none,0,0⟩ 0,3) from by decide) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,
            X86Routine.compare8,cmp32_zero,callCore,object,hf,hs,hp'])
      apply X86Routine.Prefix.step (middle := ⟨s,some (X86Routine.compare8 0 0),0x33243⟩)
        (by change ¬((0x33241:Nat) ∈ [0x30ea0,0x3325e]); decide)
        (show program 0x33241 = some (.control (.jumpZero false 6),2) from by decide) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,
            X86Routine.compare8,cmp32_zero,callCore,object,hf,hs,hp'])
      apply X86Routine.Prefix.step (middle := ⟨s,some (X86Routine.compare8 0 0),0x33247⟩)
        (by change ¬((0x33243:Nat) ∈ [0x30ea0,0x3325e]); decide)
        (show program 0x33243 = some (.compareByte ⟨some 6,none,0,1⟩ 0,4) from by decide) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,
            X86Routine.compare8,cmp32_zero,callCore,object,hf,hs,hp'])
      apply X86Routine.Prefix.step (middle := ⟨s,some (X86Routine.compare8 0 0),0x3325e⟩)
        (by change ¬((0x33247:Nat) ∈ [0x30ea0,0x3325e]); decide)
        (show program 0x33247 = some (.control (.jumpZero true 21),2) from by decide) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,
            X86Routine.compare8,cmp32_zero,callCore,object,hf,hs,hp'])
      exact X86Routine.Prefix.nil _
    have finish := path.finish (show X86Routine.run program [0x30ea0,0x3325e] 0
        ⟨s,some (X86Routine.compare8 0 0),0x3325e⟩ = some ⟨s,some (X86Routine.compare8 0 0),0x3325e⟩ from by simp [X86Routine.run]) 9 (by omega)
    simpa [selectedEnd,moving,standing,hf,hs,hp] using finish
  · have hp' := hp
    dsimp only [object] at hp'
    have path : X86Routine.Prefix program [0x30ea0,0x3325e] 4 ⟨s,flags,0x3323e⟩
        ⟨s,some (X86Routine.compare8 0 0),0x3325e⟩ := by
      apply X86Routine.Prefix.step (middle := ⟨s,some (X86Routine.compare8 0 0),0x33241⟩)
        (by change ¬((0x3323e:Nat) ∈ [0x30ea0,0x3325e]); decide)
        (show program 0x3323e = some (.compareByte ⟨some 6,none,0,0⟩ 0,3) from by decide) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,
            X86Routine.compare8,cmp32_zero,callCore,object,hf,hs,hp'])
      apply X86Routine.Prefix.step (middle := ⟨s,some (X86Routine.compare8 0 0),0x33243⟩)
        (by change ¬((0x33241:Nat) ∈ [0x30ea0,0x3325e]); decide)
        (show program 0x33241 = some (.control (.jumpZero false 6),2) from by decide) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,
            X86Routine.compare8,cmp32_zero,callCore,object,hf,hs,hp'])
      apply X86Routine.Prefix.step (middle := ⟨s,some (X86Routine.compare8 0 0),0x33247⟩)
        (by change ¬((0x33243:Nat) ∈ [0x30ea0,0x3325e]); decide)
        (show program 0x33243 = some (.compareByte ⟨some 6,none,0,1⟩ 0,4) from by decide) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,
            X86Routine.compare8,cmp32_zero,callCore,object,hf,hs,hp'])
      apply X86Routine.Prefix.step (middle := ⟨s,some (X86Routine.compare8 0 0),0x3325e⟩)
        (by change ¬((0x33247:Nat) ∈ [0x30ea0,0x3325e]); decide)
        (show program 0x33247 = some (.control (.jumpZero true 21),2) from by decide) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,
            X86Routine.compare8,cmp32_zero,callCore,object,hf,hs,hp'])
      exact X86Routine.Prefix.nil _
    have finish := path.finish (show X86Routine.run program [0x30ea0,0x3325e] 0
        ⟨s,some (X86Routine.compare8 0 0),0x3325e⟩ = some ⟨s,some (X86Routine.compare8 0 0),0x3325e⟩ from by simp [X86Routine.run]) 9 (by omega)
    simpa [selectedEnd,moving,standing,hf,hs,hp] using finish
  · have hp' := hp
    dsimp only [object] at hp'
    have path : X86Routine.Prefix program [0x30ea0,0x3325e] 9 ⟨s,flags,0x3323e⟩
        ⟨callCore s,some (compare32 0x16a74 0x16a74),0x30ea0⟩ := by
      apply X86Routine.Prefix.step (middle := ⟨s,some (X86Routine.compare8 0 0),0x33241⟩)
        (by change ¬((0x3323e:Nat) ∈ [0x30ea0,0x3325e]); decide)
        (show program 0x3323e = some (.compareByte ⟨some 6,none,0,0⟩ 0,3) from by decide) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,
            X86Routine.compare8,cmp32_zero,callCore,object,hf,hs,hp'])
      apply X86Routine.Prefix.step (middle := ⟨s,some (X86Routine.compare8 0 0),0x33243⟩)
        (by change ¬((0x33241:Nat) ∈ [0x30ea0,0x3325e]); decide)
        (show program 0x33241 = some (.control (.jumpZero false 6),2) from by decide) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,
            X86Routine.compare8,cmp32_zero,callCore,object,hf,hs,hp'])
      apply X86Routine.Prefix.step (middle := ⟨s,some (X86Routine.compare8 (s.memory (s.regs 6+1)) 0),0x33247⟩)
        (by change ¬((0x33243:Nat) ∈ [0x30ea0,0x3325e]); decide)
        (show program 0x33243 = some (.compareByte ⟨some 6,none,0,1⟩ 0,4) from by decide) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,
            X86Routine.compare8,cmp32_zero,callCore,object,hf,hs,hp'])
      apply X86Routine.Prefix.step (middle := ⟨s,some (X86Routine.compare8 (s.memory (s.regs 6+1)) 0),0x33249⟩)
        (by change ¬((0x33247:Nat) ∈ [0x30ea0,0x3325e]); decide)
        (show program 0x33247 = some (.control (.jumpZero true 21),2) from by decide) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,
            X86Routine.compare8,cmp32_zero,callCore,object,hf,hs,hp'])
      apply X86Routine.Prefix.step (middle := ⟨put s 0 (object s),some (X86Routine.compare8 (s.memory (s.regs 6+1)) 0),0x3324b⟩)
        (by change ¬((0x33249:Nat) ∈ [0x30ea0,0x3325e]); decide)
        (show program 0x33249 = some (.control (.block (.legacy (.load 0 1 0))),2) from by decide) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,
            X86Routine.compare8,cmp32_zero,callCore,object,hf,hs,hp'])
      apply X86Routine.Prefix.step (middle := ⟨put s 0 (object s),some (compare32 0x16a74 0x16a74),0x33252⟩)
        (by change ¬((0x3324b:Nat) ∈ [0x30ea0,0x3325e]); decide)
        (show program 0x3324b = some (.control (.cmpImmediate ⟨some 0,none,0,100⟩ 0x16a74),7) from by decide) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,
            X86Routine.compare8,cmp32_zero,callCore,object,hf,hs,hp'])
      apply X86Routine.Prefix.step (middle := ⟨put s 0 (object s),some (compare32 0x16a74 0x16a74),0x33254⟩)
        (by change ¬((0x33252:Nat) ∈ [0x30ea0,0x3325e]); decide)
        (show program 0x33252 = some (.control (.jumpZero false 10),2) from by decide) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,
            X86Routine.compare8,cmp32_zero,callCore,object,hf,hs,hp'])
      apply X86Routine.Prefix.step (middle := ⟨put (put s 0 (object s)) 2 150,some (compare32 0x16a74 0x16a74),0x33259⟩)
        (by change ¬((0x33254:Nat) ∈ [0x30ea0,0x3325e]); decide)
        (show program 0x33254 = some (.immediate 2 150,5) from by decide) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,
            X86Routine.compare8,cmp32_zero,callCore,object,hf,hs,hp'])
      apply X86Routine.Prefix.step (middle := ⟨callCore s,some (compare32 0x16a74 0x16a74),0x30ea0⟩)
        (by change ¬((0x33259:Nat) ∈ [0x30ea0,0x3325e]); decide)
        (show program 0x33259 = some (.call (-9150),5) from by decide) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,
            X86Routine.compare8,cmp32_zero,callCore,object,hf,hs,hp'])
      exact X86Routine.Prefix.nil _
    have finish := path.finish (show X86Routine.run program [0x30ea0,0x3325e] 0
        ⟨callCore s,some (compare32 0x16a74 0x16a74),0x30ea0⟩ = some ⟨callCore s,some (compare32 0x16a74 0x16a74),0x30ea0⟩ from by simp [X86Routine.run]) 9 (by omega)
    simpa [selectedEnd,moving,standing,hf,hs,hp] using finish
  · have hp' := hp
    dsimp only [object] at hp'
    have path : X86Routine.Prefix program [0x30ea0,0x3325e] 7 ⟨s,flags,0x3323e⟩
        ⟨put s 0 (object s),some (compare32 (load32 s.memory (object s+100)) 0x16a74),0x3325e⟩ := by
      apply X86Routine.Prefix.step (middle := ⟨s,some (X86Routine.compare8 0 0),0x33241⟩)
        (by change ¬((0x3323e:Nat) ∈ [0x30ea0,0x3325e]); decide)
        (show program 0x3323e = some (.compareByte ⟨some 6,none,0,0⟩ 0,3) from by decide) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,
            X86Routine.compare8,cmp32_zero,callCore,object,hf,hs,hp'])
      apply X86Routine.Prefix.step (middle := ⟨s,some (X86Routine.compare8 0 0),0x33243⟩)
        (by change ¬((0x33241:Nat) ∈ [0x30ea0,0x3325e]); decide)
        (show program 0x33241 = some (.control (.jumpZero false 6),2) from by decide) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,
            X86Routine.compare8,cmp32_zero,callCore,object,hf,hs,hp'])
      apply X86Routine.Prefix.step (middle := ⟨s,some (X86Routine.compare8 (s.memory (s.regs 6+1)) 0),0x33247⟩)
        (by change ¬((0x33243:Nat) ∈ [0x30ea0,0x3325e]); decide)
        (show program 0x33243 = some (.compareByte ⟨some 6,none,0,1⟩ 0,4) from by decide) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,
            X86Routine.compare8,cmp32_zero,callCore,object,hf,hs,hp'])
      apply X86Routine.Prefix.step (middle := ⟨s,some (X86Routine.compare8 (s.memory (s.regs 6+1)) 0),0x33249⟩)
        (by change ¬((0x33247:Nat) ∈ [0x30ea0,0x3325e]); decide)
        (show program 0x33247 = some (.control (.jumpZero true 21),2) from by decide) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,
            X86Routine.compare8,cmp32_zero,callCore,object,hf,hs,hp'])
      apply X86Routine.Prefix.step (middle := ⟨put s 0 (object s),some (X86Routine.compare8 (s.memory (s.regs 6+1)) 0),0x3324b⟩)
        (by change ¬((0x33249:Nat) ∈ [0x30ea0,0x3325e]); decide)
        (show program 0x33249 = some (.control (.block (.legacy (.load 0 1 0))),2) from by decide) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,
            X86Routine.compare8,cmp32_zero,callCore,object,hf,hs,hp'])
      apply X86Routine.Prefix.step (middle := ⟨put s 0 (object s),some (compare32 (load32 s.memory (object s+100)) 0x16a74),0x33252⟩)
        (by change ¬((0x3324b:Nat) ∈ [0x30ea0,0x3325e]); decide)
        (show program 0x3324b = some (.control (.cmpImmediate ⟨some 0,none,0,100⟩ 0x16a74),7) from by decide) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,
            X86Routine.compare8,cmp32_zero,callCore,object,hf,hs,hp'])
      apply X86Routine.Prefix.step (middle := ⟨put s 0 (object s),some (compare32 (load32 s.memory (object s+100)) 0x16a74),0x3325e⟩)
        (by change ¬((0x33252:Nat) ∈ [0x30ea0,0x3325e]); decide)
        (show program 0x33252 = some (.control (.jumpZero false 10),2) from by decide) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,
            X86Routine.compare8,cmp32_zero,callCore,object,hf,hs,hp'])
      exact X86Routine.Prefix.nil _
    have finish := path.finish (show X86Routine.run program [0x30ea0,0x3325e] 0
        ⟨put s 0 (object s),some (compare32 (load32 s.memory (object s+100)) 0x16a74),0x3325e⟩ = some ⟨put s 0 (object s),some (compare32 (load32 s.memory (object s+100)) 0x16a74),0x3325e⟩ from by simp [X86Routine.run]) 9 (by omega)
    simpa [selectedEnd,moving,standing,hf,hs,hp] using finish
  · have hp' := hp
    dsimp only [object] at hp'
    have path : X86Routine.Prefix program [0x30ea0,0x3325e] 7 ⟨s,flags,0x3323e⟩
        ⟨callCore s,some (compare32 0x16a74 0x16a74),0x30ea0⟩ := by
      apply X86Routine.Prefix.step (middle := ⟨s,some (X86Routine.compare8 (s.memory (s.regs 6)) 0),0x33241⟩)
        (by change ¬((0x3323e:Nat) ∈ [0x30ea0,0x3325e]); decide)
        (show program 0x3323e = some (.compareByte ⟨some 6,none,0,0⟩ 0,3) from by decide) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,
            X86Routine.compare8,cmp32_zero,callCore,object,hf,hs,hp'])
      apply X86Routine.Prefix.step (middle := ⟨s,some (X86Routine.compare8 (s.memory (s.regs 6)) 0),0x33249⟩)
        (by change ¬((0x33241:Nat) ∈ [0x30ea0,0x3325e]); decide)
        (show program 0x33241 = some (.control (.jumpZero false 6),2) from by decide) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,
            X86Routine.compare8,cmp32_zero,callCore,object,hf,hs,hp'])
      apply X86Routine.Prefix.step (middle := ⟨put s 0 (object s),some (X86Routine.compare8 (s.memory (s.regs 6)) 0),0x3324b⟩)
        (by change ¬((0x33249:Nat) ∈ [0x30ea0,0x3325e]); decide)
        (show program 0x33249 = some (.control (.block (.legacy (.load 0 1 0))),2) from by decide) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,
            X86Routine.compare8,cmp32_zero,callCore,object,hf,hs,hp'])
      apply X86Routine.Prefix.step (middle := ⟨put s 0 (object s),some (compare32 0x16a74 0x16a74),0x33252⟩)
        (by change ¬((0x3324b:Nat) ∈ [0x30ea0,0x3325e]); decide)
        (show program 0x3324b = some (.control (.cmpImmediate ⟨some 0,none,0,100⟩ 0x16a74),7) from by decide) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,
            X86Routine.compare8,cmp32_zero,callCore,object,hf,hs,hp'])
      apply X86Routine.Prefix.step (middle := ⟨put s 0 (object s),some (compare32 0x16a74 0x16a74),0x33254⟩)
        (by change ¬((0x33252:Nat) ∈ [0x30ea0,0x3325e]); decide)
        (show program 0x33252 = some (.control (.jumpZero false 10),2) from by decide) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,
            X86Routine.compare8,cmp32_zero,callCore,object,hf,hs,hp'])
      apply X86Routine.Prefix.step (middle := ⟨put (put s 0 (object s)) 2 150,some (compare32 0x16a74 0x16a74),0x33259⟩)
        (by change ¬((0x33254:Nat) ∈ [0x30ea0,0x3325e]); decide)
        (show program 0x33254 = some (.immediate 2 150,5) from by decide) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,
            X86Routine.compare8,cmp32_zero,callCore,object,hf,hs,hp'])
      apply X86Routine.Prefix.step (middle := ⟨callCore s,some (compare32 0x16a74 0x16a74),0x30ea0⟩)
        (by change ¬((0x33259:Nat) ∈ [0x30ea0,0x3325e]); decide)
        (show program 0x33259 = some (.call (-9150),5) from by decide) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,
            X86Routine.compare8,cmp32_zero,callCore,object,hf,hs,hp'])
      exact X86Routine.Prefix.nil _
    have finish := path.finish (show X86Routine.run program [0x30ea0,0x3325e] 0
        ⟨callCore s,some (compare32 0x16a74 0x16a74),0x30ea0⟩ = some ⟨callCore s,some (compare32 0x16a74 0x16a74),0x30ea0⟩ from by simp [X86Routine.run]) 9 (by omega)
    simpa [selectedEnd,moving,standing,hf,hs,hp] using finish
  · have hp' := hp
    dsimp only [object] at hp'
    have path : X86Routine.Prefix program [0x30ea0,0x3325e] 5 ⟨s,flags,0x3323e⟩
        ⟨put s 0 (object s),some (compare32 (load32 s.memory (object s+100)) 0x16a74),0x3325e⟩ := by
      apply X86Routine.Prefix.step (middle := ⟨s,some (X86Routine.compare8 (s.memory (s.regs 6)) 0),0x33241⟩)
        (by change ¬((0x3323e:Nat) ∈ [0x30ea0,0x3325e]); decide)
        (show program 0x3323e = some (.compareByte ⟨some 6,none,0,0⟩ 0,3) from by decide) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,
            X86Routine.compare8,cmp32_zero,callCore,object,hf,hs,hp'])
      apply X86Routine.Prefix.step (middle := ⟨s,some (X86Routine.compare8 (s.memory (s.regs 6)) 0),0x33249⟩)
        (by change ¬((0x33241:Nat) ∈ [0x30ea0,0x3325e]); decide)
        (show program 0x33241 = some (.control (.jumpZero false 6),2) from by decide) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,
            X86Routine.compare8,cmp32_zero,callCore,object,hf,hs,hp'])
      apply X86Routine.Prefix.step (middle := ⟨put s 0 (object s),some (X86Routine.compare8 (s.memory (s.regs 6)) 0),0x3324b⟩)
        (by change ¬((0x33249:Nat) ∈ [0x30ea0,0x3325e]); decide)
        (show program 0x33249 = some (.control (.block (.legacy (.load 0 1 0))),2) from by decide) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,
            X86Routine.compare8,cmp32_zero,callCore,object,hf,hs,hp'])
      apply X86Routine.Prefix.step (middle := ⟨put s 0 (object s),some (compare32 (load32 s.memory (object s+100)) 0x16a74),0x33252⟩)
        (by change ¬((0x3324b:Nat) ∈ [0x30ea0,0x3325e]); decide)
        (show program 0x3324b = some (.control (.cmpImmediate ⟨some 0,none,0,100⟩ 0x16a74),7) from by decide) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,
            X86Routine.compare8,cmp32_zero,callCore,object,hf,hs,hp'])
      apply X86Routine.Prefix.step (middle := ⟨put s 0 (object s),some (compare32 (load32 s.memory (object s+100)) 0x16a74),0x3325e⟩)
        (by change ¬((0x33252:Nat) ∈ [0x30ea0,0x3325e]); decide)
        (show program 0x33252 = some (.control (.jumpZero false 10),2) from by decide) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,
            X86Routine.compare8,cmp32_zero,callCore,object,hf,hs,hp'])
      exact X86Routine.Prefix.nil _
    have finish := path.finish (show X86Routine.run program [0x30ea0,0x3325e] 0
        ⟨put s 0 (object s),some (compare32 (load32 s.memory (object s+100)) 0x16a74),0x3325e⟩ = some ⟨put s 0 (object s),some (compare32 (load32 s.memory (object s+100)) 0x16a74),0x3325e⟩ from by simp [X86Routine.run]) 9 (by omega)
    simpa [selectedEnd,moving,standing,hf,hs,hp] using finish
  · have hp' := hp
    dsimp only [object] at hp'
    have path : X86Routine.Prefix program [0x30ea0,0x3325e] 7 ⟨s,flags,0x3323e⟩
        ⟨callCore s,some (compare32 0x16a74 0x16a74),0x30ea0⟩ := by
      apply X86Routine.Prefix.step (middle := ⟨s,some (X86Routine.compare8 (s.memory (s.regs 6)) 0),0x33241⟩)
        (by change ¬((0x3323e:Nat) ∈ [0x30ea0,0x3325e]); decide)
        (show program 0x3323e = some (.compareByte ⟨some 6,none,0,0⟩ 0,3) from by decide) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,
            X86Routine.compare8,cmp32_zero,callCore,object,hf,hs,hp'])
      apply X86Routine.Prefix.step (middle := ⟨s,some (X86Routine.compare8 (s.memory (s.regs 6)) 0),0x33249⟩)
        (by change ¬((0x33241:Nat) ∈ [0x30ea0,0x3325e]); decide)
        (show program 0x33241 = some (.control (.jumpZero false 6),2) from by decide) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,
            X86Routine.compare8,cmp32_zero,callCore,object,hf,hs,hp'])
      apply X86Routine.Prefix.step (middle := ⟨put s 0 (object s),some (X86Routine.compare8 (s.memory (s.regs 6)) 0),0x3324b⟩)
        (by change ¬((0x33249:Nat) ∈ [0x30ea0,0x3325e]); decide)
        (show program 0x33249 = some (.control (.block (.legacy (.load 0 1 0))),2) from by decide) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,
            X86Routine.compare8,cmp32_zero,callCore,object,hf,hs,hp'])
      apply X86Routine.Prefix.step (middle := ⟨put s 0 (object s),some (compare32 0x16a74 0x16a74),0x33252⟩)
        (by change ¬((0x3324b:Nat) ∈ [0x30ea0,0x3325e]); decide)
        (show program 0x3324b = some (.control (.cmpImmediate ⟨some 0,none,0,100⟩ 0x16a74),7) from by decide) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,
            X86Routine.compare8,cmp32_zero,callCore,object,hf,hs,hp'])
      apply X86Routine.Prefix.step (middle := ⟨put s 0 (object s),some (compare32 0x16a74 0x16a74),0x33254⟩)
        (by change ¬((0x33252:Nat) ∈ [0x30ea0,0x3325e]); decide)
        (show program 0x33252 = some (.control (.jumpZero false 10),2) from by decide) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,
            X86Routine.compare8,cmp32_zero,callCore,object,hf,hs,hp'])
      apply X86Routine.Prefix.step (middle := ⟨put (put s 0 (object s)) 2 150,some (compare32 0x16a74 0x16a74),0x33259⟩)
        (by change ¬((0x33254:Nat) ∈ [0x30ea0,0x3325e]); decide)
        (show program 0x33254 = some (.immediate 2 150,5) from by decide) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,
            X86Routine.compare8,cmp32_zero,callCore,object,hf,hs,hp'])
      apply X86Routine.Prefix.step (middle := ⟨callCore s,some (compare32 0x16a74 0x16a74),0x30ea0⟩)
        (by change ¬((0x33259:Nat) ∈ [0x30ea0,0x3325e]); decide)
        (show program 0x33259 = some (.call (-9150),5) from by decide) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,
            X86Routine.compare8,cmp32_zero,callCore,object,hf,hs,hp'])
      exact X86Routine.Prefix.nil _
    have finish := path.finish (show X86Routine.run program [0x30ea0,0x3325e] 0
        ⟨callCore s,some (compare32 0x16a74 0x16a74),0x30ea0⟩ = some ⟨callCore s,some (compare32 0x16a74 0x16a74),0x30ea0⟩ from by simp [X86Routine.run]) 9 (by omega)
    simpa [selectedEnd,moving,standing,hf,hs,hp] using finish
  · have hp' := hp
    dsimp only [object] at hp'
    have path : X86Routine.Prefix program [0x30ea0,0x3325e] 5 ⟨s,flags,0x3323e⟩
        ⟨put s 0 (object s),some (compare32 (load32 s.memory (object s+100)) 0x16a74),0x3325e⟩ := by
      apply X86Routine.Prefix.step (middle := ⟨s,some (X86Routine.compare8 (s.memory (s.regs 6)) 0),0x33241⟩)
        (by change ¬((0x3323e:Nat) ∈ [0x30ea0,0x3325e]); decide)
        (show program 0x3323e = some (.compareByte ⟨some 6,none,0,0⟩ 0,3) from by decide) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,
            X86Routine.compare8,cmp32_zero,callCore,object,hf,hs,hp'])
      apply X86Routine.Prefix.step (middle := ⟨s,some (X86Routine.compare8 (s.memory (s.regs 6)) 0),0x33249⟩)
        (by change ¬((0x33241:Nat) ∈ [0x30ea0,0x3325e]); decide)
        (show program 0x33241 = some (.control (.jumpZero false 6),2) from by decide) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,
            X86Routine.compare8,cmp32_zero,callCore,object,hf,hs,hp'])
      apply X86Routine.Prefix.step (middle := ⟨put s 0 (object s),some (X86Routine.compare8 (s.memory (s.regs 6)) 0),0x3324b⟩)
        (by change ¬((0x33249:Nat) ∈ [0x30ea0,0x3325e]); decide)
        (show program 0x33249 = some (.control (.block (.legacy (.load 0 1 0))),2) from by decide) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,
            X86Routine.compare8,cmp32_zero,callCore,object,hf,hs,hp'])
      apply X86Routine.Prefix.step (middle := ⟨put s 0 (object s),some (compare32 (load32 s.memory (object s+100)) 0x16a74),0x33252⟩)
        (by change ¬((0x3324b:Nat) ∈ [0x30ea0,0x3325e]); decide)
        (show program 0x3324b = some (.control (.cmpImmediate ⟨some 0,none,0,100⟩ 0x16a74),7) from by decide) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,
            X86Routine.compare8,cmp32_zero,callCore,object,hf,hs,hp'])
      apply X86Routine.Prefix.step (middle := ⟨put s 0 (object s),some (compare32 (load32 s.memory (object s+100)) 0x16a74),0x3325e⟩)
        (by change ¬((0x33252:Nat) ∈ [0x30ea0,0x3325e]); decide)
        (show program 0x33252 = some (.control (.jumpZero false 10),2) from by decide) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,
            X86Routine.compare8,cmp32_zero,callCore,object,hf,hs,hp'])
      exact X86Routine.Prefix.nil _
    have finish := path.finish (show X86Routine.run program [0x30ea0,0x3325e] 0
        ⟨put s 0 (object s),some (compare32 (load32 s.memory (object s+100)) 0x16a74),0x3325e⟩ = some ⟨put s 0 (object s),some (compare32 (load32 s.memory (object s+100)) 0x16a74),0x3325e⟩ from by simp [X86Routine.run]) 9 (by omega)
    simpa [selectedEnd,moving,standing,hf,hs,hp] using finish


def result (s : X86Memory.State) : X86Control.State :=
  if moving s ∧ standing s then setterEnd (callCore s) else selectedEnd s

theorem animation_program (s : X86Memory.State) (flags : Option Flags) (h : Inputs s) :
    X86Routine.run program [0x3325e] 33 ⟨s,flags,0x3323e⟩ = some (result s) := by
  obtain ⟨k,hk,path,_⟩ := X86Routine.run_path (selector_program s flags)
  have path := path.transfer program [0x3325e] (fun _ _ => rfl) exit_active
  have tail : X86Routine.run program [0x3325e] 24 (selectedEnd s) = some (result s) := by
    by_cases hm : moving s
    · by_cases hs : standing s
      · simp only [selectedEnd,if_pos hm,if_pos hs,result,if_pos (And.intro hm hs)]
        exact setter_program _ _ (call_establishes_setter s h)
      · simp [selectedEnd,result,hm,hs,X86Routine.run]
    · simp [selectedEnd,result,hm,X86Routine.run]
  exact path.finish tail 33 (by omega)

/-- Actual extracted caller and callee bytes, including the real CALL/RET path. -/
theorem animation_bytes (s : X86Memory.State) (flags : Option Flags) (h : Inputs s) :
    X86Routine.run (bytesProgram Doom19.playerAnimationBytes Doom19.setMobjStateBytes)
      [0x3325e] 33 ⟨s,flags,0x3323e⟩ = some (result s) := by
  rw [X86Routine.run_sound _ program decoded _ _ _ (by rw [animation_program s flags h]; simp)]
  exact animation_program s flags h

def statePointer (frame : Nat) : Word := (0x15a28#32) + BitVec.ofNat 32 (frame*28)

theorem standing_pointer (frame : Nat) (bound : frame < 65536) :
    statePointer frame = (0x16a74#32) ↔ frame = 149 := by
  rw [← BitVec.toNat_inj]
  simp only [statePointer,BitVec.toNat_add,BitVec.toNat_ofNat]
  omega

structure EngineInputs (s : X86Memory.State) (anim : PlayerAnim.State) (cmd : Ticcmd) : Prop
    extends Inputs s where
  forward : s.memory (s.regs 6) = cmd.forwardMove.toBitVec
  side : s.memory (s.regs 6+(1#32)) = cmd.sideMove.toBitVec
  frame : load32 s.memory (object s+(100#32)) = statePointer anim.frame
  frameBound : anim.frame < 65536
  tics : load32 s.memory (object s+(96#32)) = anim.tics.toBitVec

theorem engine_selection (s : X86Memory.State) (anim : PlayerAnim.State) (cmd : Ticcmd)
    (h : EngineInputs s anim cmd) :
    (moving s ↔ cmd.forwardMove ≠ 0 ∨ cmd.sideMove ≠ 0) ∧ (standing s ↔ anim.frame = 149) := by
  constructor
  · unfold moving
    rw [h.forward,h.side]
    have f : cmd.forwardMove.toBitVec = (0#8) ↔ cmd.forwardMove = 0 := by simpa using (Int8.toBitVec_inj (a := cmd.forwardMove) (b := 0))
    have c : cmd.sideMove.toBitVec = (0#8) ↔ cmd.sideMove = 0 := by simpa using (Int8.toBitVec_inj (a := cmd.sideMove) (b := 0))
    simp only [ne_eq,f,c]
  · unfold standing; rw [h.frame]; exact standing_pointer _ h.frameBound

theorem result_fields (s : X86Memory.State) (anim : PlayerAnim.State) (cmd : Ticcmd)
    (h : EngineInputs s anim cmd) :
    (load32 (result s).core.memory (object s+(100#32)),
     load32 (result s).core.memory (object s+(96#32)),(result s).core.regs 4) =
    (statePointer (anim.startWalking cmd).frame,(anim.startWalking cmd).tics.toBitVec,s.regs 4) := by
  have selection := engine_selection s anim cmd h
  have f100_96 := apart_offsets (object s) (100#32) (96#32) (by decide)
  have f100_36 := apart_offsets (object s) (100#32) (36#32) (by decide)
  have f100_40 := apart_offsets (object s) (100#32) (40#32) (by decide)
  have ti := tics_apart (object s)
  by_cases hm : moving s <;> by_cases hs : standing s
  · have moving := selection.1.mp hm
    have standing := selection.2.mp hs
    simp [result,hm,hs,setterEnd,entryMemory,callCore,X86Routine.pushWord,put,write,
      load_store_apart _ _ _ _ f100_40,load_store_apart _ _ _ _ f100_36,
      load_store_apart _ _ _ _ f100_96,load_store_apart _ _ _ _ ti.1,load_store_apart _ _ _ _ ti.2,
      load_store,BitVec.sub_add_cancel,PlayerAnim.State.startWalking,PlayerAnim.enter,standing,statePointer,moving]
  · have notStanding : anim.frame ≠ 149 := fun eq => hs (selection.2.mpr eq)
    simp [result,selectedEnd,hm,hs,put,write,h.frame,h.tics,PlayerAnim.State.startWalking,notStanding]
  · have notMoving : cmd.forwardMove = 0 ∧ cmd.sideMove = 0 := by
      have hn : ¬ (cmd.forwardMove ≠ 0 ∨ cmd.sideMove ≠ 0) := fun v => hm (selection.1.mpr v)
      simpa using hn
    simp [result,selectedEnd,hm,h.frame,h.tics,PlayerAnim.State.startWalking,notMoving.1,notMoving.2]
  · have notMoving : cmd.forwardMove = 0 ∧ cmd.sideMove = 0 := by
      have hn : ¬ (cmd.forwardMove ≠ 0 ∨ cmd.sideMove ≠ 0) := fun v => hm (selection.1.mpr v)
      simpa using hn
    simp [result,selectedEnd,hm,h.frame,h.tics,PlayerAnim.State.startWalking,notMoving.1,notMoving.2]

theorem animation_engine (s : X86Memory.State) (flags : Option Flags)
    (anim : PlayerAnim.State) (cmd : Ticcmd) (h : EngineInputs s anim cmd) :
    (X86Routine.run (bytesProgram Doom19.playerAnimationBytes Doom19.setMobjStateBytes)
      [0x3325e] 33 ⟨s,flags,0x3323e⟩).map (fun t =>
      (t.pc,load32 t.core.memory (object s+(100#32)),load32 t.core.memory (object s+(96#32)),t.core.regs 4)) =
      some (0x3325e,statePointer (anim.startWalking cmd).frame,(anim.startWalking cmd).tics.toBitVec,s.regs 4) := by
  rw [animation_bytes s flags h.toInputs]
  simp only [Option.map_some]
  have pc : (result s).pc = 0x3325e := by
    unfold result selectedEnd
    by_cases hm : moving s <;> by_cases hs : standing s <;> simp [hm,hs,setterEnd]
  rw [pc,result_fields s anim cmd h]

end PlayerAnimation
end Doom.Proofs
