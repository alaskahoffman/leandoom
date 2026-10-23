import Doom.Proofs.OriginalPainHandoff
import Doom.Proofs.OriginalPlayerAnimation

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.PainSetter
open Verification X86 X86Memory X86Control BlockSummary
open PlayerAnimation (callee)

/-- Reuse the decoded non-null/no-action setter instruction listing. -/
def listed : X86Routine.Program := fun pc =>
  if 0x30ea0 ≤ pc ∧ pc < 0x30efb then callee (pc-0x30ea0) else none

def bytesProgram (code : List UInt8) : X86Routine.Program := fun pc =>
  if 0x30ea0 ≤ pc ∧ pc < 0x30efb then X86Routine.decodeAt code (pc-0x30ea0) else none
def program := bytesProgram Doom19.setMobjStateBytes

theorem decoded (pc : Nat) (h : listed pc ≠ none) : program pc = listed pc := by
  by_cases bound : 0x30ea0 ≤ pc ∧ pc < 0x30efb
  · simp only [listed,if_pos bound] at h ⊢
    simp only [program,bytesProgram,if_pos bound]
    exact PlayerAnimation.callee_decoded (pc-0x30ea0) h
  · simp [listed,bound] at h

def fields (obj : Word) : List Word := [obj+(100#32),obj+(96#32),obj+(36#32),obj+(40#32)]
def tableWords : List Word := [0x16b38,0x16b3c,0x16b40,0x16b44,0x16b48]

structure PainTable (m : Memory) : Prop where
  sprite : load32 m (0x16b38#32) = 28
  frame : load32 m (0x16b3c#32) = 6
  tics : load32 m (0x16b40#32) = 4
  action : load32 m (0x16b44#32) = 0
  next : load32 m (0x16b48#32) = 157

/-- Pinned first player pain-state data, including its null action. -/
def painStateBytes : List UInt8 := [28,0,0,0,6,0,0,0,4,0,0,0,0,0,0,0,157,0,0,0,0,0,0,0,0,0,0,0]
theorem table_decoded : PainTable (fun a =>
    if 0x16b38 ≤ a.toNat ∧ a.toNat < 0x16b54 then painStateBytes.toArray[a.toNat-0x16b38]!.toBitVec else 0) := by
  constructor <;> decide

/-- Callee-entry relation for the specific non-null, non-zero-tic, no-action
first pain state. The saved return address is part of ordinary stack memory. -/
structure SetterInputs (s : X86Memory.State) : Prop where
  state : s.regs 2 = 156
  table : PainTable s.memory
  returnAddress : load32 s.memory (s.regs 4) = 0x2a6df
  tableSafe : ∀ a, a ∈ tableWords → ∀ b, b ∈ fields (s.regs 0) ++ [s.regs 4-(4#32),s.regs 4-(8#32)] → Apart a b
  stackSafe : ∀ a, a ∈ [s.regs 4,s.regs 4-(4#32),s.regs 4-(8#32)] →
    ∀ b, b ∈ fields (s.regs 0) → Apart a b

def savedMemory (s : X86Memory.State) : Memory :=
  store32 (store32 s.memory (s.regs 4-(4#32)) (s.regs 3)) (s.regs 4-(8#32)) (s.regs 6)

def entryMemory (m : Memory) (obj : Word) : Memory :=
  store32 (store32 (store32 (store32 m (obj+(100#32)) 0x16b38)
    (obj+(96#32)) 4) (obj+(36#32)) 28) (obj+(40#32)) 6

def setterEnd (s : X86Memory.State) : X86Control.State :=
  ⟨⟨write (write (write s.regs 0 1) 2 157) 4 (s.regs 4+(4#32)),
    entryMemory (savedMemory s) (s.regs 0)⟩,some (logical32 4),0x2a6df⟩

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

private theorem at_30ea0 : listed 0x30ea0 = callee 0 := by decide
private theorem at_30ea1 : listed 0x30ea1 = callee 1 := by decide
private theorem at_30ea2 : listed 0x30ea2 = callee 2 := by decide
private theorem at_30ea4 : listed 0x30ea4 = callee 4 := by decide
private theorem at_30ea6 : listed 0x30ea6 = callee 6 := by decide
private theorem at_30ebb : listed 0x30ebb = callee 27 := by decide
private theorem at_30ebe : listed 0x30ebe = callee 30 := by decide
private theorem at_30ec4 : listed 0x30ec4 = callee 36 := by decide
private theorem at_30ec7 : listed 0x30ec7 = callee 39 := by decide
private theorem at_30eca : listed 0x30eca = callee 42 := by decide
private theorem at_30ecd : listed 0x30ecd = callee 45 := by decide
private theorem at_30ecf : listed 0x30ecf = callee 47 := by decide
private theorem at_30ed2 : listed 0x30ed2 = callee 50 := by decide
private theorem at_30ed5 : listed 0x30ed5 = callee 53 := by decide
private theorem at_30ed8 : listed 0x30ed8 = callee 56 := by decide
private theorem at_30edc : listed 0x30edc = callee 60 := by decide
private theorem at_30ee3 : listed 0x30ee3 = callee 67 := by decide
private theorem at_30ee6 : listed 0x30ee6 = callee 70 := by decide
private theorem at_30ee9 : listed 0x30ee9 = callee 73 := by decide
private theorem at_30eeb : listed 0x30eeb = callee 75 := by decide
private theorem at_30ef3 : listed 0x30ef3 = callee 83 := by decide
private theorem at_30ef8 : listed 0x30ef8 = callee 88 := by decide
private theorem at_30ef9 : listed 0x30ef9 = callee 89 := by decide
private theorem at_30efa : listed 0x30efa = callee 90 := by decide

def prologueEnd (s : X86Memory.State) : X86Control.State :=
  ⟨⟨write (write s.regs 4 (s.regs 4-(8#32))) 3 (s.regs 0),savedMemory s⟩,
    some (logical32 156),0x30ebb⟩

def bodyEnd (s : X86Memory.State) : X86Control.State :=
  ⟨⟨write (write (write (write (write s.regs 4 (s.regs 4-(8#32))) 3 (s.regs 0)) 0 6) 6 4) 2 157,
    entryMemory (savedMemory s) (s.regs 0)⟩,some (logical32 4),0x30ef3⟩

theorem setter_prologue (s : X86Memory.State) (flags : Option Flags) (state : s.regs 2 = 156) :
    X86Routine.run listed [0x30ebb] 5 ⟨s,flags,0x30ea0⟩ = some (prologueEnd s) := by
  let s1 := X86Routine.pushWord s (s.regs 3)
  let s2 := X86Routine.pushWord s1 (s.regs 6)
  let s3 := put s2 3 (s.regs 0)
  have path : X86Routine.Prefix listed [0x30ebb] 5 ⟨s,flags,0x30ea0⟩
      ⟨s3,some (logical32 156),0x30ebb⟩ := by
    apply X86Routine.Prefix.step (middle := ⟨s1,flags,0x30ea1⟩) (by change ¬((0x30ea0:Nat) ∈ [0x30ebb]); decide)
      (show listed 0x30ea0 = some (.push 3,1) from by decide) (by rfl)
    apply X86Routine.Prefix.step (middle := ⟨s2,flags,0x30ea2⟩) (by change ¬((0x30ea1:Nat) ∈ [0x30ebb]); decide)
      (show listed 0x30ea1 = some (.push 6,1) from by decide) (by
        simp [X86Routine.execute,s1,s2,X86Routine.pushWord,put,write])
    apply X86Routine.Prefix.step (middle := ⟨s3,flags,0x30ea4⟩) (by change ¬((0x30ea2:Nat) ∈ [0x30ebb]); decide)
      (show listed 0x30ea2 = some (.control (.block (.legacy (.mov 3 0))),2) from by decide) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
          blockPreservesFlags,s3,s2,s1,X86Routine.pushWord,put,write])
    apply X86Routine.Prefix.step (middle := ⟨s3,some (logical32 156),0x30ea6⟩) (by change ¬((0x30ea4:Nat) ∈ [0x30ebb]); decide)
      (show listed 0x30ea4 = some (.control (.testWord 2 2),2) from by decide) (by
        simp [X86Routine.execute,X86Control.execute,s3,s2,s1,X86Routine.pushWord,put,write,state])
    apply X86Routine.Prefix.step (middle := ⟨s3,some (logical32 156),0x30ebb⟩) (by change ¬((0x30ea6:Nat) ∈ [0x30ebb]); decide)
      (show listed 0x30ea6 = some (.control (.jumpZero false 19),2) from by decide) (by
        simp [X86Routine.execute,X86Control.execute,logical32])
    exact X86Routine.Prefix.nil _
  rw [show 5 = 5+0 from rfl,path.run 0]
  simp [X86Routine.run,prologueEnd,s3,s2,s1,savedMemory,X86Routine.pushWord,put,write,BitVec.sub_sub]
  funext r
  by_cases h3 : r = 3 <;> by_cases h4 : r = 4 <;> simp_all [write]

theorem setter_body (s : X86Memory.State) (h : SetterInputs s) :
    X86Routine.run listed [0x30ef3] 15 (prologueEnd s) = some (bodyEnd s) := by
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
  have addback : s.regs 4-(8#32)+(4#32) = s.regs 4-(4#32) := by simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  let c0 := (prologueEnd s).core
  let c1 : X86Memory.State := put c0 2 4368
  let c2 : X86Memory.State := put c1 2 0x16b38
  let c3 : X86Memory.State := {c2 with memory := store32 c2.memory (s.regs 0+100) 0x16b38}
  let c4 : X86Memory.State := put c3 0 4
  let c5 : X86Memory.State := {c4 with memory := store32 c4.memory (s.regs 0+96) 4}
  let c6 : X86Memory.State := put c5 0 28
  let c7 : X86Memory.State := {c6 with memory := store32 c6.memory (s.regs 0+36) 28}
  let c8 : X86Memory.State := put c7 0 6
  let c9 : X86Memory.State := {c8 with memory := store32 c8.memory (s.regs 0+40) 6}
  let c10 : X86Memory.State := c9
  let c11 : X86Memory.State := c10
  let c12 : X86Memory.State := put c11 6 4
  let c13 : X86Memory.State := put c12 2 157
  let c14 : X86Memory.State := c13
  let c15 : X86Memory.State := c14
  have path : X86Routine.Prefix listed [0x30ef3] 15 (prologueEnd s)
      ⟨c15,some (logical32 4),0x30ef3⟩ := by
    apply X86Routine.Prefix.step (middle := ⟨c1,none,0x30ebe⟩)
      (by change ¬((0x30ebb:Nat) ∈ [0x30ef3]); decide)
      (show listed 0x30ebb = some (.multiplyImmediate 2 2 28,3) from by decide) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,put,write,blockPreservesFlags,h.state,logical32,compare32,tableLoad,fields,tableWords,load_store_apart _ _ _ _ ti.1,load_store_apart _ _ _ _ ti.2,load_store,h.table.sprite,h.table.frame,h.table.tics,h.table.action,h.table.next,prologueEnd,savedMemory,c1,c0])
    apply X86Routine.Prefix.step (middle := ⟨c2,none,0x30ec4⟩)
      (by change ¬((0x30ebe:Nat) ∈ [0x30ef3]); decide)
      (show listed 0x30ebe = some (.addImmediate 2 0x15a28,6) from by decide) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,put,write,blockPreservesFlags,h.state,logical32,compare32,tableLoad,fields,tableWords,load_store_apart _ _ _ _ ti.1,load_store_apart _ _ _ _ ti.2,load_store,h.table.sprite,h.table.frame,h.table.tics,h.table.action,h.table.next,prologueEnd,savedMemory,c2,c1,c0])
    apply X86Routine.Prefix.step (middle := ⟨c3,none,0x30ec7⟩)
      (by change ¬((0x30ec4:Nat) ∈ [0x30ef3]); decide)
      (show listed 0x30ec4 = some (.control (.block (.store ⟨some 3,none,0,100⟩ 2)),3) from by decide) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,put,write,blockPreservesFlags,h.state,logical32,compare32,tableLoad,fields,tableWords,load_store_apart _ _ _ _ ti.1,load_store_apart _ _ _ _ ti.2,load_store,h.table.sprite,h.table.frame,h.table.tics,h.table.action,h.table.next,prologueEnd,savedMemory,c3,c2,c1,c0])
    apply X86Routine.Prefix.step (middle := ⟨c4,none,0x30eca⟩)
      (by change ¬((0x30ec7:Nat) ∈ [0x30ef3]); decide)
      (show listed 0x30ec7 = some (.control (.block (.legacy (.load 0 2 8))),3) from by decide) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,put,write,blockPreservesFlags,h.state,logical32,compare32,tableLoad,fields,tableWords,load_store_apart _ _ _ _ ti.1,load_store_apart _ _ _ _ ti.2,load_store,h.table.sprite,h.table.frame,h.table.tics,h.table.action,h.table.next,prologueEnd,savedMemory,c4,c3,c2,c1,c0])
    apply X86Routine.Prefix.step (middle := ⟨c5,none,0x30ecd⟩)
      (by change ¬((0x30eca:Nat) ∈ [0x30ef3]); decide)
      (show listed 0x30eca = some (.control (.block (.store ⟨some 3,none,0,96⟩ 0)),3) from by decide) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,put,write,blockPreservesFlags,h.state,logical32,compare32,tableLoad,fields,tableWords,load_store_apart _ _ _ _ ti.1,load_store_apart _ _ _ _ ti.2,load_store,h.table.sprite,h.table.frame,h.table.tics,h.table.action,h.table.next,prologueEnd,savedMemory,c5,c4,c3,c2,c1,c0])
    apply X86Routine.Prefix.step (middle := ⟨c6,none,0x30ecf⟩)
      (by change ¬((0x30ecd:Nat) ∈ [0x30ef3]); decide)
      (show listed 0x30ecd = some (.control (.block (.legacy (.load 0 2 0))),2) from by decide) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,put,write,blockPreservesFlags,h.state,logical32,compare32,tableLoad,fields,tableWords,load_store_apart _ _ _ _ ti.1,load_store_apart _ _ _ _ ti.2,load_store,h.table.sprite,h.table.frame,h.table.tics,h.table.action,h.table.next,prologueEnd,savedMemory,c6,c5,c4,c3,c2,c1,c0])
    apply X86Routine.Prefix.step (middle := ⟨c7,none,0x30ed2⟩)
      (by change ¬((0x30ecf:Nat) ∈ [0x30ef3]); decide)
      (show listed 0x30ecf = some (.control (.block (.store ⟨some 3,none,0,36⟩ 0)),3) from by decide) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,put,write,blockPreservesFlags,h.state,logical32,compare32,tableLoad,fields,tableWords,load_store_apart _ _ _ _ ti.1,load_store_apart _ _ _ _ ti.2,load_store,h.table.sprite,h.table.frame,h.table.tics,h.table.action,h.table.next,prologueEnd,savedMemory,c7,c6,c5,c4,c3,c2,c1,c0])
    apply X86Routine.Prefix.step (middle := ⟨c8,none,0x30ed5⟩)
      (by change ¬((0x30ed2:Nat) ∈ [0x30ef3]); decide)
      (show listed 0x30ed2 = some (.control (.block (.legacy (.load 0 2 4))),3) from by decide) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,put,write,blockPreservesFlags,h.state,logical32,compare32,tableLoad,fields,tableWords,load_store_apart _ _ _ _ ti.1,load_store_apart _ _ _ _ ti.2,load_store,h.table.sprite,h.table.frame,h.table.tics,h.table.action,h.table.next,prologueEnd,savedMemory,c8,c7,c6,c5,c4,c3,c2,c1,c0])
    apply X86Routine.Prefix.step (middle := ⟨c9,none,0x30ed8⟩)
      (by change ¬((0x30ed5:Nat) ∈ [0x30ef3]); decide)
      (show listed 0x30ed5 = some (.control (.block (.store ⟨some 3,none,0,40⟩ 0)),3) from by decide) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,put,write,blockPreservesFlags,h.state,logical32,compare32,tableLoad,fields,tableWords,load_store_apart _ _ _ _ ti.1,load_store_apart _ _ _ _ ti.2,load_store,h.table.sprite,h.table.frame,h.table.tics,h.table.action,h.table.next,prologueEnd,savedMemory,c9,c8,c7,c6,c5,c4,c3,c2,c1,c0])
    apply X86Routine.Prefix.step (middle := ⟨c10,some (compare32 0 0),0x30edc⟩)
      (by change ¬((0x30ed8:Nat) ∈ [0x30ef3]); decide)
      (show listed 0x30ed8 = some (.control (.cmpImmediate ⟨some 2,none,0,12⟩ 0),4) from by decide) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,put,write,blockPreservesFlags,h.state,logical32,compare32,tableLoad,fields,tableWords,load_store_apart _ _ _ _ ti.1,load_store_apart _ _ _ _ ti.2,load_store,h.table.sprite,h.table.frame,h.table.tics,h.table.action,h.table.next,prologueEnd,savedMemory,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,c0])
    apply X86Routine.Prefix.step (middle := ⟨c11,some (compare32 0 0),0x30ee3⟩)
      (by change ¬((0x30edc:Nat) ∈ [0x30ef3]); decide)
      (show listed 0x30edc = some (.control (.jumpZero true 5),2) from by decide) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,put,write,blockPreservesFlags,h.state,logical32,compare32,tableLoad,fields,tableWords,load_store_apart _ _ _ _ ti.1,load_store_apart _ _ _ _ ti.2,load_store,h.table.sprite,h.table.frame,h.table.tics,h.table.action,h.table.next,prologueEnd,savedMemory,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,c0])
    apply X86Routine.Prefix.step (middle := ⟨c12,some (compare32 0 0),0x30ee6⟩)
      (by change ¬((0x30ee3:Nat) ∈ [0x30ef3]); decide)
      (show listed 0x30ee3 = some (.control (.block (.legacy (.load 6 3 96))),3) from by decide) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,put,write,blockPreservesFlags,h.state,logical32,compare32,tableLoad,fields,tableWords,load_store_apart _ _ _ _ ti.1,load_store_apart _ _ _ _ ti.2,load_store,h.table.sprite,h.table.frame,h.table.tics,h.table.action,h.table.next,prologueEnd,savedMemory,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,c0])
    apply X86Routine.Prefix.step (middle := ⟨c13,some (compare32 0 0),0x30ee9⟩)
      (by change ¬((0x30ee6:Nat) ∈ [0x30ef3]); decide)
      (show listed 0x30ee6 = some (.control (.block (.legacy (.load 2 2 16))),3) from by decide) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,put,write,blockPreservesFlags,h.state,logical32,compare32,tableLoad,fields,tableWords,load_store_apart _ _ _ _ ti.1,load_store_apart _ _ _ _ ti.2,load_store,h.table.sprite,h.table.frame,h.table.tics,h.table.action,h.table.next,prologueEnd,savedMemory,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,c0])
    apply X86Routine.Prefix.step (middle := ⟨c14,some (logical32 4),0x30eeb⟩)
      (by change ¬((0x30ee9:Nat) ∈ [0x30ef3]); decide)
      (show listed 0x30ee9 = some (.control (.testWord 6 6),2) from by decide) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,put,write,blockPreservesFlags,h.state,logical32,compare32,tableLoad,fields,tableWords,load_store_apart _ _ _ _ ti.1,load_store_apart _ _ _ _ ti.2,load_store,h.table.sprite,h.table.frame,h.table.tics,h.table.action,h.table.next,prologueEnd,savedMemory,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,c0])
    apply X86Routine.Prefix.step (middle := ⟨c15,some (logical32 4),0x30ef3⟩)
      (by change ¬((0x30eeb:Nat) ∈ [0x30ef3]); decide)
      (show listed 0x30eeb = some (.control (.jumpZero false 6),2) from by decide) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,put,write,blockPreservesFlags,h.state,logical32,compare32,tableLoad,fields,tableWords,load_store_apart _ _ _ _ ti.1,load_store_apart _ _ _ _ ti.2,load_store,h.table.sprite,h.table.frame,h.table.tics,h.table.action,h.table.next,prologueEnd,savedMemory,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,c0])
    exact X86Routine.Prefix.nil _
  rw [show 15 = 15+0 from rfl,path.run 0]
  simp [X86Routine.run,bodyEnd,entryMemory,prologueEnd,put,write,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,c0]
  funext r
  by_cases h0 : r = 0 <;> by_cases h2 : r = 2 <;> by_cases h3 : r = 3 <;>
    by_cases h4 : r = 4 <;> by_cases h6 : r = 6 <;> simp_all [write]

theorem setter_epilogue (s : X86Memory.State) (h : SetterInputs s) :
    X86Routine.run listed [0x2a6df] 4 (bodyEnd s) = some (setterEnd s) := by
  have active_83 : (0x30ef3:Nat) ∉ [0x2a6df] := by decide
  have active_88 : (0x30ef8:Nat) ∉ [0x2a6df] := by decide
  have active_89 : (0x30ef9:Nat) ∉ [0x2a6df] := by decide
  have active_90 : (0x30efa:Nat) ∉ [0x2a6df] := by decide

  have tableLoad (m : Memory) (a b v : Word) (ha : a ∈ tableWords)
      (hb : b ∈ fields (s.regs 0) ++ [s.regs 4-(4#32),s.regs 4-(8#32)]) :=
    load_store_apart m b a v (h.tableSafe a ha b hb)
  have stackLoad (m : Memory) (a b v : Word)
      (ha : a ∈ [s.regs 4,s.regs 4-(4#32),s.regs 4-(8#32)]) (hb : b ∈ fields (s.regs 0)) :=
    load_store_apart m b a v (h.stackSafe a ha b hb)
  have st := stack_apart (s.regs 4)
  have ti := tics_apart (s.regs 0)
  have addback : s.regs 4-(8#32)+(4#32) = s.regs 4-(4#32) := by simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  let c0 := (bodyEnd s).core
  let c1 : X86Memory.State := put c0 0 1
  let c2 : X86Memory.State := put (put c1 4 (s.regs 4-4)) 6 (s.regs 6)
  let c3 : X86Memory.State := put (put c2 4 (s.regs 4)) 3 (s.regs 3)
  let c4 : X86Memory.State := put c3 4 (s.regs 4+4)
  have path : X86Routine.Prefix listed [0x2a6df] 4 (bodyEnd s) ⟨c4,some (logical32 4),0x2a6df⟩ := by
    apply X86Routine.Prefix.step (middle := ⟨c1,some (logical32 4),0x30ef8⟩)
      (by change ¬((0x30ef3:Nat) ∈ [0x2a6df]); decide)
      (show listed 0x30ef3 = some (.immediate 0 1,5) from by decide) (by
        simp [active_83,active_88,active_89,active_90,at_30ea0,at_30ea1,at_30ea2,at_30ea4,at_30ea6,at_30ebb,at_30ebe,at_30ec4,at_30ec7,at_30eca,at_30ecd,at_30ecf,at_30ed2,at_30ed5,at_30ed8,at_30edc,at_30ee3,at_30ee6,at_30ee9,at_30eeb,at_30ef3,at_30ef8,at_30ef9,at_30efa,callee,X86Routine.execute,X86Control.execute,X86Block.execute,
    X86Memory.execute,X86Block.Address.eval,X86Routine.pushWord,put,write,
    blockPreservesFlags,logical32,compare32,h.state,BitVec.sub_sub,addback,BitVec.sub_add_cancel,tableLoad,stackLoad,
    fields,tableWords,load_store_apart _ _ _ _ st.1,load_store_apart _ _ _ _ st.2.1,
    load_store_apart _ _ _ _ st.2.2,load_store_apart _ _ _ _ ti.1,
    load_store_apart _ _ _ _ ti.2,load_store,h.table.sprite,h.table.frame,h.table.tics,
    h.table.action,h.table.next,h.returnAddress,bodyEnd,setterEnd,entryMemory,savedMemory,eax,c1,c0])
    apply X86Routine.Prefix.step (middle := ⟨c2,some (logical32 4),0x30ef9⟩)
      (by change ¬((0x30ef8:Nat) ∈ [0x2a6df]); decide)
      (show listed 0x30ef8 = some (.pop 6,1) from by decide) (by
        simp [active_83,active_88,active_89,active_90,at_30ea0,at_30ea1,at_30ea2,at_30ea4,at_30ea6,at_30ebb,at_30ebe,at_30ec4,at_30ec7,at_30eca,at_30ecd,at_30ecf,at_30ed2,at_30ed5,at_30ed8,at_30edc,at_30ee3,at_30ee6,at_30ee9,at_30eeb,at_30ef3,at_30ef8,at_30ef9,at_30efa,callee,X86Routine.execute,X86Control.execute,X86Block.execute,
    X86Memory.execute,X86Block.Address.eval,X86Routine.pushWord,put,write,
    blockPreservesFlags,logical32,compare32,h.state,BitVec.sub_sub,addback,BitVec.sub_add_cancel,tableLoad,stackLoad,
    fields,tableWords,load_store_apart _ _ _ _ st.1,load_store_apart _ _ _ _ st.2.1,
    load_store_apart _ _ _ _ st.2.2,load_store_apart _ _ _ _ ti.1,
    load_store_apart _ _ _ _ ti.2,load_store,h.table.sprite,h.table.frame,h.table.tics,
    h.table.action,h.table.next,h.returnAddress,bodyEnd,setterEnd,entryMemory,savedMemory,eax,c2,c1,c0])
    apply X86Routine.Prefix.step (middle := ⟨c3,some (logical32 4),0x30efa⟩)
      (by change ¬((0x30ef9:Nat) ∈ [0x2a6df]); decide)
      (show listed 0x30ef9 = some (.pop 3,1) from by decide) (by
        simp [active_83,active_88,active_89,active_90,at_30ea0,at_30ea1,at_30ea2,at_30ea4,at_30ea6,at_30ebb,at_30ebe,at_30ec4,at_30ec7,at_30eca,at_30ecd,at_30ecf,at_30ed2,at_30ed5,at_30ed8,at_30edc,at_30ee3,at_30ee6,at_30ee9,at_30eeb,at_30ef3,at_30ef8,at_30ef9,at_30efa,callee,X86Routine.execute,X86Control.execute,X86Block.execute,
    X86Memory.execute,X86Block.Address.eval,X86Routine.pushWord,put,write,
    blockPreservesFlags,logical32,compare32,h.state,BitVec.sub_sub,addback,BitVec.sub_add_cancel,tableLoad,stackLoad,
    fields,tableWords,load_store_apart _ _ _ _ st.1,load_store_apart _ _ _ _ st.2.1,
    load_store_apart _ _ _ _ st.2.2,load_store_apart _ _ _ _ ti.1,
    load_store_apart _ _ _ _ ti.2,load_store,h.table.sprite,h.table.frame,h.table.tics,
    h.table.action,h.table.next,h.returnAddress,bodyEnd,setterEnd,entryMemory,savedMemory,eax,c3,c2,c1,c0])
    apply X86Routine.Prefix.step (middle := ⟨c4,some (logical32 4),0x2a6df⟩)
      (by change ¬((0x30efa:Nat) ∈ [0x2a6df]); decide)
      (show listed 0x30efa = some (.ret,1) from by decide) (by
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

theorem exit_active (pc : Nat) (h : listed pc ≠ none) : pc ∉ [0x2a6df] := by
  simp only [List.mem_singleton]
  intro eq; subst pc
  exact h (by rfl)

theorem setter_program (s : X86Memory.State) (flags : Option Flags) (h : SetterInputs s) :
    X86Routine.run listed [0x2a6df] 24 ⟨s,flags,0x30ea0⟩ = some (setterEnd s) := by
  obtain ⟨k,hk,p,_⟩ := X86Routine.run_path (setter_prologue s flags h.state)
  obtain ⟨j,hj,q,_⟩ := X86Routine.run_path (setter_body s h)
  have p := p.transfer listed [0x2a6df] (fun _ _ => rfl) exit_active
  have q := q.transfer listed [0x2a6df] (fun _ _ => rfl) exit_active
  have tail := q.finish (setter_epilogue s h) 19 (by omega)
  exact p.finish tail 24 (by omega)


theorem original_execution (s : X86Memory.State) (f : Option Flags) (h : SetterInputs s) :
    X86Routine.run program [0x2a6df] 24 ⟨s,f,0x30ea0⟩ = some (setterEnd s) := by
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [setter_program s f h]; simp)]
  exact setter_program s f h

def writes (s : X86Memory.State) := fields (s.regs 0) ++ [s.regs 4-(4#32),s.regs 4-(8#32)]
theorem memory_frame (s : X86Memory.State) :
    PlayerHeight.Frame s.memory (setterEnd s).core.memory (writes s) := by
  intro a safe
  unfold setterEnd entryMemory savedMemory
  repeat rw [load_store_apart _ _ _ _ (safe _ (by simp [writes,fields]))]

def observeFields (m : Memory) (obj : Word) :=
  (load32 m (obj+(100#32)),load32 m (obj+(96#32)),load32 m (obj+(36#32)),load32 m (obj+(40#32)))

theorem entry_fields (m : Memory) (obj : Word) :
    observeFields (entryMemory m obj) obj = ((0x16b38#32),(4#32),(28#32),(6#32)) := by
  have keep (a b : Fin 256) (sep : a.val+4 ≤ b.val ∨ b.val+4 ≤ a.val) (m : Memory) (v : Word) :=
    load_store_apart m (obj+BitVec.ofNat 32 b.val) (obj+BitVec.ofNat 32 a.val) v (PlayerHealth.offsets_apart obj a b sep)
  have k100_40 (m : Memory) (v : Word) : load32 (store32 m (obj+(40#32)) v) (obj+(100#32)) = load32 m (obj+(100#32)) := keep 100 40 (by decide) m v
  have k100_36 (m : Memory) (v : Word) : load32 (store32 m (obj+(36#32)) v) (obj+(100#32)) = load32 m (obj+(100#32)) := keep 100 36 (by decide) m v
  have k100_96 (m : Memory) (v : Word) : load32 (store32 m (obj+(96#32)) v) (obj+(100#32)) = load32 m (obj+(100#32)) := keep 100 96 (by decide) m v
  have k96_40 (m : Memory) (v : Word) : load32 (store32 m (obj+(40#32)) v) (obj+(96#32)) = load32 m (obj+(96#32)) := keep 96 40 (by decide) m v
  have k96_36 (m : Memory) (v : Word) : load32 (store32 m (obj+(36#32)) v) (obj+(96#32)) = load32 m (obj+(96#32)) := keep 96 36 (by decide) m v
  have k36_40 (m : Memory) (v : Word) : load32 (store32 m (obj+(40#32)) v) (obj+(36#32)) = load32 m (obj+(36#32)) := keep 36 40 (by decide) m v
  simp only [observeFields,entryMemory]
  rw [k100_40,k100_36,k100_96,load_store,k96_40,k96_36,load_store,k36_40,load_store,load_store]
  rfl

def exits : List Nat := [0x2a6a6,0x2a6df,0x2a747]
def joined (pc : Nat) : Option (X86Routine.Op × Nat) :=
  if 0x30ea0 ≤ pc ∧ pc < 0x30efb then program pc else PainHandoff.joined pc

theorem contains_handoff (pc : Nat) (h : PainHandoff.joined pc ≠ none) : joined pc = PainHandoff.joined pc := by
  unfold joined
  split
  next bounds =>
    have b1 : ¬(0x2a650 ≤ pc ∧ pc < 0x2a6a6) := by omega
    have b2 : ¬(0x1bb50 ≤ pc ∧ pc < 0x1bb66) := by omega
    have b3 : ¬(0x1bc41 ≤ pc ∧ pc < 0x1bc45) := by omega
    have b4 : ¬(0x2a616 ≤ pc ∧ pc < 0x2a650) := by omega
    have b5 : ¬(0x2a460 ≤ pc ∧ pc < 0x2a5d5) := by omega
    have b6 : ¬(0x2a5d5 ≤ pc ∧ pc < 0x2a616) := by omega
    have b7 : ¬(0x2a6b6 ≤ pc ∧ pc < 0x2a6c9) := by omega
    have b8 : ¬(0x24160 ≤ pc ∧ pc < 0x2417c) := by omega
    have b9 : ¬(0x2a6c9 ≤ pc ∧ pc < 0x2a6df) := by omega
    simp [PainHandoff.joined,PlayerPain.joined,ActorHealth.joined,PlayerHealth.joined,
      PlayerDamageEntry.program,PlayerDamageEntry.bytesProgram,b1,b2,b3,b4,b5,b6,b7,b8,b9,
      show pc ≠ 0x2fb76 by omega,show pc ≠ 0x2fba0 by omega,show pc ≠ 0x2fbd2 by omega] at h
  next => rfl

theorem handoff_active (pc : Nat) (h : PainHandoff.joined pc ≠ none) : pc ∉ exits := by
  intro hm
  simp only [exits,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl <;> contradiction

theorem contains_setter (pc : Nat) (h : program pc ≠ none) : joined pc = program pc := by
  unfold joined
  split
  next => rfl
  next hn => simp [program,bytesProgram,hn] at h

theorem setter_active (pc : Nat) (h : program pc ≠ none) : pc ∉ exits := by
  intro hm
  simp only [exits,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl <;> contradiction

def suffixWrites (s : X86Memory.State) := fields (s.regs 0) ++ [s.regs 4-(36#32),s.regs 4-(40#32)]
def retained (s : X86Memory.State) := PainHandoff.retained s ++ [s.regs 0+(104#32)]
structure JoinedInputs (s : X86Memory.State) (v : PlayerDamage.State) (d : Int32) (baby : Bool) (i : UInt8)
    extends toHandoff : PainHandoff.JoinedInputs s v d baby i where
  painTable : PainTable s.memory
  tablePreviousSafe : ∀ a, a ∈ tableWords → ∀ b, b ∈ PainHandoff.joinedWrites s → Apart a b
  animationPreviousSafe : ∀ a, a ∈ fields (s.regs 0) → ∀ b, b ∈ PainHandoff.joinedWrites s → Apart a b
  tableSetterSafe : ∀ a, a ∈ tableWords → ∀ b, b ∈ suffixWrites s → Apart a b
  stackSetterSafe : ∀ a, a ∈ [s.regs 4-(32#32),s.regs 4-(36#32),s.regs 4-(40#32)] →
    ∀ b, b ∈ fields (s.regs 0) → Apart a b
  retainedSetterSafe : ∀ a, a ∈ retained s → ∀ b, b ∈ suffixWrites s → Apart a b

/-- State identity and tics come from the actual live entry function. Sprite
and frame are the pinned original state's presentation fields. -/
def painFields :=
  (PlayerAnimation.statePointer (PlayerAnim.enter 156).1.frame,(PlayerAnim.enter 156).1.tics.toBitVec,(28#32),(6#32))
def observation (s : X86Memory.State) (t : X86Control.State) :=
  ((ActorHealth.observation s t,load32 t.core.memory (0x12720#32)),
    load32 t.core.memory (s.regs 0+(104#32)),observeFields t.core.memory (s.regs 0))
def answer (s : X86Memory.State) (v : PlayerDamage.State) (d : Int32) (baby : Bool) (i : UInt8) :=
  let prev := PainHandoff.answer s v d baby i
  ((prev.1.1,prev.1.2.1),prev.2.1,
    if prev.1.2.2 then painFields else observeFields s.memory (s.regs 0))
def joinedWrites (s : X86Memory.State) := PainHandoff.joinedWrites s ++ suffixWrites s

def afterWrites (s : X86Memory.State) := PainHandoff.afterWrites s ++ suffixWrites s

/-- All table/stack/field relations are established from the initial damage
CALL state, then the real setter returns to the original damage continuation. -/
theorem joined_execution_detailed (s : X86Memory.State) (f : Option Flags) (pc : Nat)
    (site : pc ∈ PlayerDamageEntry.sites) (v : PlayerDamage.State) (d : Int32) (baby : Bool)
    (i : UInt8) (h : JoinedInputs s v d baby i) :
    ∃ t, X86Routine.run joined exits 152 ⟨s,f,pc⟩ = some t ∧
      observation s t = answer s v d baby i ∧ t.core.regs 4 = s.regs 4-(28#32) ∧
      t.core.regs 6 = s.regs 0 ∧ PlayerHeight.Frame s.memory t.core.memory (joinedWrites s) ∧
      PlayerHeight.Frame (PlayerDamageEntry.saved s pc) t.core.memory (afterWrites s) := by
  obtain ⟨g,grun,gobs,gsp,gobj,gframe,gsaved⟩ := PainHandoff.joined_execution_detailed s f pc site v d baby i h.toHandoff
  obtain ⟨n,hn,path,gexit⟩ := X86Routine.run_path grun
  have path := path.transfer joined exits contains_handoff handoff_active
  have choice : decide (g.pc=0x30ea0) = (PainHandoff.answer s v d baby i).1.2.2 := congrArg (fun x => x.1.2.2) gobs
  have observed := congrArg (fun x => ((x.1.1,x.1.2.1),x.2.1)) gobs
  change ((ActorHealth.observation s g,load32 g.core.memory (0x12720#32)),load32 g.core.memory (s.regs 0+(104#32))) = _ at observed
  by_cases gp : g.pc=0x30ea0
  · have selected : (PainHandoff.answer s v d baby i).1.2.2 = true := by simpa [gp] using choice.symm
    have args := congrArg (fun x => x.2.2) gobs
    simp only [PainHandoff.observation,gp,if_true,PainHandoff.answer] at args
    have pain : (PlayerPain.answer v d baby i).2.2 = true := selected
    simp only [pain,if_true,Option.some.injEq,Prod.mk.injEq] at args
    obtain ⟨target,state,ret⟩ := args
    have sp : g.core.regs 4 = s.regs 4-(32#32) := by simpa only [gp,if_true] using gsp
    have slots : writes g.core = suffixWrites s := by simp [writes,suffixWrites,target,sp,BitVec.sub_sub]
    have table (a : Word) (ha : a ∈ tableWords) : load32 g.core.memory a = load32 s.memory a :=
      gframe a (h.tablePreviousSafe a ha)
    have ins : SetterInputs g.core := by
      refine ⟨state,?_,ret,?_,?_⟩
      · constructor
        · rw [table _ (by simp [tableWords])]; exact h.painTable.sprite
        · rw [table _ (by simp [tableWords])]; exact h.painTable.frame
        · rw [table _ (by simp [tableWords])]; exact h.painTable.tics
        · rw [table _ (by simp [tableWords])]; exact h.painTable.action
        · rw [table _ (by simp [tableWords])]; exact h.painTable.next
      · intro a ha b hb
        apply h.tableSetterSafe a ha b
        simpa [suffixWrites,target,sp,BitVec.sub_sub] using hb
      · intro a ha b hb
        apply h.stackSetterSafe a
        · simpa [sp,BitVec.sub_sub] using ha
        · simpa [target] using hb
    have trun := original_execution g.core g.flags ins
    rw [← gp] at trun
    obtain ⟨k,hk,tail,_⟩ := X86Routine.run_path trun
    have tail := tail.transfer joined exits contains_setter setter_active
    have done : (setterEnd g.core).pc ∈ exits := by simp [setterEnd,exits]
    have rest : X86Routine.run joined exits 24 g = some (setterEnd g.core) :=
      tail.finish (fuel := 0) (by simp [X86Routine.run,done]) 24 (by omega)
    have preserve (a : Word) (ha : a ∈ retained s) :
        load32 (setterEnd g.core).core.memory a = load32 g.core.memory a := by
      apply memory_frame
      intro b hb; rw [slots] at hb; exact h.retainedSetterSafe a ha b hb
    have old : ActorHealth.observation s (setterEnd g.core) = ActorHealth.observation s g := by
      simp only [ActorHealth.observation,PlayerHealth.observation,setterEnd,gp]
      simp [write]
      exact ⟨⟨preserve _ (by simp [retained,PainHandoff.retained,ActorHealth.fields]),
        preserve _ (by simp [retained,PainHandoff.retained,ActorHealth.fields]),
        preserve _ (by simp [retained,PainHandoff.retained,ActorHealth.fields]),
        preserve _ (by simp [retained,PainHandoff.retained,ActorHealth.fields]),
        preserve _ (by simp [retained,PainHandoff.retained,ActorHealth.fields])⟩,
        preserve _ (by simp [retained,PainHandoff.retained])⟩
    have fieldResult : observeFields (setterEnd g.core).core.memory (s.regs 0) = painFields := by
      rw [← target,setterEnd,entry_fields]
      rfl
    refine ⟨setterEnd g.core,path.finish rest 152 (by omega),?_,?_,?_,?_,?_⟩
    · unfold observation answer
      dsimp only
      rw [old,preserve (0x12720#32) (by simp [retained,PainHandoff.retained]),
        preserve (s.regs 0+(104#32)) (by simp [retained]),fieldResult]
      simp only [selected,↓reduceIte]
      have eq := congrArg (fun x => (x.1,x.2,painFields)) observed
      exact eq
    · simp [setterEnd,write,sp,BitVec.sub_eq_add_neg,BitVec.add_assoc]
    · simpa [setterEnd,write] using gobj
    · intro a safe
      rw [memory_frame g.core a]
      · exact gframe a (fun b hb => safe b (by simp [joinedWrites,hb]))
      · intro b hb; rw [slots] at hb; exact safe b (by simp [joinedWrites,hb])
    · intro a safe
      rw [memory_frame g.core a]
      · exact gsaved a (fun b hb => safe b (by simp [afterWrites,hb]))
      · intro b hb; rw [slots] at hb; exact safe b (by simp [afterWrites,hb])
  · have selected : (PainHandoff.answer s v d baby i).1.2.2 = false := by simpa [gp] using choice.symm
    have done : g.pc ∈ exits := by
      simp only [PainHandoff.exits,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at gexit
      simp only [exits,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false]
      omega
    have unchanged : observeFields g.core.memory (s.regs 0) = observeFields s.memory (s.regs 0) := by
      unfold observeFields
      rw [gframe _ (h.animationPreviousSafe _ (by simp [fields])),gframe _ (h.animationPreviousSafe _ (by simp [fields])),
        gframe _ (h.animationPreviousSafe _ (by simp [fields])),gframe _ (h.animationPreviousSafe _ (by simp [fields]))]
    refine ⟨g,path.finish (fuel := 0) (by simp [X86Routine.run,done]) 152 (by omega),?_,?_,gobj,?_,?_⟩
    · unfold observation answer
      dsimp only
      simp only [selected,↓reduceIte,unchanged]
      exact congrArg (fun x => (x.1,x.2,observeFields s.memory (s.regs 0))) observed
    · simpa [gp] using gsp
    · intro a safe; exact gframe a (fun b hb => safe b (by simp [joinedWrites,hb]))
    · intro a safe; exact gsaved a (fun b hb => safe b (by simp [afterWrites,hb]))

theorem joined_execution (s : X86Memory.State) (f : Option Flags) (pc : Nat)
    (site : pc ∈ PlayerDamageEntry.sites) (v : PlayerDamage.State) (d : Int32) (baby : Bool)
    (i : UInt8) (h : JoinedInputs s v d baby i) :
    ∃ t, X86Routine.run joined exits 152 ⟨s,f,pc⟩ = some t ∧
      observation s t = answer s v d baby i ∧ t.core.regs 4 = s.regs 4-(28#32) ∧
      t.core.regs 6 = s.regs 0 ∧ PlayerHeight.Frame s.memory t.core.memory (joinedWrites s) := by
  obtain ⟨t,run,obs,sp,obj,frame,_⟩ := joined_execution_detailed s f pc site v d baby i h
  exact ⟨t,run,obs,sp,obj,frame⟩

def liveObservation (s : X86Memory.State) (v : PlayerDamage.State) (out : PlayerDamage.Result) :=
  ((ActorHealth.liveObservation v out,BitVec.ofNat 32 out.rng.play.toNat),
    load32 s.memory (s.regs 0+(104#32)) ||| (if out.pain then (64#32) else (0#32)),
    if out.pain then painFields else observeFields s.memory (s.regs 0))

theorem live_answer (s : X86Memory.State) (v : PlayerDamage.State) (d : Int32) (baby : Bool) (rng : DoomRandom)
    (skull : v.skullFly=false) (ordinary : v.sectorSpecial ≠ 11) :
    liveObservation s v (PlayerDamage.apply v d none false baby rng) = answer s v d baby rng.play := by
  have eq := PainHandoff.live_answer s v d baby rng skull ordinary
  have mapped := congrArg (fun x => ((x.1.1,x.1.2.1),x.2.1,
    if x.1.2.2 then painFields else observeFields s.memory (s.regs 0))) eq
  exact mapped

theorem live_correspondence (s : X86Memory.State) (f : Option Flags) (pc : Nat)
    (site : pc ∈ PlayerDamageEntry.sites) (v : PlayerDamage.State) (d : Int32)
    (baby : Bool) (rng : DoomRandom) (h : JoinedInputs s v d baby rng.play) :
    (X86Routine.run joined exits 152 ⟨s,f,pc⟩).map (observation s) =
      some (liveObservation s v (PlayerDamage.apply v d none false baby rng)) := by
  obtain ⟨t,run,obs,_⟩ := joined_execution s f pc site v d baby rng.play h
  rw [live_answer s v d baby rng h.liveSkull h.liveOrdinary]
  simp [run,obs]

end Doom.Proofs.PainSetter
