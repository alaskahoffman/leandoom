import Doom.Proofs.OriginalPainSetter
import Doom.DeathData
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.DeathSetter
open Verification X86 X86Memory X86Control BlockSummary
abbrev listed := PainSetter.listed
abbrev program := PainSetter.program
abbrev decoded := PainSetter.decoded
abbrev fields := PainSetter.fields

/-- A non-null state with no action and nonzero duration. The return site is
P_KillMobj's state-entry continuation. Values stay symbolic for reuse. -/
structure Entry where
  index : Word
  sprite : Word
  frame : Word
  tics : Word
  next : Word
  indexNonzero : index ≠ (0#32)
  ticsNonzero : tics ≠ (0#32)

def Entry.pointer (p : Entry) : Word := p.index*28+0x15a28
def tableWords (p : Entry) : List Word :=
  [p.pointer,p.pointer+4,p.pointer+8,p.pointer+12,p.pointer+16]
structure Table (p : Entry) (m : Memory) : Prop where
  sprite : load32 m p.pointer=p.sprite
  frame : load32 m (p.pointer+4)=p.frame
  tics : load32 m (p.pointer+8)=p.tics
  action : load32 m (p.pointer+12)=0
  next : load32 m (p.pointer+16)=p.next
structure SetterInputs (p : Entry) (s : X86Memory.State) (returnPC : Word := 0x2a3f1) : Prop where
  state : s.regs 2=p.index
  table : Table p s.memory
  returnAddress : load32 s.memory (s.regs 4)=returnPC
  tableSafe : ∀ a, a ∈ tableWords p → ∀ b, b ∈ fields (s.regs 0) ++ [s.regs 4-4,s.regs 4-8] → Apart a b
  stackSafe : ∀ a, a ∈ [s.regs 4,s.regs 4-4,s.regs 4-8] → ∀ b, b ∈ fields (s.regs 0) → Apart a b

def savedMemory (s : X86Memory.State) : Memory :=
  store32 (store32 s.memory (s.regs 4-(4#32)) (s.regs 3)) (s.regs 4-(8#32)) (s.regs 6)

def entryMemory (p : Entry) (m : Memory) (obj : Word) : Memory :=
  store32 (store32 (store32 (store32 m (obj+(100#32)) p.pointer)
    (obj+(96#32)) p.tics) (obj+(36#32)) p.sprite) (obj+(40#32)) p.frame

def setterEnd (p : Entry) (s : X86Memory.State) : X86Control.State :=
  ⟨⟨write (write (write s.regs 0 1) 2 p.next) 4 (s.regs 4+(4#32)),
    entryMemory p (savedMemory s) (s.regs 0)⟩,some (logical32 p.tics),0x2a3f1⟩

abbrev stack_apart := PainSetter.stack_apart
abbrev tics_apart := PainSetter.tics_apart

def prologueEnd (p : Entry) (s : X86Memory.State) : X86Control.State :=
  ⟨⟨write (write s.regs 4 (s.regs 4-(8#32))) 3 (s.regs 0),savedMemory s⟩,
    some (logical32 p.index),0x30ebb⟩

def bodyEnd (p : Entry) (s : X86Memory.State) : X86Control.State :=
  ⟨⟨write (write (write (write (write s.regs 4 (s.regs 4-(8#32))) 3 (s.regs 0)) 0 p.frame) 6 p.tics) 2 p.next,
    entryMemory p (savedMemory s) (s.regs 0)⟩,some (logical32 p.tics),0x30ef3⟩

theorem setter_prologue (p : Entry) (s : X86Memory.State) (flags : Option Flags) (state : s.regs 2 = p.index) :
    X86Routine.run listed [0x30ebb] 5 ⟨s,flags,0x30ea0⟩ = some (prologueEnd p s) := by
  let s1 := X86Routine.pushWord s (s.regs 3)
  let s2 := X86Routine.pushWord s1 (s.regs 6)
  let s3 := put s2 3 (s.regs 0)
  have path : X86Routine.Prefix listed [0x30ebb] 5 ⟨s,flags,0x30ea0⟩
      ⟨s3,some (logical32 p.index),0x30ebb⟩ := by
    apply X86Routine.Prefix.step (middle := ⟨s1,flags,0x30ea1⟩) (by change ¬((0x30ea0:Nat) ∈ [0x30ebb]); decide)
      (show listed 0x30ea0 = some (.push 3,1) from by decide) (by rfl)
    apply X86Routine.Prefix.step (middle := ⟨s2,flags,0x30ea2⟩) (by change ¬((0x30ea1:Nat) ∈ [0x30ebb]); decide)
      (show listed 0x30ea1 = some (.push 6,1) from by decide) (by
        simp [X86Routine.execute,s1,s2,X86Routine.pushWord,put,write])
    apply X86Routine.Prefix.step (middle := ⟨s3,flags,0x30ea4⟩) (by change ¬((0x30ea2:Nat) ∈ [0x30ebb]); decide)
      (show listed 0x30ea2 = some (.control (.block (.legacy (.mov 3 0))),2) from by decide) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
          blockPreservesFlags,s3,s2,s1,X86Routine.pushWord,put,write])
    apply X86Routine.Prefix.step (middle := ⟨s3,some (logical32 p.index),0x30ea6⟩) (by change ¬((0x30ea4:Nat) ∈ [0x30ebb]); decide)
      (show listed 0x30ea4 = some (.control (.testWord 2 2),2) from by decide) (by
        simp [X86Routine.execute,X86Control.execute,s3,s2,s1,X86Routine.pushWord,put,write,state])
    apply X86Routine.Prefix.step (middle := ⟨s3,some (logical32 p.index),0x30ebb⟩) (by change ¬((0x30ea6:Nat) ∈ [0x30ebb]); decide)
      (show listed 0x30ea6 = some (.control (.jumpZero false 19),2) from by decide) (by
        simp [X86Routine.execute,X86Control.execute,logical32,p.indexNonzero,p.ticsNonzero])
    exact X86Routine.Prefix.nil _
  rw [show 5 = 5+0 from rfl,path.run 0]
  simp [X86Routine.run,prologueEnd,s3,s2,s1,savedMemory,X86Routine.pushWord,put,write,BitVec.sub_sub]
  funext r
  by_cases h3 : r = 3 <;> by_cases h4 : r = 4 <;> simp_all [write]

theorem setter_body (p : Entry) (s : X86Memory.State) {returnPC : Word} (h : SetterInputs p s returnPC) :
    X86Routine.run listed [0x30ef3] 15 (prologueEnd p s) = some (bodyEnd p s) := by
  have ht_sprite := h.table.sprite
  simp [Entry.pointer] at ht_sprite
  have ht_frame := h.table.frame
  simp [Entry.pointer] at ht_frame
  have ht_tics := h.table.tics
  simp [Entry.pointer] at ht_tics
  have ht_action := h.table.action
  simp [Entry.pointer] at ht_action
  have ht_next := h.table.next
  simp [Entry.pointer] at ht_next

  have tableLoad (m : Memory) (a b v : Word) (ha : a ∈ tableWords p)
      (hb : b ∈ fields (s.regs 0) ++ [s.regs 4-(4#32),s.regs 4-(8#32)]) :=
    load_store_apart m b a v (h.tableSafe a ha b hb)
  have stackLoad (m : Memory) (a b v : Word)
      (ha : a ∈ [s.regs 4,s.regs 4-(4#32),s.regs 4-(8#32)]) (hb : b ∈ fields (s.regs 0)) :=
    load_store_apart m b a v (h.stackSafe a ha b hb)
  have st := stack_apart (s.regs 4)
  have ti := tics_apart (s.regs 0)
  have addback : s.regs 4-(8#32)+(4#32) = s.regs 4-(4#32) := by simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  let c0 := (prologueEnd p s).core
  let c1 : X86Memory.State := put c0 2 (p.index*28)
  let c2 : X86Memory.State := put c1 2 p.pointer
  let c3 : X86Memory.State := {c2 with memory := store32 c2.memory (s.regs 0+100) p.pointer}
  let c4 : X86Memory.State := put c3 0 p.tics
  let c5 : X86Memory.State := {c4 with memory := store32 c4.memory (s.regs 0+96) p.tics}
  let c6 : X86Memory.State := put c5 0 p.sprite
  let c7 : X86Memory.State := {c6 with memory := store32 c6.memory (s.regs 0+36) p.sprite}
  let c8 : X86Memory.State := put c7 0 p.frame
  let c9 : X86Memory.State := {c8 with memory := store32 c8.memory (s.regs 0+40) p.frame}
  let c10 : X86Memory.State := c9
  let c11 : X86Memory.State := c10
  let c12 : X86Memory.State := put c11 6 p.tics
  let c13 : X86Memory.State := put c12 2 p.next
  let c14 : X86Memory.State := c13
  let c15 : X86Memory.State := c14
  have path : X86Routine.Prefix listed [0x30ef3] 15 (prologueEnd p s)
      ⟨c15,some (logical32 p.tics),0x30ef3⟩ := by
    apply X86Routine.Prefix.step (middle := ⟨c1,none,0x30ebe⟩)
      (by change ¬((0x30ebb:Nat) ∈ [0x30ef3]); decide)
      (show listed 0x30ebb = some (.multiplyImmediate 2 2 28,3) from by decide) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,put,write,blockPreservesFlags,h.state,p.indexNonzero,p.ticsNonzero,Entry.pointer,logical32,compare32,tableLoad,fields,PainSetter.fields,tableWords,Entry.pointer,load_store_apart _ _ _ _ ti.1,load_store_apart _ _ _ _ ti.2,load_store,ht_sprite,ht_frame,ht_tics,ht_action,ht_next,prologueEnd,savedMemory,c1,c0])
    apply X86Routine.Prefix.step (middle := ⟨c2,none,0x30ec4⟩)
      (by change ¬((0x30ebe:Nat) ∈ [0x30ef3]); decide)
      (show listed 0x30ebe = some (.addImmediate 2 0x15a28,6) from by decide) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,put,write,blockPreservesFlags,h.state,p.indexNonzero,p.ticsNonzero,Entry.pointer,logical32,compare32,tableLoad,fields,PainSetter.fields,tableWords,Entry.pointer,load_store_apart _ _ _ _ ti.1,load_store_apart _ _ _ _ ti.2,load_store,ht_sprite,ht_frame,ht_tics,ht_action,ht_next,prologueEnd,savedMemory,c2,c1,c0])
    apply X86Routine.Prefix.step (middle := ⟨c3,none,0x30ec7⟩)
      (by change ¬((0x30ec4:Nat) ∈ [0x30ef3]); decide)
      (show listed 0x30ec4 = some (.control (.block (.store ⟨some 3,none,0,100⟩ 2)),3) from by decide) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,put,write,blockPreservesFlags,h.state,p.indexNonzero,p.ticsNonzero,Entry.pointer,logical32,compare32,tableLoad,fields,PainSetter.fields,tableWords,Entry.pointer,load_store_apart _ _ _ _ ti.1,load_store_apart _ _ _ _ ti.2,load_store,ht_sprite,ht_frame,ht_tics,ht_action,ht_next,prologueEnd,savedMemory,c3,c2,c1,c0])
    apply X86Routine.Prefix.step (middle := ⟨c4,none,0x30eca⟩)
      (by change ¬((0x30ec7:Nat) ∈ [0x30ef3]); decide)
      (show listed 0x30ec7 = some (.control (.block (.legacy (.load 0 2 8))),3) from by decide) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,put,write,blockPreservesFlags,h.state,p.indexNonzero,p.ticsNonzero,Entry.pointer,logical32,compare32,tableLoad,fields,PainSetter.fields,tableWords,Entry.pointer,load_store_apart _ _ _ _ ti.1,load_store_apart _ _ _ _ ti.2,load_store,ht_sprite,ht_frame,ht_tics,ht_action,ht_next,prologueEnd,savedMemory,c4,c3,c2,c1,c0])
    apply X86Routine.Prefix.step (middle := ⟨c5,none,0x30ecd⟩)
      (by change ¬((0x30eca:Nat) ∈ [0x30ef3]); decide)
      (show listed 0x30eca = some (.control (.block (.store ⟨some 3,none,0,96⟩ 0)),3) from by decide) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,put,write,blockPreservesFlags,h.state,p.indexNonzero,p.ticsNonzero,Entry.pointer,logical32,compare32,tableLoad,fields,PainSetter.fields,tableWords,Entry.pointer,load_store_apart _ _ _ _ ti.1,load_store_apart _ _ _ _ ti.2,load_store,ht_sprite,ht_frame,ht_tics,ht_action,ht_next,prologueEnd,savedMemory,c5,c4,c3,c2,c1,c0])
    apply X86Routine.Prefix.step (middle := ⟨c6,none,0x30ecf⟩)
      (by change ¬((0x30ecd:Nat) ∈ [0x30ef3]); decide)
      (show listed 0x30ecd = some (.control (.block (.legacy (.load 0 2 0))),2) from by decide) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,put,write,blockPreservesFlags,h.state,p.indexNonzero,p.ticsNonzero,Entry.pointer,logical32,compare32,tableLoad,fields,PainSetter.fields,tableWords,Entry.pointer,load_store_apart _ _ _ _ ti.1,load_store_apart _ _ _ _ ti.2,load_store,ht_sprite,ht_frame,ht_tics,ht_action,ht_next,prologueEnd,savedMemory,c6,c5,c4,c3,c2,c1,c0])
    apply X86Routine.Prefix.step (middle := ⟨c7,none,0x30ed2⟩)
      (by change ¬((0x30ecf:Nat) ∈ [0x30ef3]); decide)
      (show listed 0x30ecf = some (.control (.block (.store ⟨some 3,none,0,36⟩ 0)),3) from by decide) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,put,write,blockPreservesFlags,h.state,p.indexNonzero,p.ticsNonzero,Entry.pointer,logical32,compare32,tableLoad,fields,PainSetter.fields,tableWords,Entry.pointer,load_store_apart _ _ _ _ ti.1,load_store_apart _ _ _ _ ti.2,load_store,ht_sprite,ht_frame,ht_tics,ht_action,ht_next,prologueEnd,savedMemory,c7,c6,c5,c4,c3,c2,c1,c0])
    apply X86Routine.Prefix.step (middle := ⟨c8,none,0x30ed5⟩)
      (by change ¬((0x30ed2:Nat) ∈ [0x30ef3]); decide)
      (show listed 0x30ed2 = some (.control (.block (.legacy (.load 0 2 4))),3) from by decide) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,put,write,blockPreservesFlags,h.state,p.indexNonzero,p.ticsNonzero,Entry.pointer,logical32,compare32,tableLoad,fields,PainSetter.fields,tableWords,Entry.pointer,load_store_apart _ _ _ _ ti.1,load_store_apart _ _ _ _ ti.2,load_store,ht_sprite,ht_frame,ht_tics,ht_action,ht_next,prologueEnd,savedMemory,c8,c7,c6,c5,c4,c3,c2,c1,c0])
    apply X86Routine.Prefix.step (middle := ⟨c9,none,0x30ed8⟩)
      (by change ¬((0x30ed5:Nat) ∈ [0x30ef3]); decide)
      (show listed 0x30ed5 = some (.control (.block (.store ⟨some 3,none,0,40⟩ 0)),3) from by decide) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,put,write,blockPreservesFlags,h.state,p.indexNonzero,p.ticsNonzero,Entry.pointer,logical32,compare32,tableLoad,fields,PainSetter.fields,tableWords,Entry.pointer,load_store_apart _ _ _ _ ti.1,load_store_apart _ _ _ _ ti.2,load_store,ht_sprite,ht_frame,ht_tics,ht_action,ht_next,prologueEnd,savedMemory,c9,c8,c7,c6,c5,c4,c3,c2,c1,c0])
    apply X86Routine.Prefix.step (middle := ⟨c10,some (compare32 0 0),0x30edc⟩)
      (by change ¬((0x30ed8:Nat) ∈ [0x30ef3]); decide)
      (show listed 0x30ed8 = some (.control (.cmpImmediate ⟨some 2,none,0,12⟩ 0),4) from by decide) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,put,write,blockPreservesFlags,h.state,p.indexNonzero,p.ticsNonzero,Entry.pointer,logical32,compare32,tableLoad,fields,PainSetter.fields,tableWords,Entry.pointer,load_store_apart _ _ _ _ ti.1,load_store_apart _ _ _ _ ti.2,load_store,ht_sprite,ht_frame,ht_tics,ht_action,ht_next,prologueEnd,savedMemory,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,c0])
    apply X86Routine.Prefix.step (middle := ⟨c11,some (compare32 0 0),0x30ee3⟩)
      (by change ¬((0x30edc:Nat) ∈ [0x30ef3]); decide)
      (show listed 0x30edc = some (.control (.jumpZero true 5),2) from by decide) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,put,write,blockPreservesFlags,h.state,p.indexNonzero,p.ticsNonzero,Entry.pointer,logical32,compare32,tableLoad,fields,PainSetter.fields,tableWords,Entry.pointer,load_store_apart _ _ _ _ ti.1,load_store_apart _ _ _ _ ti.2,load_store,ht_sprite,ht_frame,ht_tics,ht_action,ht_next,prologueEnd,savedMemory,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,c0])
    apply X86Routine.Prefix.step (middle := ⟨c12,some (compare32 0 0),0x30ee6⟩)
      (by change ¬((0x30ee3:Nat) ∈ [0x30ef3]); decide)
      (show listed 0x30ee3 = some (.control (.block (.legacy (.load 6 3 96))),3) from by decide) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,put,write,blockPreservesFlags,h.state,p.indexNonzero,p.ticsNonzero,Entry.pointer,logical32,compare32,tableLoad,fields,PainSetter.fields,tableWords,Entry.pointer,load_store_apart _ _ _ _ ti.1,load_store_apart _ _ _ _ ti.2,load_store,ht_sprite,ht_frame,ht_tics,ht_action,ht_next,prologueEnd,savedMemory,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,c0])
    apply X86Routine.Prefix.step (middle := ⟨c13,some (compare32 0 0),0x30ee9⟩)
      (by change ¬((0x30ee6:Nat) ∈ [0x30ef3]); decide)
      (show listed 0x30ee6 = some (.control (.block (.legacy (.load 2 2 16))),3) from by decide) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,put,write,blockPreservesFlags,h.state,p.indexNonzero,p.ticsNonzero,Entry.pointer,logical32,compare32,tableLoad,fields,PainSetter.fields,tableWords,Entry.pointer,load_store_apart _ _ _ _ ti.1,load_store_apart _ _ _ _ ti.2,load_store,ht_sprite,ht_frame,ht_tics,ht_action,ht_next,prologueEnd,savedMemory,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,c0])
    apply X86Routine.Prefix.step (middle := ⟨c14,some (logical32 p.tics),0x30eeb⟩)
      (by change ¬((0x30ee9:Nat) ∈ [0x30ef3]); decide)
      (show listed 0x30ee9 = some (.control (.testWord 6 6),2) from by decide) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,put,write,blockPreservesFlags,h.state,p.indexNonzero,p.ticsNonzero,Entry.pointer,logical32,compare32,tableLoad,fields,PainSetter.fields,tableWords,Entry.pointer,load_store_apart _ _ _ _ ti.1,load_store_apart _ _ _ _ ti.2,load_store,ht_sprite,ht_frame,ht_tics,ht_action,ht_next,prologueEnd,savedMemory,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,c0])
    apply X86Routine.Prefix.step (middle := ⟨c15,some (logical32 p.tics),0x30ef3⟩)
      (by change ¬((0x30eeb:Nat) ∈ [0x30ef3]); decide)
      (show listed 0x30eeb = some (.control (.jumpZero false 6),2) from by decide) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,put,write,blockPreservesFlags,h.state,p.indexNonzero,p.ticsNonzero,Entry.pointer,logical32,compare32,tableLoad,fields,PainSetter.fields,tableWords,Entry.pointer,load_store_apart _ _ _ _ ti.1,load_store_apart _ _ _ _ ti.2,load_store,ht_sprite,ht_frame,ht_tics,ht_action,ht_next,prologueEnd,savedMemory,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,c0])
    exact X86Routine.Prefix.nil _
  rw [show 15 = 15+0 from rfl,path.run 0]
  simp [X86Routine.run,bodyEnd,entryMemory,prologueEnd,put,write,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,c0]
  funext r
  by_cases h0 : r = 0 <;> by_cases h2 : r = 2 <;> by_cases h3 : r = 3 <;>
    by_cases h4 : r = 4 <;> by_cases h6 : r = 6 <;> simp_all [write]

theorem setter_epilogue (p : Entry) (s : X86Memory.State) (h : SetterInputs p s) :
    X86Routine.run listed [0x2a3f1] 4 (bodyEnd p s) = some (setterEnd p s) := by
  have ht_sprite := h.table.sprite
  simp [Entry.pointer] at ht_sprite
  have ht_frame := h.table.frame
  simp [Entry.pointer] at ht_frame
  have ht_tics := h.table.tics
  simp [Entry.pointer] at ht_tics
  have ht_action := h.table.action
  simp [Entry.pointer] at ht_action
  have ht_next := h.table.next
  simp [Entry.pointer] at ht_next

  have tableLoad (m : Memory) (a b v : Word) (ha : a ∈ tableWords p)
      (hb : b ∈ fields (s.regs 0) ++ [s.regs 4-(4#32),s.regs 4-(8#32)]) :=
    load_store_apart m b a v (h.tableSafe a ha b hb)
  have stackLoad (m : Memory) (a b v : Word)
      (ha : a ∈ [s.regs 4,s.regs 4-(4#32),s.regs 4-(8#32)]) (hb : b ∈ fields (s.regs 0)) :=
    load_store_apart m b a v (h.stackSafe a ha b hb)
  have st := stack_apart (s.regs 4)
  have ti := tics_apart (s.regs 0)
  have addback : s.regs 4-(8#32)+(4#32) = s.regs 4-(4#32) := by simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  let c0 := (bodyEnd p s).core
  let c1 : X86Memory.State := put c0 0 1
  let c2 : X86Memory.State := put (put c1 4 (s.regs 4-4)) 6 (s.regs 6)
  let c3 : X86Memory.State := put (put c2 4 (s.regs 4)) 3 (s.regs 3)
  let c4 : X86Memory.State := put c3 4 (s.regs 4+4)
  have path : X86Routine.Prefix listed [0x2a3f1] 4 (bodyEnd p s) ⟨c4,some (logical32 p.tics),0x2a3f1⟩ := by
    apply X86Routine.Prefix.step (middle := ⟨c1,some (logical32 p.tics),0x30ef8⟩)
      (by change ¬((0x30ef3:Nat) ∈ [0x2a3f1]); decide)
      (show listed 0x30ef3 = some (.immediate 0 1,5) from by decide) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,
    X86Memory.execute,X86Block.Address.eval,X86Routine.pushWord,put,write,
    blockPreservesFlags,logical32,compare32,h.state,p.indexNonzero,p.ticsNonzero,Entry.pointer,BitVec.sub_sub,addback,BitVec.sub_add_cancel,tableLoad,stackLoad,
    fields,PainSetter.fields,tableWords,Entry.pointer,load_store_apart _ _ _ _ st.1,load_store_apart _ _ _ _ st.2.1,
    load_store_apart _ _ _ _ st.2.2,load_store_apart _ _ _ _ ti.1,
    load_store_apart _ _ _ _ ti.2,load_store,ht_sprite,ht_frame,ht_tics,
    ht_action,ht_next,h.returnAddress,bodyEnd,setterEnd,entryMemory,savedMemory,eax,c1,c0])
    apply X86Routine.Prefix.step (middle := ⟨c2,some (logical32 p.tics),0x30ef9⟩)
      (by change ¬((0x30ef8:Nat) ∈ [0x2a3f1]); decide)
      (show listed 0x30ef8 = some (.pop 6,1) from by decide) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,
    X86Memory.execute,X86Block.Address.eval,X86Routine.pushWord,put,write,
    blockPreservesFlags,logical32,compare32,h.state,p.indexNonzero,p.ticsNonzero,Entry.pointer,BitVec.sub_sub,addback,BitVec.sub_add_cancel,tableLoad,stackLoad,
    fields,PainSetter.fields,tableWords,Entry.pointer,load_store_apart _ _ _ _ st.1,load_store_apart _ _ _ _ st.2.1,
    load_store_apart _ _ _ _ st.2.2,load_store_apart _ _ _ _ ti.1,
    load_store_apart _ _ _ _ ti.2,load_store,ht_sprite,ht_frame,ht_tics,
    ht_action,ht_next,h.returnAddress,bodyEnd,setterEnd,entryMemory,savedMemory,eax,c2,c1,c0])
    apply X86Routine.Prefix.step (middle := ⟨c3,some (logical32 p.tics),0x30efa⟩)
      (by change ¬((0x30ef9:Nat) ∈ [0x2a3f1]); decide)
      (show listed 0x30ef9 = some (.pop 3,1) from by decide) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,
    X86Memory.execute,X86Block.Address.eval,X86Routine.pushWord,put,write,
    blockPreservesFlags,logical32,compare32,h.state,p.indexNonzero,p.ticsNonzero,Entry.pointer,BitVec.sub_sub,addback,BitVec.sub_add_cancel,tableLoad,stackLoad,
    fields,PainSetter.fields,tableWords,Entry.pointer,load_store_apart _ _ _ _ st.1,load_store_apart _ _ _ _ st.2.1,
    load_store_apart _ _ _ _ st.2.2,load_store_apart _ _ _ _ ti.1,
    load_store_apart _ _ _ _ ti.2,load_store,ht_sprite,ht_frame,ht_tics,
    ht_action,ht_next,h.returnAddress,bodyEnd,setterEnd,entryMemory,savedMemory,eax,c3,c2,c1,c0])
    apply X86Routine.Prefix.step (middle := ⟨c4,some (logical32 p.tics),0x2a3f1⟩)
      (by change ¬((0x30efa:Nat) ∈ [0x2a3f1]); decide)
      (show listed 0x30efa = some (.ret,1) from by decide) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,
    X86Memory.execute,X86Block.Address.eval,X86Routine.pushWord,put,write,
    blockPreservesFlags,logical32,compare32,h.state,p.indexNonzero,p.ticsNonzero,Entry.pointer,BitVec.sub_sub,addback,BitVec.sub_add_cancel,tableLoad,stackLoad,
    fields,PainSetter.fields,tableWords,Entry.pointer,load_store_apart _ _ _ _ st.1,load_store_apart _ _ _ _ st.2.1,
    load_store_apart _ _ _ _ st.2.2,load_store_apart _ _ _ _ ti.1,
    load_store_apart _ _ _ _ ti.2,load_store,ht_sprite,ht_frame,ht_tics,
    ht_action,ht_next,h.returnAddress,bodyEnd,setterEnd,entryMemory,savedMemory,eax,c4,c3,c2,c1,c0])
    exact X86Routine.Prefix.nil _
  rw [show 4 = 4+0 from rfl,path.run 0]
  simp [X86Routine.run,setterEnd,bodyEnd,put,write,c4,c3,c2,c1,c0]
  funext r
  by_cases h0 : r = 0 <;> by_cases h2 : r = 2 <;> by_cases h3 : r = 3 <;>
    by_cases h4 : r = 4 <;> by_cases h6 : r = 6 <;> simp_all [write]

theorem exit_active (pc : Nat) (h : listed pc ≠ none) : pc ∉ [0x2a3f1] := by
  simp only [List.mem_singleton]
  intro eq; subst pc
  exact h (by rfl)

theorem setter_program (p : Entry) (s : X86Memory.State) (flags : Option Flags) (h : SetterInputs p s) :
    X86Routine.run listed [0x2a3f1] 24 ⟨s,flags,0x30ea0⟩ = some (setterEnd p s) := by
  obtain ⟨k,hk,path,_⟩ := X86Routine.run_path (setter_prologue p s flags h.state)
  obtain ⟨j,hj,q,_⟩ := X86Routine.run_path (setter_body p s h)
  have path := path.transfer listed [0x2a3f1] (fun _ _ => rfl) exit_active
  have q := q.transfer listed [0x2a3f1] (fun _ _ => rfl) exit_active
  have tail := q.finish (setter_epilogue p s h) 19 (by omega)
  exact path.finish tail 24 (by omega)


theorem original_execution (p : Entry) (s : X86Memory.State) (f : Option Flags) (h : SetterInputs p s) :
    X86Routine.run program [0x2a3f1] 24 ⟨s,f,0x30ea0⟩ = some (setterEnd p s) := by
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [setter_program p s f h]; simp)]
  exact setter_program p s f h

def writes (s : X86Memory.State) := fields (s.regs 0) ++ [s.regs 4-(4#32),s.regs 4-(8#32)]
theorem memory_frame (p : Entry) (s : X86Memory.State) :
    PlayerHeight.Frame s.memory (setterEnd p s).core.memory (writes s) := by
  intro a safe
  unfold setterEnd entryMemory savedMemory
  repeat rw [load_store_apart _ _ _ _ (safe _ (by simp [writes,fields,PainSetter.fields]))]

def observeFields (m : Memory) (obj : Word) :=
  (load32 m (obj+(100#32)),load32 m (obj+(96#32)),load32 m (obj+(36#32)),load32 m (obj+(40#32)))

theorem entry_fields (p : Entry) (m : Memory) (obj : Word) :
    observeFields (entryMemory p m obj) obj = (p.pointer,p.tics,p.sprite,p.frame) := by
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


end Doom.Proofs.DeathSetter
