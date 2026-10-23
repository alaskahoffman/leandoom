import Doom.Proofs.OriginalDeathSetter
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.ActorSetterReturn
open Verification X86 X86Memory X86Control BlockSummary DeathSetter

/-- Reusable non-null/no-action/nonzero-tic setter with an arbitrary actual
return address. The earlier death caller retains its default address. -/
def result (p : Entry) (s : X86Memory.State) (ret : Word) : X86Control.State :=
  ⟨⟨write (write (write s.regs 0 1) 2 p.next) 4 (s.regs 4+(4#32)),
    entryMemory p (savedMemory s) (s.regs 0)⟩,some (logical32 p.tics),ret.toNat⟩

theorem epilogue (p : Entry) (s : X86Memory.State) (ret : Word) (h : SetterInputs p s ret) :
    X86Routine.Prefix program [] 4 (bodyEnd p s) (result p s ret) := by
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
  have path : X86Routine.Prefix listed [] 4 (bodyEnd p s) ⟨c4,some (logical32 p.tics),ret.toNat⟩ := by
    apply X86Routine.Prefix.step (middle := ⟨c1,some (logical32 p.tics),0x30ef8⟩)
      (by simp)
      (show listed 0x30ef3 = some (.immediate 0 1,5) from by decide) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,
    X86Memory.execute,X86Block.Address.eval,X86Routine.pushWord,put,write,
    blockPreservesFlags,logical32,compare32,h.state,p.indexNonzero,p.ticsNonzero,Entry.pointer,BitVec.sub_sub,addback,BitVec.sub_add_cancel,tableLoad,stackLoad,
    fields,PainSetter.fields,tableWords,Entry.pointer,load_store_apart _ _ _ _ st.1,load_store_apart _ _ _ _ st.2.1,
    load_store_apart _ _ _ _ st.2.2,load_store_apart _ _ _ _ ti.1,
    load_store_apart _ _ _ _ ti.2,load_store,ht_sprite,ht_frame,ht_tics,
    ht_action,ht_next,h.returnAddress,bodyEnd,setterEnd,entryMemory,savedMemory,eax,c1,c0])
    apply X86Routine.Prefix.step (middle := ⟨c2,some (logical32 p.tics),0x30ef9⟩)
      (by simp)
      (show listed 0x30ef8 = some (.pop 6,1) from by decide) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,
    X86Memory.execute,X86Block.Address.eval,X86Routine.pushWord,put,write,
    blockPreservesFlags,logical32,compare32,h.state,p.indexNonzero,p.ticsNonzero,Entry.pointer,BitVec.sub_sub,addback,BitVec.sub_add_cancel,tableLoad,stackLoad,
    fields,PainSetter.fields,tableWords,Entry.pointer,load_store_apart _ _ _ _ st.1,load_store_apart _ _ _ _ st.2.1,
    load_store_apart _ _ _ _ st.2.2,load_store_apart _ _ _ _ ti.1,
    load_store_apart _ _ _ _ ti.2,load_store,ht_sprite,ht_frame,ht_tics,
    ht_action,ht_next,h.returnAddress,bodyEnd,setterEnd,entryMemory,savedMemory,eax,c2,c1,c0])
    apply X86Routine.Prefix.step (middle := ⟨c3,some (logical32 p.tics),0x30efa⟩)
      (by simp)
      (show listed 0x30ef9 = some (.pop 3,1) from by decide) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,
    X86Memory.execute,X86Block.Address.eval,X86Routine.pushWord,put,write,
    blockPreservesFlags,logical32,compare32,h.state,p.indexNonzero,p.ticsNonzero,Entry.pointer,BitVec.sub_sub,addback,BitVec.sub_add_cancel,tableLoad,stackLoad,
    fields,PainSetter.fields,tableWords,Entry.pointer,load_store_apart _ _ _ _ st.1,load_store_apart _ _ _ _ st.2.1,
    load_store_apart _ _ _ _ st.2.2,load_store_apart _ _ _ _ ti.1,
    load_store_apart _ _ _ _ ti.2,load_store,ht_sprite,ht_frame,ht_tics,
    ht_action,ht_next,h.returnAddress,bodyEnd,setterEnd,entryMemory,savedMemory,eax,c3,c2,c1,c0])
    apply X86Routine.Prefix.step (middle := ⟨c4,some (logical32 p.tics),ret.toNat⟩)
      (by simp)
      (show listed 0x30efa = some (.ret,1) from by decide) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,
    X86Memory.execute,X86Block.Address.eval,X86Routine.pushWord,put,write,
    blockPreservesFlags,logical32,compare32,h.state,p.indexNonzero,p.ticsNonzero,Entry.pointer,BitVec.sub_sub,addback,BitVec.sub_add_cancel,tableLoad,stackLoad,
    fields,PainSetter.fields,tableWords,Entry.pointer,load_store_apart _ _ _ _ st.1,load_store_apart _ _ _ _ st.2.1,
    load_store_apart _ _ _ _ st.2.2,load_store_apart _ _ _ _ ti.1,
    load_store_apart _ _ _ _ ti.2,load_store,ht_sprite,ht_frame,ht_tics,
    ht_action,ht_next,h.returnAddress,bodyEnd,setterEnd,entryMemory,savedMemory,eax,c4,c3,c2,c1,c0])
    exact X86Routine.Prefix.nil _
  have eq : (⟨c4,some (logical32 p.tics),ret.toNat⟩ : X86Control.State)=result p s ret := by
    simp [result,bodyEnd,put,write,c4,c3,c2,c1,c0]
    funext r
    by_cases h0 : r = 0 <;> by_cases h2 : r = 2 <;> by_cases h3 : r = 3 <;>
      by_cases h4 : r = 4 <;> by_cases h6 : r = 6 <;> simp_all [write]
  rw [eq] at path
  exact path.transfer program [] decoded (by simp)

private theorem prefix_trans {p stops n m s t u}
    (a : X86Routine.Prefix p stops n s t) (b : X86Routine.Prefix p stops m t u) :
    X86Routine.Prefix p stops (n+m) s u := by
  induction a with
  | nil => simpa using b
  | @step n s middle last op len active decoded executed rest ih =>
    simpa only [Nat.succ_add] using X86Routine.Prefix.step active decoded executed (ih b)

theorem execution (p : Entry) (s : X86Memory.State) (f : Option Flags) (ret : Word)
    (h : SetterInputs p s ret) :
    ∃ n, n≤24 ∧ X86Routine.Prefix program [] n ⟨s,f,0x30ea0⟩ (result p s ret) := by
  obtain ⟨n,hn,a,_⟩ := X86Routine.run_path (setter_prologue p s f h.state)
  obtain ⟨m,hm,b,_⟩ := X86Routine.run_path (setter_body p s h)
  have a := a.transfer program [] decoded (by simp)
  have b := b.transfer program [] decoded (by simp)
  exact ⟨n+m+4,by omega,prefix_trans (prefix_trans a b) (epilogue p s ret h)⟩

theorem memory_frame (p : Entry) (s : X86Memory.State) (ret : Word) :
    PlayerHeight.Frame s.memory (result p s ret).core.memory (writes s) :=
  DeathSetter.memory_frame p s

theorem fields (p : Entry) (s : X86Memory.State) (ret : Word) :
    observeFields (result p s ret).core.memory (s.regs 0)=(p.pointer,p.tics,p.sprite,p.frame) :=
  entry_fields p (savedMemory s) (s.regs 0)
end Doom.Proofs.ActorSetterReturn
