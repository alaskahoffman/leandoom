import Doom.Proofs.E1M1GroupOutput
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
open Doom.Verification Doom.Proofs X86 X86Memory X86Control BlockSummary
open OriginalGroupStep OriginalGroupScan OriginalGroupFrame OriginalGroupOutput
local instance (a b : Word) : Decidable (Apart a b) := by unfold Apart; infer_instance
local instance (a sp : Word) : Decidable (StackApart a sp) :=
  decidable_of_iff (Apart a (sp-4) ∧ Apart a sp ∧ Apart a (sp+4) ∧ Apart a (sp+8) ∧ Apart a (sp+12))
    ⟨fun h => ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩,fun h => ⟨h.ret,h.top,h.bottom,h.left,h.right⟩⟩
def lines : List OriginalGroupOutput.Line :=
  [⟨0x601000,0x620000,0⟩,⟨0x60103e,0x620080,0x620000⟩,
   ⟨0x60107c,0x620000,0x620000⟩,⟨0x6010ba,0x620080,0⟩]
def initial : X86Memory.State :=
  let m : Memory := fun _ => 0
  let m := store32 m 0x2c120 0x601000
  let m := store32 m 0x2c134 0x4
  let m := store32 m 0x62004e 0x3
  let m := store32 m 0x620052 0xdeadbeef
  let m := store32 m 0x600800 0x80000000
  let m := store32 m 0x600804 0x7fffffff
  let m := store32 m 0x600808 0x7fffffff
  let m := store32 m 0x60080c 0x80000000
  let m := store32 m 0x601000 0x610000
  let m := store32 m 0x601004 0x610008
  let m := store32 m 0x60102e 0x620000
  let m := store32 m 0x601032 0x0
  let m := store32 m 0x610000 0x0
  let m := store32 m 0x610004 0x1
  let m := store32 m 0x610008 0x2
  let m := store32 m 0x61000c 0x3
  let m := store32 m 0x60103e 0x610010
  let m := store32 m 0x601042 0x610018
  let m := store32 m 0x60106c 0x620080
  let m := store32 m 0x601070 0x620000
  let m := store32 m 0x610010 0x4
  let m := store32 m 0x610014 0x5
  let m := store32 m 0x610018 0x6
  let m := store32 m 0x61001c 0x7
  let m := store32 m 0x60107c 0x610020
  let m := store32 m 0x601080 0x610028
  let m := store32 m 0x6010aa 0x620000
  let m := store32 m 0x6010ae 0x620000
  let m := store32 m 0x610020 0x8
  let m := store32 m 0x610024 0x9
  let m := store32 m 0x610028 0xa
  let m := store32 m 0x61002c 0xb
  let m := store32 m 0x6010ba 0x610030
  let m := store32 m 0x6010be 0x610038
  let m := store32 m 0x6010e8 0x620080
  let m := store32 m 0x6010ec 0x0
  let m := store32 m 0x610030 0xc
  let m := store32 m 0x610034 0xd
  let m := store32 m 0x610038 0xe
  let m := store32 m 0x61003c 0xf
  ⟨fun r => if r=4 then 0x600800 else if r=5 then 0x620000 else if r=6 then 0x618000 else 0,m⟩
private theorem safe (a : Word) (hs : StackApart a 0x600800)
    (ho : ∀ j : Fin 4, Apart a (cursor 0x618000 j.val)) : SafeWord a 0x600800 0x618000 4 :=
  ⟨hs,fun j hj => ho ⟨j,hj⟩⟩
private theorem storage : Storage lines 0x600800 0x618000 := by
  constructor
  · have h : ∀ j : Fin 4, StackApart (cursor 0x618000 j.val) 0x600800 := by decide +kernel
    intro j hj; exact h ⟨j,hj⟩
  · have h : ∀ i j : Fin 4, i.val≠j.val → Apart (cursor 0x618000 i.val) (cursor 0x618000 j.val) := by decide +kernel
    intro i hi j hj ne; exact h ⟨i,hi⟩ ⟨j,hj⟩ ne
  · intro e he
    simp only [lines,List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl|rfl|rfl|rfl
    all_goals exact safe _ (by decide +kernel) (by decide +kernel)
  · intro e he
    simp only [lines,List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl|rfl|rfl|rfl
    all_goals exact safe _ (by decide +kernel) (by decide +kernel)
private theorem layout : Layout 4 0x600800 0x618000 := by
  constructor
  · decide
  · constructor <;> decide +kernel
  · have h : ∀ j : Fin 4, Apart 0x2c134 (cursor 0x618000 j.val) := by decide +kernel
    intro j hj; exact h ⟨j,hj⟩
private theorem inputs : Inputs lines initial.memory := by unfold Inputs; decide +kernel
private theorem linked : Linked lines (load32 initial.memory 0x2c120) := by
  simp only [lines,Linked]; decide +kernel
-- Full entry/scan execution derives this representation; it is not a premise.
example : ∃ out, X86Routine.run program [0x2e6af] 178 ⟨initial,none,0x2e661⟩=some out ∧
    out.pc=0x2e6af ∧ E1M1NoiseMap.Rep
      ⟨0x620000,0x618000,[0x601000,0x60103e,0x60107c]⟩ out.core.memory := by
  exact entry_rep lines initial none layout storage inputs linked (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (safe _ (by decide +kernel) (by decide +kernel))
    (safe _ (by decide +kernel) (by decide +kernel)) (by decide)
-- Concrete readback makes ordering, single self-edge emission, and the untouched
-- fourth output slot visible without depending on function equality decidability.
def finalState := after 4 (OriginalGroupLines.entry initial).core
example : load32 finalState.memory 0x618000=0x601000 ∧
    load32 finalState.memory 0x618004=0x60103e ∧
    load32 finalState.memory 0x618008=0x60107c ∧
    load32 finalState.memory 0x61800c=0 ∧
    load32 finalState.memory (0x620000+82)=0x618000 ∧
    load32 finalState.memory (0x620000+78)=3 := by decide +kernel
