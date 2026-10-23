import Doom.Proofs.OriginalHeightJoined

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000
namespace Doom.Proofs.PlayerHeight.Function
open Verification X86 X86Memory X86Control BlockSummary

/-- Complete listing: the body is return-free, while RET keeps its absolute
stack-supplied PC when the body is relocated into a caller. -/
def program : X86Routine.Program := fun pc =>
  if pc = 301 then some (.ret,1) else PlayerHeight.program pc

theorem contains_body (pc : Nat) (h : PlayerHeight.program pc ≠ none) :
    program pc = PlayerHeight.program pc := by
  have hn : pc ≠ 301 := by intro e; subst pc; contradiction
  simp only [program,hn,↓reduceIte]

theorem decoded (pc : Nat) (h : program pc ≠ none) :
    X86Routine.decodeAt code pc = program pc := by
  by_cases he : pc = 301
  · subst pc; rfl
  · simp only [program,he,↓reduceIte] at h ⊢
    exact PlayerHeight.decoded pc h

theorem write_shadow (rs : Registers) (i : Reg) (a b : Word) :
    write (write rs i a) i b = write rs i b := by
  funext j; by_cases h : j = i <;> simp [write,h]

def saved (s : X86Memory.State) : Memory :=
  store32 (store32 (store32 (store32 (store32 (store32 s.memory
    (s.regs 4-(4#32)) (s.regs 3)) (s.regs 4-(8#32)) (s.regs 1))
    (s.regs 4-(12#32)) (s.regs 2)) (s.regs 4-(16#32)) (s.regs 6))
    (s.regs 4-(20#32)) (s.regs 7)) (s.regs 4-(24#32)) (s.regs 5)

def savedSlots (s : X86Memory.State) : List Word :=
  [s.regs 4,s.regs 4-(4#32),s.regs 4-(8#32),s.regs 4-(12#32),
   s.regs 4-(16#32),s.regs 4-(20#32),s.regs 4-(24#32)]

def pushSlots (s : X86Memory.State) : List Word := (savedSlots s).tail

theorem saved_load (s : X86Memory.State) (a : Word)
    (safe : ∀ b, b ∈ pushSlots s → Apart a b) : load32 (saved s) a = load32 s.memory a := by
  unfold saved
  rw [load_store_apart _ _ _ _ (safe _ (by simp [pushSlots,savedSlots])),
      load_store_apart _ _ _ _ (safe _ (by simp [pushSlots,savedSlots])),
      load_store_apart _ _ _ _ (safe _ (by simp [pushSlots,savedSlots])),
      load_store_apart _ _ _ _ (safe _ (by simp [pushSlots,savedSlots])),
      load_store_apart _ _ _ _ (safe _ (by simp [pushSlots,savedSlots])),
      load_store_apart _ _ _ _ (safe _ (by simp [pushSlots,savedSlots]))]

/-- Distinct aligned word slots remain disjoint even across 32-bit wraparound. -/
theorem slots_apart (sp : Word) (i j : Fin 11) (hne : i ≠ j) :
    Apart (sp-BitVec.ofNat 32 (i.val*4)) (sp-BitVec.ofNat 32 (j.val*4)) := by
  have checked : ∀ i j : Fin 11, i ≠ j →
      Apart (-BitVec.ofNat 32 (i.val*4)) (-BitVec.ofNat 32 (j.val*4)) := by unfold Apart; decide
  intro a b eq
  apply checked i j hne a b
  apply (BitVec.add_right_inj sp).mp
  simpa only [BitVec.sub_eq_add_neg,BitVec.add_assoc] using eq

theorem saved_return (s : X86Memory.State) : load32 (saved s) (s.regs 4) = load32 s.memory (s.regs 4) := by
  apply saved_load
  intro b hb
  simp only [pushSlots,savedSlots,List.tail_cons,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h|h|h|h|h|h <;> subst b
  · have h := slots_apart (s.regs 4) 0 1 (by decide)
    change Apart (s.regs 4-(0#32)) (s.regs 4-(4#32)) at h
    simpa only [BitVec.sub_zero] using h
  · have h := slots_apart (s.regs 4) 0 2 (by decide)
    change Apart (s.regs 4-(0#32)) (s.regs 4-(8#32)) at h
    simpa only [BitVec.sub_zero] using h
  · have h := slots_apart (s.regs 4) 0 3 (by decide)
    change Apart (s.regs 4-(0#32)) (s.regs 4-(12#32)) at h
    simpa only [BitVec.sub_zero] using h
  · have h := slots_apart (s.regs 4) 0 4 (by decide)
    change Apart (s.regs 4-(0#32)) (s.regs 4-(16#32)) at h
    simpa only [BitVec.sub_zero] using h
  · have h := slots_apart (s.regs 4) 0 5 (by decide)
    change Apart (s.regs 4-(0#32)) (s.regs 4-(20#32)) at h
    simpa only [BitVec.sub_zero] using h
  · have h := slots_apart (s.regs 4) 0 6 (by decide)
    change Apart (s.regs 4-(0#32)) (s.regs 4-(24#32)) at h
    simpa only [BitVec.sub_zero] using h

theorem saved_registers (s : X86Memory.State) :
    (load32 (saved s) (s.regs 4-(4#32)),load32 (saved s) (s.regs 4-(8#32)),
     load32 (saved s) (s.regs 4-(12#32)),load32 (saved s) (s.regs 4-(16#32)),
     load32 (saved s) (s.regs 4-(20#32)),load32 (saved s) (s.regs 4-(24#32))) =
    (s.regs 3,s.regs 1,s.regs 2,s.regs 6,s.regs 7,s.regs 5) := by
  have k12 : Apart (s.regs 4-(4#32)) (s.regs 4-(8#32)) := slots_apart (s.regs 4) 1 2 (by decide)
  have k13 : Apart (s.regs 4-(4#32)) (s.regs 4-(12#32)) := slots_apart (s.regs 4) 1 3 (by decide)
  have k14 : Apart (s.regs 4-(4#32)) (s.regs 4-(16#32)) := slots_apart (s.regs 4) 1 4 (by decide)
  have k15 : Apart (s.regs 4-(4#32)) (s.regs 4-(20#32)) := slots_apart (s.regs 4) 1 5 (by decide)
  have k16 : Apart (s.regs 4-(4#32)) (s.regs 4-(24#32)) := slots_apart (s.regs 4) 1 6 (by decide)
  have k23 : Apart (s.regs 4-(8#32)) (s.regs 4-(12#32)) := slots_apart (s.regs 4) 2 3 (by decide)
  have k24 : Apart (s.regs 4-(8#32)) (s.regs 4-(16#32)) := slots_apart (s.regs 4) 2 4 (by decide)
  have k25 : Apart (s.regs 4-(8#32)) (s.regs 4-(20#32)) := slots_apart (s.regs 4) 2 5 (by decide)
  have k26 : Apart (s.regs 4-(8#32)) (s.regs 4-(24#32)) := slots_apart (s.regs 4) 2 6 (by decide)
  have k34 : Apart (s.regs 4-(12#32)) (s.regs 4-(16#32)) := slots_apart (s.regs 4) 3 4 (by decide)
  have k35 : Apart (s.regs 4-(12#32)) (s.regs 4-(20#32)) := slots_apart (s.regs 4) 3 5 (by decide)
  have k36 : Apart (s.regs 4-(12#32)) (s.regs 4-(24#32)) := slots_apart (s.regs 4) 3 6 (by decide)
  have k45 : Apart (s.regs 4-(16#32)) (s.regs 4-(20#32)) := slots_apart (s.regs 4) 4 5 (by decide)
  have k46 : Apart (s.regs 4-(16#32)) (s.regs 4-(24#32)) := slots_apart (s.regs 4) 4 6 (by decide)
  have k56 : Apart (s.regs 4-(20#32)) (s.regs 4-(24#32)) := slots_apart (s.regs 4) 5 6 (by decide)
  simp only [saved,load_store,
    load_store_apart _ _ _ _ k12,
    load_store_apart _ _ _ _ k13,
    load_store_apart _ _ _ _ k14,
    load_store_apart _ _ _ _ k15,
    load_store_apart _ _ _ _ k16,
    load_store_apart _ _ _ _ k23,
    load_store_apart _ _ _ _ k24,
    load_store_apart _ _ _ _ k25,
    load_store_apart _ _ _ _ k26,
    load_store_apart _ _ _ _ k34,
    load_store_apart _ _ _ _ k35,
    load_store_apart _ _ _ _ k36,
    load_store_apart _ _ _ _ k45,
    load_store_apart _ _ _ _ k46,
    load_store_apart _ _ _ _ k56]

def preservedRegisters (s : X86Memory.State) :=
  (s.regs 3,s.regs 1,s.regs 2,s.regs 6,s.regs 7,s.regs 5,s.regs 4)


def enter (s : X86Memory.State) : X86Memory.State :=
  {regs := write s.regs 4 (s.regs 4-(24#32)),memory := saved s}

theorem prologue (s : X86Memory.State) (flags : Option Flags) :
    X86Routine.Prefix PlayerHeight.program [] 6 ⟨s,flags,0⟩ ⟨enter s,flags,6⟩ := by
  apply X86Routine.Prefix.step (by simp) (show PlayerHeight.program 0 = some (.push 3,1) from rfl) (by rfl)
  apply X86Routine.Prefix.step (by simp) (show PlayerHeight.program 1 = some (.push 1,1) from rfl) (by rfl)
  apply X86Routine.Prefix.step (by simp) (show PlayerHeight.program 2 = some (.push 2,1) from rfl) (by rfl)
  apply X86Routine.Prefix.step (by simp) (show PlayerHeight.program 3 = some (.push 6,1) from rfl) (by rfl)
  apply X86Routine.Prefix.step (by simp) (show PlayerHeight.program 4 = some (.push 7,1) from rfl) (by rfl)
  apply X86Routine.Prefix.step (by simp) (show PlayerHeight.program 5 = some (.push 5,1) from rfl) (by rfl)
  simpa [enter,saved,X86Routine.pushWord,put,write,BitVec.sub_sub,
    BitVec.sub_eq_add_neg,BitVec.add_assoc,write_shadow] using
    (X86Routine.Prefix.nil (program := PlayerHeight.program) (exits := []) ⟨enter s,flags,6⟩)

/-- The exact six POPs and RET; body memory is retained. -/
def leave (t : X86Control.State) : X86Control.State :=
  let sp := t.core.regs 4
  let m := t.core.memory
  ⟨⟨write (write (write (write (write (write (write t.core.regs
    5 (load32 m sp)) 7 (load32 m (sp+(4#32))))
    6 (load32 m (sp+(8#32)))) 2 (load32 m (sp+(12#32))))
    1 (load32 m (sp+(16#32)))) 3 (load32 m (sp+(20#32)))) 4 (sp+(28#32)),m⟩,
    t.flags,(load32 m (sp+(24#32))).toNat⟩

theorem epilogue (t : X86Control.State) (ret : Nat) (hr : 302 ≤ ret)
    (hp : t.pc = 295) (returnAddress : (load32 t.core.memory (t.core.regs 4+(24#32))).toNat = ret) :
    X86Routine.run program [ret] 7 t = some (leave t) := by
  rcases t with ⟨s,f,pc⟩; dsimp at hp; subst pc
  have a295 : (295:Nat) ∉ [ret] := by simp; omega
  have d295 : program 295 = some (.pop 5,1) := rfl
  have a296 : (296:Nat) ∉ [ret] := by simp; omega
  have d296 : program 296 = some (.pop 7,1) := rfl
  have a297 : (297:Nat) ∉ [ret] := by simp; omega
  have d297 : program 297 = some (.pop 6,1) := rfl
  have a298 : (298:Nat) ∉ [ret] := by simp; omega
  have d298 : program 298 = some (.pop 2,1) := rfl
  have a299 : (299:Nat) ∉ [ret] := by simp; omega
  have d299 : program 299 = some (.pop 1,1) := rfl
  have a300 : (300:Nat) ∉ [ret] := by simp; omega
  have d300 : program 300 = some (.pop 3,1) := rfl
  have a301 : (301:Nat) ∉ [ret] := by simp; omega
  have d301 : program 301 = some (.ret,1) := rfl
  simp only [X86Routine.run,a295,d295,a296,d296,a297,d297,a298,d298,a299,d299,a300,d300,a301,d301,↓reduceIte,
    X86Routine.execute,Bind.bind,Option.bind,put,write,↓reduceIte,BitVec.add_assoc] at *
  simp_all [leave,put,write,BitVec.add_assoc]
  funext r
  have cases : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 := by
    have hb := r.isLt
    simp only [Fin.ext_iff]; omega
  rcases cases with h|h|h|h|h|h|h|h <;> subst r <;> rfl

def object (s : X86Memory.State) : Word := load32 s.memory (s.regs 0)

/-- Only function-entry facts: encoded inputs, initialized tables, disjoint
writes/reads/stack, and a return address outside this 302-byte function. -/
structure Inputs (s : X86Memory.State) (body : Motion) (v : ViewState)
    (time : Int32) (ground live : Bool) : Prop where
  context : Context (s.regs 0) (object s) body time ground live s.memory
  words : Words (s.regs 0) s.memory v
  aliases : Safe (s.regs 0) (object s)
  pushesSafe : ∀ a, contextReads (s.regs 0) (object s) a ∨ a ∈ viewWrites (s.regs 0) →
    ∀ b, b ∈ pushSlots s → Apart a b
  savedSafe : ∀ a, a ∈ savedSlots s → ∀ b, b ∈ viewWrites (s.regs 0) → Apart a b
  returnOutside : 302 ≤ (load32 s.memory (s.regs 4)).toNat

@[simp] theorem enter_eax (s : X86Memory.State) : (enter s).regs 0 = s.regs 0 := rfl
@[simp] theorem enter_esp (s : X86Memory.State) : (enter s).regs 4 = s.regs 4-(24#32) := rfl

theorem establishes_context (s : X86Memory.State) (body : Motion) (v : ViewState)
    (time : Int32) (ground live : Bool) (h : Inputs s body v time ground live) :
    Context ((enter s).regs 0) (object s) body time ground live (enter s).memory := by
  change Context (s.regs 0) (object s) body time ground live (saved s)
  exact context_transport h.context (fun a ha => saved_load s a (h.pushesSafe a (Or.inl ha)))

theorem establishes_words (s : X86Memory.State) (body : Motion) (v : ViewState)
    (time : Int32) (ground live : Bool) (h : Inputs s body v time ground live) :
    Words ((enter s).regs 0) (enter s).memory v := by
  have keep (a : Word) (ha : a ∈ viewWrites (s.regs 0)) := saved_load s a (h.pushesSafe a (Or.inr ha))
  constructor
  · exact (keep _ (by simp [viewWrites])).trans h.words.height
  · exact (keep _ (by simp [viewWrites])).trans h.words.delta
  · exact (keep _ (by simp [viewWrites])).trans h.words.bob

theorem program_bound (pc : Nat) (h : program pc ≠ none) : pc < 302 := by
  by_cases he : pc = 301
  · omega
  · simp only [program,he,↓reduceIte] at h
    fun_cases PlayerHeight.program pc <;> first | omega | simp_all [PlayerHeight.program]

/-- Returning restores all six saved registers and pops the return address,
provided the body preserved the seven saved words. -/
theorem restores (s : X86Memory.State) (t : X86Control.State)
    (stack : t.core.regs 4 = s.regs 4-(24#32))
    (keep : ∀ a, a ∈ savedSlots s → load32 t.core.memory a = load32 (saved s) a) :
    preservedRegisters (leave t).core =
      (s.regs 3,s.regs 1,s.regs 2,s.regs 6,s.regs 7,s.regs 5,s.regs 4+(4#32)) := by
  have k1 := keep _ (show s.regs 4-(4#32) ∈ savedSlots s by simp [savedSlots])
  have k2 := keep _ (show s.regs 4-(8#32) ∈ savedSlots s by simp [savedSlots])
  have k3 := keep _ (show s.regs 4-(12#32) ∈ savedSlots s by simp [savedSlots])
  have k4 := keep _ (show s.regs 4-(16#32) ∈ savedSlots s by simp [savedSlots])
  have k5 := keep _ (show s.regs 4-(20#32) ∈ savedSlots s by simp [savedSlots])
  have k6 := keep _ (show s.regs 4-(24#32) ∈ savedSlots s by simp [savedSlots])
  have regs := saved_registers s
  simp only [Prod.mk.injEq] at regs
  obtain ⟨r3,r1,r2,r6,r7,r5⟩ := regs
  have a4 : s.regs 4-(24#32)+(4#32) = s.regs 4-(20#32) := by bv_decide
  have a8 : s.regs 4-(24#32)+(8#32) = s.regs 4-(16#32) := by bv_decide
  have a12 : s.regs 4-(24#32)+(12#32) = s.regs 4-(12#32) := by bv_decide
  have a16 : s.regs 4-(24#32)+(16#32) = s.regs 4-(8#32) := by bv_decide
  have a20 : s.regs 4-(24#32)+(20#32) = s.regs 4-(4#32) := by bv_decide
  have a28 : s.regs 4-(24#32)+(28#32) = s.regs 4+(4#32) := by bv_decide
  simp [preservedRegisters,leave,write,stack,a4,a8,a12,a16,a20,a28,k1,k2,k3,k4,k5,k6,
    r3,r1,r2,r6,r7,r5]

/-- Complete original P_CalcHeight execution, from PUSH through RET. -/
theorem execution (s : X86Memory.State) (flags : Option Flags) (body : Motion) (v : ViewState)
    (time : Int32) (ground live : Bool) (h : Inputs s body v time ground live) :
    ∃ t, X86Routine.run program [(load32 s.memory (s.regs 4)).toNat] 100 ⟨s,flags,0⟩ = some t ∧
      t.pc = (load32 s.memory (s.regs 4)).toNat ∧
      Words (s.regs 0) t.core.memory (v.calcHeight body time ground live) ∧
      load32 t.core.memory (s.regs 0+(16#32)) = (v.calcHeight body time ground live).z.raw.toBitVec ∧
      preservedRegisters t.core =
        (s.regs 3,s.regs 1,s.regs 2,s.regs 6,s.regs 7,s.regs 5,s.regs 4+(4#32)) ∧
      Frame s.memory t.core.memory (viewWrites (s.regs 0) ++ pushSlots s) := by
  obtain ⟨b,path,pc,post,z,frame⟩ := body_segment (enter s) flags (object s) body time ground live v
    (establishes_context s body v time ground live h) (establishes_words s body v time ground live h)
    (by simpa only [enter_eax] using h.aliases)
  have stack : b.core.regs 4 = s.regs 4-(24#32) := post.stack
  have keep (a : Word) (ha : a ∈ savedSlots s) : load32 b.core.memory a = load32 (saved s) a :=
    frame a (by simpa only [enter_eax] using h.savedSafe a ha)
  have returnAddress : (load32 b.core.memory (b.core.regs 4+(24#32))).toNat =
      (load32 s.memory (s.regs 4)).toNat := by
    rw [stack,BitVec.sub_add_cancel,keep _ (by simp [savedSlots]),saved_return]
  have tail := epilogue b _ h.returnOutside pc returnAddress
  have start : Reaches 6 ⟨s,flags,0⟩ ⟨enter s,flags,6⟩ := ⟨6,by decide,prologue s flags⟩
  obtain ⟨n,bound,pathAll⟩ := start.trans path
  have transferred := pathAll.transfer program [(load32 s.memory (s.regs 4)).toNat]
    (contains_body) (by intro pc hd; have hb := program_bound pc (by rw [contains_body pc hd]; exact hd); simp only [List.mem_singleton]; have := h.returnOutside; omega)
  have done := transferred.finish tail 100 (by omega)
  refine ⟨leave b,done,returnAddress,post.words,z,restores s b stack keep,?_⟩
  intro a ha
  have bodyKeep := frame a (by
    intro addr hadd; apply ha addr
    exact List.mem_append_left _ (by simpa only [enter_eax] using hadd))
  exact bodyKeep.trans (saved_load s a (fun addr hadd => ha addr (List.mem_append_right _ hadd)))

/-- The full result and memory frame also hold for the decoded original bytes. -/
theorem execution_bytes (s : X86Memory.State) (flags : Option Flags) (body : Motion) (v : ViewState)
    (time : Int32) (ground live : Bool) (h : Inputs s body v time ground live) :
    ∃ t, X86Routine.run (X86Routine.decodeAt code) [(load32 s.memory (s.regs 4)).toNat] 100 ⟨s,flags,0⟩ = some t ∧
      t.pc = (load32 s.memory (s.regs 4)).toNat ∧
      Words (s.regs 0) t.core.memory (v.calcHeight body time ground live) ∧
      load32 t.core.memory (s.regs 0+(16#32)) = (v.calcHeight body time ground live).z.raw.toBitVec ∧
      preservedRegisters t.core =
        (s.regs 3,s.regs 1,s.regs 2,s.regs 6,s.regs 7,s.regs 5,s.regs 4+(4#32)) ∧
      Frame s.memory t.core.memory (viewWrites (s.regs 0) ++ pushSlots s) := by
  obtain ⟨t,run,rest⟩ := execution s flags body v time ground live h
  refine ⟨t,?_,rest⟩
  rw [X86Routine.run_sound _ _ decoded _ _ _ (by rw [run]; simp),run]

def observe (p : Word) (t : X86Control.State) :=
  (t.pc,load32 t.core.memory (p+(20#32)),load32 t.core.memory (p+(24#32)),
    load32 t.core.memory (p+(16#32)),load32 t.core.memory (p+(28#32)),preservedRegisters t.core)

/-- Universal original-byte theorem with only a function-entry contract. -/
theorem observation (s : X86Memory.State) (flags : Option Flags) (body : Motion) (v : ViewState)
    (time : Int32) (ground live : Bool) (h : Inputs s body v time ground live) :
    (X86Routine.run (X86Routine.decodeAt code) [(load32 s.memory (s.regs 4)).toNat]
      100 ⟨s,flags,0⟩).map (observe (s.regs 0)) =
      some ((load32 s.memory (s.regs 4)).toNat,
        (v.calcHeight body time ground live).height.raw.toBitVec,
        (v.calcHeight body time ground live).delta.raw.toBitVec,
        (v.calcHeight body time ground live).z.raw.toBitVec,
        (v.calcHeight body time ground live).bob.raw.toBitVec,
        (s.regs 3,s.regs 1,s.regs 2,s.regs 6,s.regs 7,s.regs 5,s.regs 4+(4#32))) := by
  obtain ⟨t,run,pc,words,z,regs,_⟩ := execution_bytes s flags body v time ground live h
  rw [run]
  simp only [Option.map_some,observe,pc,words.height,words.delta,words.bob,z,regs]

end Doom.Proofs.PlayerHeight.Function
