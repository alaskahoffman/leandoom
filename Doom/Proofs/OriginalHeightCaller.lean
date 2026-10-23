import Doom.Proofs.OriginalHeightFunction

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000
namespace Doom.Proofs.PlayerHeight.Caller
open Verification X86 X86Memory X86Control BlockSummary

/-- Original P_PlayerThink CALL at 0x333cb, using P_CalcHeight's
0x33030 code origin. The actual return PC is 0x3a0. -/
def callBytes : List UInt8 := [0xe8,0x60,0xfc,0xff,0xff]
def bytesProgram (caller height : List UInt8) : X86Routine.Program := fun pc =>
  if pc = 0x39b then X86Routine.decodeAt caller 0
  else X86Routine.decodeAt height pc
def program := bytesProgram callBytes code
def entry (s : X86Memory.State) := X86Routine.pushWord s 0x3a0
def beforePush (s : X86Memory.State) := put s 4 (s.regs 4-(4#32))
def reads (s : X86Memory.State) (a : Word) :=
  contextReads (s.regs 0) (Function.object s) a ∨ a ∈ viewWrites (s.regs 0)

/-- Facts about memory before CALL. The return address is derived, not assumed. -/
structure Inputs (s : X86Memory.State) (body : Motion) (v : ViewState)
    (time : Int32) (ground live : Bool) : Prop where
  context : Context (s.regs 0) (Function.object s) body time ground live s.memory
  words : Words (s.regs 0) s.memory v
  aliases : Safe (s.regs 0) (Function.object s)
  callSafe : ∀ a, reads s a → Apart a (s.regs 4-(4#32))
  pushesSafe : ∀ a, reads s a → ∀ b, b ∈ Function.pushSlots (beforePush s) → Apart a b
  savedSafe : ∀ a, a ∈ Function.savedSlots (beforePush s) →
    ∀ b, b ∈ viewWrites (s.regs 0) → Apart a b

@[simp] theorem entry_eax (s : X86Memory.State) : (entry s).regs 0 = s.regs 0 := rfl
@[simp] theorem entry_esp (s : X86Memory.State) : (entry s).regs 4 = s.regs 4-(4#32) := rfl
theorem entry_return (s : X86Memory.State) : load32 (entry s).memory ((entry s).regs 4) = 0x3a0 := by
  exact load_store _ _ _

theorem entry_object (s : X86Memory.State) (body : Motion) (v : ViewState)
    (time : Int32) (ground live : Bool) (h : Inputs s body v time ground live) :
    Function.object (entry s) = Function.object s := by
  exact load_store_apart _ _ _ _ (h.callSafe _ (Or.inl (by simp [contextReads])))

/-- CALL's stack store establishes the complete existing function contract. -/
theorem establishes_function (s : X86Memory.State) (body : Motion) (v : ViewState)
    (time : Int32) (ground live : Bool) (h : Inputs s body v time ground live) :
    Function.Inputs (entry s) body v time ground live := by
  have obj := entry_object s body v time ground live h
  have keep (a : Word) (ha : reads s a) : load32 (entry s).memory a = load32 s.memory a :=
    load_store_apart _ _ _ _ (h.callSafe a ha)
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rw [entry_eax,obj]
    exact context_transport h.context (fun a ha => keep a (Or.inl ha))
  · constructor
    · exact (keep _ (Or.inr (by simp [viewWrites]))).trans h.words.height
    · exact (keep _ (Or.inr (by simp [viewWrites]))).trans h.words.delta
    · exact (keep _ (Or.inr (by simp [viewWrites]))).trans h.words.bob
  · simpa only [entry_eax,obj] using h.aliases
  · intro a ha b hb
    rw [entry_eax,obj] at ha
    exact h.pushesSafe a ha b hb
  · exact h.savedSafe
  · rw [entry_return]; decide

theorem call_prefix (s : X86Memory.State) (flags : Option Flags) :
    X86Routine.Prefix program [0x3a0] 1 ⟨s,flags,0x39b⟩ ⟨entry s,flags,0⟩ := by
  apply X86Routine.Prefix.step (by simp)
    (show program 0x39b = some (.call (-928),5) from by decide) (by rfl)
  exact X86Routine.Prefix.nil _

theorem contains_height (pc : Nat) (h : Function.program pc ≠ none) :
    program pc = Function.program pc := by
  have bound := Function.program_bound pc h
  unfold program bytesProgram
  rw [if_neg (by omega)]
  exact Function.decoded pc h

/-- Execute the original CALL, the entire original function, and RET, without
installing a return address or resetting memory/registers at the call seam. -/
theorem execution (s : X86Memory.State) (flags : Option Flags) (body : Motion) (v : ViewState)
    (time : Int32) (ground live : Bool) (h : Inputs s body v time ground live) :
    ∃ t, X86Routine.run program [0x3a0] 101 ⟨s,flags,0x39b⟩ = some t ∧
      t.pc = 0x3a0 ∧ Words (s.regs 0) t.core.memory (v.calcHeight body time ground live) ∧
      load32 t.core.memory (s.regs 0+(16#32)) = (v.calcHeight body time ground live).z.raw.toBitVec ∧
      Function.preservedRegisters t.core = Function.preservedRegisters s ∧
      Frame s.memory t.core.memory
        (viewWrites (s.regs 0) ++ Function.pushSlots (beforePush s) ++ [s.regs 4-(4#32)]) := by
  obtain ⟨t,run,pc,words,z,regs,frame⟩ := Function.execution (entry s) flags body v time ground live
    (establishes_function s body v time ground live h)
  rw [entry_return] at run pc
  change X86Routine.run Function.program [0x3a0] 100 ⟨entry s,flags,0⟩ = some t at run
  change t.pc = 0x3a0 at pc
  have actual : X86Routine.run program [0x3a0] 100 ⟨entry s,flags,0⟩ = some t := by
    rw [X86Routine.run_sound program Function.program contains_height _ _ _ (by rw [run]; simp),run]
  refine ⟨t,(call_prefix s flags).finish actual 101 (by omega),pc,words,z,?_,?_⟩
  · simpa [Function.preservedRegisters,entry,X86Routine.pushWord,put,write,
      BitVec.sub_add_cancel] using regs
  · intro a ha
    exact (frame a (fun b hb => ha b (List.mem_append_left _ hb))).trans
      (load_store_apart _ _ _ _ (ha _ (by simp)))

theorem observation (s : X86Memory.State) (flags : Option Flags) (body : Motion) (v : ViewState)
    (time : Int32) (ground live : Bool) (h : Inputs s body v time ground live) :
    (X86Routine.run program [0x3a0] 101 ⟨s,flags,0x39b⟩).map (Function.observe (s.regs 0)) =
      some (0x3a0,(v.calcHeight body time ground live).height.raw.toBitVec,
        (v.calcHeight body time ground live).delta.raw.toBitVec,
        (v.calcHeight body time ground live).z.raw.toBitVec,
        (v.calcHeight body time ground live).bob.raw.toBitVec,Function.preservedRegisters s) := by
  obtain ⟨t,run,pc,words,z,regs,_⟩ := execution s flags body v time ground live h
  rw [run]
  simp only [Option.map_some,Function.observe,pc,words.height,words.delta,words.bob,z,regs]

end Doom.Proofs.PlayerHeight.Caller
