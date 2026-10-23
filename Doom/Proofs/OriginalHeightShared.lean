import Doom.Proofs.OriginalHeightCaller
import Doom.Verification.X86RoutineBridge

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
namespace Doom.Proofs.PlayerHeight.Shared
open Verification X86 X86Memory X86Control BlockSummary
open Doom.Proofs.PlayerHeight.Function

/-- All PCs use absolute DOS code-object offsets, shared with movement and sector dispatch. -/
def base : Nat := 0x33030
def bytesProgram (caller height : List UInt8) : X86Routine.Program := fun pc =>
  if pc = 0x333cb then X86Routine.decodeAt caller 0
  else if base ≤ pc ∧ pc < base+height.length then X86Routine.decodeAt height (pc-base)
  else none
def program := bytesProgram Caller.callBytes code

theorem shifted_decoded (pc : Nat) (op : X86Routine.Op) (len : Nat)
    (h : PlayerHeight.program pc = some (op,len)) :
    program (base+pc) = some (op,len) := by
  have valid : PlayerHeight.program pc ≠ none := by simp [h]
  have bound := Function.program_bound pc (by rw [Function.contains_body pc valid]; exact valid)
  unfold program bytesProgram
  rw [if_neg (by unfold base; omega),if_pos (by change base ≤ base+pc ∧ base+pc < base+302; omega)]
  simpa only [Nat.add_sub_cancel_left] using (PlayerHeight.decoded pc valid).trans h

/-- The return-free body relocates PC only. No stack values or memory are
translated. Finite decoder cases check every branch's bounds after relocation. -/
theorem execute_shift (pc : Nat) (op : X86Routine.Op) (len : Nat)
    (h : PlayerHeight.program pc = some (op,len)) (s : X86Memory.State) (f : Option Flags) :
    X86Routine.execute op ⟨s,f,base+pc+len⟩ =
      (X86Routine.execute op ⟨s,f,pc+len⟩).map (shiftState base) := by
  fun_cases PlayerHeight.program pc <;> simp_all [PlayerHeight.program]
  all_goals obtain ⟨rfl,rfl⟩ := h
  all_goals first | rfl | cases f <;> simp [X86Routine.execute,X86Control.execute,shiftState,base]
  all_goals split <;> simp_all [shiftState]

theorem lift_prefix {n s t} (path : X86Routine.Prefix PlayerHeight.program [] n s t)
    (ret : Nat) (outside : base+302 ≤ ret) :
    X86Routine.Prefix program [ret] n (shiftState base s) (shiftState base t) := by
  induction path with
  | nil => exact X86Routine.Prefix.nil _
  | @step n s middle last op len active decoded executed rest ih =>
    have valid : PlayerHeight.program s.pc ≠ none := by simp [decoded]
    have bound := Function.program_bound s.pc (by rw [Function.contains_body _ valid]; exact valid)
    refine X86Routine.Prefix.step (by simp only [shiftState,List.mem_singleton]; omega)
      (shifted_decoded _ _ _ decoded) ?_ ih
    have he := execute_shift _ _ _ decoded s.core s.flags
    rw [executed] at he
    exact he

theorem epilogue (t : X86Control.State) (ret : Nat) (hr : base+302 ≤ ret)
    (hp : t.pc = (base+295)) (returnAddress : (load32 t.core.memory (t.core.regs 4+(24#32))).toNat = ret) :
    X86Routine.run program [ret] 7 t = some (leave t) := by
  rcases t with ⟨s,f,pc⟩; dsimp at hp; subst pc
  have a295 : ((base+295):Nat) ∉ [ret] := by simp; unfold base at *; omega
  have d295 : program (base+295) = some (.pop 5,1) := by decide
  have a296 : ((base+296):Nat) ∉ [ret] := by simp; unfold base at *; omega
  have d296 : program (base+296) = some (.pop 7,1) := by decide
  have a297 : ((base+297):Nat) ∉ [ret] := by simp; unfold base at *; omega
  have d297 : program (base+297) = some (.pop 6,1) := by decide
  have a298 : ((base+298):Nat) ∉ [ret] := by simp; unfold base at *; omega
  have d298 : program (base+298) = some (.pop 2,1) := by decide
  have a299 : ((base+299):Nat) ∉ [ret] := by simp; unfold base at *; omega
  have d299 : program (base+299) = some (.pop 1,1) := by decide
  have a300 : ((base+300):Nat) ∉ [ret] := by simp; unfold base at *; omega
  have d300 : program (base+300) = some (.pop 3,1) := by decide
  have a301 : ((base+301):Nat) ∉ [ret] := by simp; unfold base at *; omega
  have d301 : program (base+301) = some (.ret,1) := by decide
  simp only [X86Routine.run,a295,d295,a296,d296,a297,d297,a298,d298,a299,d299,a300,d300,a301,d301,↓reduceIte,
    X86Routine.execute,Bind.bind,Option.bind,put,write,↓reduceIte,BitVec.add_assoc] at *
  simp_all [leave,put,write,BitVec.add_assoc]
  funext r
  have cases : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 := by
    have hb := r.isLt
    simp only [Fin.ext_iff]; omega
  rcases cases with h|h|h|h|h|h|h|h <;> subst r <;> rfl

theorem function_execution (s : X86Memory.State) (flags : Option Flags) (body : Motion) (v : ViewState)
    (time : Int32) (ground live : Bool) (h : Function.Inputs s body v time ground live)
    (outside : base+302 ≤ (load32 s.memory (s.regs 4)).toNat) :
    ∃ t, X86Routine.run program [(load32 s.memory (s.regs 4)).toNat] 100 ⟨s,flags,base⟩ = some t ∧
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
  have tail := epilogue (shiftState base b) _ outside (by simp [shiftState,pc]) returnAddress
  have start : Reaches 6 ⟨s,flags,0⟩ ⟨enter s,flags,6⟩ := ⟨6,by decide,prologue s flags⟩
  obtain ⟨n,bound,pathAll⟩ := start.trans path
  have transferred := lift_prefix pathAll _ outside
  have done := transferred.finish tail 100 (by omega)
  refine ⟨leave b,done,returnAddress,post.words,z,restores s b stack keep,?_⟩
  intro a ha
  have bodyKeep := frame a (by
    intro addr hadd; apply ha addr
    exact List.mem_append_left _ (by simpa only [enter_eax] using hadd))
  exact bodyKeep.trans (saved_load s a (fun addr hadd => ha addr (List.mem_append_right _ hadd)))


def entry (s : X86Memory.State) := X86Routine.pushWord s 0x333d0
def beforePush (s : X86Memory.State) := put s 4 (s.regs 4-(4#32))
def reads (s : X86Memory.State) (a : Word) :=
  contextReads (s.regs 0) (Function.object s) a ∨ a ∈ viewWrites (s.regs 0)

abbrev Inputs := Caller.Inputs

@[simp] theorem entry_eax (s : X86Memory.State) : (entry s).regs 0 = s.regs 0 := rfl
@[simp] theorem entry_esp (s : X86Memory.State) : (entry s).regs 4 = s.regs 4-(4#32) := rfl
theorem entry_return (s : X86Memory.State) : load32 (entry s).memory ((entry s).regs 4) = 0x333d0 := by
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
    X86Routine.Prefix program [0x333d0] 1 ⟨s,flags,0x333cb⟩ ⟨entry s,flags,base⟩ := by
  apply X86Routine.Prefix.step (by simp)
    (show program 0x333cb = some (.call (-928),5) from by decide) (by rfl)
  exact X86Routine.Prefix.nil _


theorem execution (s : X86Memory.State) (flags : Option Flags) (body : Motion) (v : ViewState)
    (time : Int32) (ground live : Bool) (h : Inputs s body v time ground live) :
    ∃ t, X86Routine.run program [0x333d0] 101 ⟨s,flags,0x333cb⟩ = some t ∧
      t.pc = 0x333d0 ∧ Words (s.regs 0) t.core.memory (v.calcHeight body time ground live) ∧
      load32 t.core.memory (s.regs 0+(16#32)) = (v.calcHeight body time ground live).z.raw.toBitVec ∧
      Function.preservedRegisters t.core = Function.preservedRegisters s ∧
      Frame s.memory t.core.memory
        (viewWrites (s.regs 0) ++ Function.pushSlots (beforePush s) ++ [s.regs 4-(4#32)]) := by
  obtain ⟨t,run,pc,words,z,regs,frame⟩ := function_execution (entry s) flags body v time ground live
    (establishes_function s body v time ground live h) (by rw [entry_return]; decide)
  rw [entry_return] at run pc
  change X86Routine.run program [0x333d0] 100 ⟨entry s,flags,base⟩ = some t at run
  change t.pc = 0x333d0 at pc
  refine ⟨t,(call_prefix s flags).finish run 101 (by omega),pc,words,z,?_,?_⟩
  · simpa [Function.preservedRegisters,entry,X86Routine.pushWord,put,write,
      BitVec.sub_add_cancel] using regs
  · intro a ha
    exact (frame a (fun b hb => ha b (List.mem_append_left _ hb))).trans
      (load_store_apart _ _ _ _ (ha _ (by simp)))


end Doom.Proofs.PlayerHeight.Shared
