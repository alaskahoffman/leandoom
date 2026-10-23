import Doom.Proofs.OriginalFloorCaller
import Doom.Proofs.DeathStack

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.FloorReturn
open Verification X86 X86Memory X86Control BlockSummary

/-- The three damage continuations and the common no-damage exit contain the
same four POPs and RET in the pinned DOS executable. -/
def sites : List Nat := [0x2fb7b,0x2fba5,0x2fbd7,0x2fc39]
def code : List UInt8 := [0x5e,0x5a,0x59,0x5b,0xc3]
def bytesProgram (a b c d : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2fb7b ≤ pc ∧ pc < 0x2fb80 then X86Routine.decodeAt a (pc-0x2fb7b)
  else if 0x2fba5 ≤ pc ∧ pc < 0x2fbaa then X86Routine.decodeAt b (pc-0x2fba5)
  else if 0x2fbd7 ≤ pc ∧ pc < 0x2fbdc then X86Routine.decodeAt c (pc-0x2fbd7)
  else if 0x2fc39 ≤ pc ∧ pc < 0x2fc3e then X86Routine.decodeAt d (pc-0x2fc39)
  else none
def program := bytesProgram code code code code

def listed : X86Routine.Program
  | 0x2fb7b | 0x2fba5 | 0x2fbd7 | 0x2fc39 => some (.pop 6,1)
  | 0x2fb7c | 0x2fba6 | 0x2fbd8 | 0x2fc3a => some (.pop 2,1)
  | 0x2fb7d | 0x2fba7 | 0x2fbd9 | 0x2fc3b => some (.pop 1,1)
  | 0x2fb7e | 0x2fba8 | 0x2fbda | 0x2fc3c => some (.pop 3,1)
  | 0x2fb7f | 0x2fba9 | 0x2fbdb | 0x2fc3d => some (.ret,1)
  | _ => none

theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def result (s : X86Memory.State) (f : Option Flags) : X86Control.State :=
  ⟨⟨write (write (write (write (write s.regs 6 (load32 s.memory (s.regs 4)))
    2 (load32 s.memory (s.regs 4+4))) 1 (load32 s.memory (s.regs 4+8)))
    3 (load32 s.memory (s.regs 4+12))) 4 (s.regs 4+20),s.memory⟩,
    f,(load32 s.memory (s.regs 4+16)).toNat⟩

theorem execution (s : X86Memory.State) (f : Option Flags) (pc : Nat)
    (site : pc ∈ sites) (returnPC : load32 s.memory (s.regs 4+16)=0x333e5) :
    X86Routine.run listed [0x333e5] 5 ⟨s,f,pc⟩=some (result s f) := by
  change load32 s.memory (s.regs 4+(16#32))=(0x333e5#32) at returnPC
  simp only [sites,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at site
  rcases site with rfl|rfl|rfl|rfl <;>
    simp [X86Routine.run,listed,X86Routine.execute,put,write,result,BitVec.add_assoc,returnPC] <;>
    funext r <;> by_cases r1 : r=1 <;> by_cases r2 : r=2 <;>
    by_cases r3 : r=3 <;> by_cases r4 : r=4 <;> by_cases r6 : r=6 <;> simp_all [write]

theorem original_execution (s : X86Memory.State) (f : Option Flags) (pc : Nat)
    (site : pc ∈ sites) (returnPC : load32 s.memory (s.regs 4+16)=0x333e5) :
    X86Routine.run program [0x333e5] 5 ⟨s,f,pc⟩=some (result s f) := by
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [execution s f pc site returnPC]; simp)]
  exact execution s f pc site returnPC

/-- Saved words at a floor-effect boundary. These are derived from the actual
caller below; this structure alone does not assert that a caller has executed. -/
structure Saved (caller boundary : X86Memory.State) : Prop where
  sp : boundary.regs 4=caller.regs 4-20
  words : ∀ a, a ∈ SectorCaller.slots caller →
    load32 boundary.memory a=load32 (SectorCaller.saved caller) a

theorem Saved.then_frame {caller s t : X86Memory.State} (h : Saved caller s)
    (sp : t.regs 4=s.regs 4) (writes : List Word)
    (frame : PlayerHeight.Frame s.memory t.memory writes)
    (safe : ∀ a, a ∈ SectorCaller.slots caller → ∀ b, b ∈ writes → Apart a b) :
    Saved caller t :=
  ⟨sp.trans h.sp,fun a ha => (frame a (safe a ha)).trans (h.words a ha)⟩

/-- The original CALL and prologue establish the saved frame, even when the
floor test makes the optional suit-leak RNG call. Only address separation is
assumed; no saved register value or return address is supplied as a hypothesis. -/
theorem caller_saved (kind : FloorDamage.Kind) (s : X86Memory.State)
    (z floor : Fixed) (time : Nat) (suit : Bool) (rng : DoomRandom)
    (h : FloorCaller.Inputs kind s z floor time suit rng)
    (indexSafe : ∀ a, a ∈ SectorCaller.slots s → Apart a (0x12720#32)) :
    Saved s (FloorCaller.result kind s rng).core := by
  refine ⟨FloorCaller.stack_position kind s rng,?_⟩
  intro a ha
  rw [FloorCaller.memory_frame kind s z floor time suit rng h]
  split
  · rw [load_store_apart _ _ _ _ (indexSafe a ha)]
    apply load_store_apart
    simp only [SectorCaller.slots,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl|rfl|rfl
    · exact DeathStack.slots_apart (s.regs 4) ⟨1,by decide⟩ ⟨6,by decide⟩ (by decide)
    · exact DeathStack.slots_apart (s.regs 4) ⟨2,by decide⟩ ⟨6,by decide⟩ (by decide)
    · exact DeathStack.slots_apart (s.regs 4) ⟨3,by decide⟩ ⟨6,by decide⟩ (by decide)
    · exact DeathStack.slots_apart (s.regs 4) ⟨4,by decide⟩ ⟨6,by decide⟩ (by decide)
    · exact DeathStack.slots_apart (s.regs 4) ⟨5,by decide⟩ ⟨6,by decide⟩ (by decide)

  · rfl

/-- Reading the proved frame restores the outer caller's registers and stack.
EAX, EBP, EDI and flags are exactly those delivered by the enclosed effect. -/
theorem restores (caller s : X86Memory.State) (f : Option Flags) (h : Saved caller s) :
    (result s f).pc=0x333e5 ∧
    (result s f).core.regs 4=caller.regs 4 ∧
    (result s f).core.regs 6=caller.regs 6 ∧
    (result s f).core.regs 2=caller.regs 2 ∧
    (result s f).core.regs 1=caller.regs 1 ∧
    (result s f).core.regs 3=caller.regs 3 ∧
    (result s f).core.regs 0=s.regs 0 ∧
    (result s f).core.regs 5=s.regs 5 ∧
    (result s f).core.regs 7=s.regs 7 ∧
    (result s f).core.memory=s.memory ∧ (result s f).flags=f := by
  have words := SectorCaller.saved_words caller
  simp only [Prod.mk.injEq] at words
  rcases words with ⟨ret,b,c,d,si⟩
  have ret := (h.words (caller.regs 4-(4#32)) (by simp [SectorCaller.slots])).trans ret
  have b := (h.words (caller.regs 4-(8#32)) (by simp [SectorCaller.slots])).trans b
  have c := (h.words (caller.regs 4-(12#32)) (by simp [SectorCaller.slots])).trans c
  have d := (h.words (caller.regs 4-(16#32)) (by simp [SectorCaller.slots])).trans d
  have si := (h.words (caller.regs 4-(20#32)) (by simp [SectorCaller.slots])).trans si
  simp [BitVec.sub_eq_add_neg] at ret b c d si
  simp [result,write,h.sp,BitVec.sub_eq_add_neg,BitVec.add_assoc,ret,b,c,d,si]

end Doom.Proofs.FloorReturn
