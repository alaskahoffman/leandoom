import Doom.Proofs.OriginalPreparedRuntime

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
namespace Doom.Proofs.SectorDispatch
open Verification X86 X86Memory X86Control BlockSummary

/-- P_PlayerThink after P_CalcHeight, including the conditional special-sector
CALL encoding. Execution stops before that CALL; its callee is not assumed. -/
def code : List UInt8 := [0x8b,0x02,0x8b,0x40,0x34,0x8b,0x00,0x66,0x83,0x78,0x0e,0x00,
  0x74,0x07,0x89,0xd0,0xe8,0x3b,0xc7,0xff,0xff]
def bytesProgram (bytes : List UInt8) : X86Routine.Program := fun pc =>
  if 0x333d0 ≤ pc ∧ pc < 0x333d0+bytes.length then X86Routine.decodeAt bytes (pc-0x333d0)
  else none
def program := bytesProgram code

def object (s : X86Memory.State) := load32 s.memory (s.regs 2)
def subsector (s : X86Memory.State) := load32 s.memory (object s+(52#32))
def sector (s : X86Memory.State) := load32 s.memory (subsector s)
def special (s : X86Memory.State) := load16 s.memory (sector s+(14#32))
def exitPc (value : BitVec 16) : Nat := if value = 0 then 0x333e5 else 0x333e0

def result (s : X86Memory.State) : X86Control.State :=
  ⟨put s 0 (if special s = 0 then sector s else s.regs 2),
    some (X86Routine.compare16 (special s) 0),exitPc (special s)⟩

/-- Both branches, arbitrary memory and registers. No writes occur here.
A nonzero signed sector word is special, including negative bit patterns. -/
theorem execution (s : X86Memory.State) (flags : Option Flags) :
    X86Routine.run program [0x333e0,0x333e5] 6 ⟨s,flags,0x333d0⟩ = some (result s) := by
  have d0 : program 0x333d0 = some (.control (.block (.legacy (.load 0 2 0))),2) := by decide
  have d1 : program 0x333d2 = some (.control (.block (.legacy (.load 0 0 52))),3) := by decide
  have d2 : program 0x333d5 = some (.control (.block (.legacy (.load 0 0 0))),2) := by decide
  have d3 : program 0x333d7 = some (.compareHalf ⟨some 0,none,0,14⟩ 0,5) := by decide
  have d4 : program 0x333dc = some (.control (.jumpZero true 7),2) := by decide
  have d5 : program 0x333de = some (.control (.block (.legacy (.mov 0 2))),2) := by decide
  by_cases zero : special s = 0 <;>
    simp [X86Routine.run,d0,d1,d2,d3,d4,d5,X86Routine.execute,X86Control.execute,
      X86Block.execute,X86Memory.execute,X86Block.Address.eval,blockPreservesFlags,
      X86Routine.compare16,result,exitPc,special,sector,subsector,object,put,write] at zero ⊢ <;>
    simp_all
  all_goals funext r; simp [write]; split <;> simp_all

/-- The 16-bit load depends only on the low half of the framed word. -/
theorem load_half (m : Memory) (a : Word) : (load32 m a).extractLsb' 0 16 = load16 m a := by
  unfold load32 load16
  rw [BitVec.extractLsb'_append_eq_of_add_le (by decide)]
  simp

/-- Initial addresses whose contents determine the sector dispatch. -/
def reads (s : X86Memory.State) : List Word :=
  [s.regs 2,object s+(52#32),subsector s,sector s+(14#32)]
def writes (s : X86Memory.State) := PlayerHeightJoin.writes s ++ PlayerPreparation.heightWrites s

def Safe (s : X86Memory.State) : Prop :=
  ∀ a, a ∈ reads s → ∀ b, b ∈ writes s → Apart a b

/-- Carry the pointer chain and 16-bit special through preparation, rather
than assuming their values again at the intermediate boundary. -/
theorem special_preserved (s t : X86Memory.State) (edx : t.regs 2 = s.regs 2)
    (frame : PlayerHeight.Frame s.memory t.memory (writes s)) (safe : Safe s) :
    special t = special s := by
  have keep (a : Word) (ha : a ∈ reads s) := frame a (safe a ha)
  have obj : object t = object s := by
    unfold object; rw [edx,keep _ (by simp [reads])]
  have sub : subsector t = subsector s := by
    unfold subsector; rw [obj,keep _ (by simp [reads])]
  have sec : sector t = sector s := by
    unfold sector; rw [sub,keep _ (by simp [reads])]
  unfold special
  rw [sec,← load_half,keep _ (by simp [reads]),load_half]

def joinedBytes (reaction movement setter heightCaller height dispatch : List UInt8) : X86Routine.Program := fun pc =>
  match bytesProgram dispatch pc with
  | some op => some op
  | none => PlayerPreparation.bytesProgram reaction movement setter heightCaller height pc

def joined := joinedBytes PlayerReactionProof.callerBytes PlayerFunction.functionBytes
  Doom19.setMobjStateBytes PlayerHeight.Caller.callBytes PlayerHeight.code code

theorem preparation_bound (pc : Nat) (h : PlayerPreparation.program pc ≠ none) : pc < 0x333d0 := by
  change (match PlayerHeight.Shared.program pc with
    | some op => some op | none => PlayerReactionProof.program pc) ≠ none at h
  cases hs : PlayerHeight.Shared.program pc with
  | none =>
    rw [hs] at h
    have b := PlayerPreparation.reaction_region pc h
    omega
  | some op =>
    unfold PlayerHeight.Shared.program PlayerHeight.Shared.bytesProgram at hs
    split at hs
    next hp => omega
    next hp =>
      split at hs
      next hh => change _ ∧ pc < 0x33030+302 at hh; omega
      next hh => simp_all

theorem contains_preparation (pc : Nat) (h : PlayerPreparation.program pc ≠ none) :
    joined pc = PlayerPreparation.program pc := by
  have bound := preparation_bound pc h
  change (match program pc with | some op => some op | none => PlayerPreparation.program pc) = _
  have hn : program pc = none := by
    unfold program bytesProgram
    rw [if_neg (by omega)]
  rw [hn]

theorem contains_dispatch (pc : Nat) (h : program pc ≠ none) : joined pc = program pc := by
  change (match program pc with | some op => some op | none => PlayerPreparation.program pc) = _
  cases hp : program pc with
  | none => exact False.elim (h hp)
  | some op => rfl

/-- One uninterrupted original-byte execution through preparation and the
sector decision. Special sectors stop with EAX prepared immediately before
P_PlayerInSpecialSector's CALL. Its effects are deliberately not assumed. -/
theorem joined_execution (s : X86Memory.State) (flags : Option Flags)
    (body : Motion) (anim : PlayerAnim.State) (cmd : Ticcmd) (timer : Int32)
    (v : ViewState) (time : Int32) (cached live : Bool)
    (h : PlayerHeightJoin.Inputs s body anim cmd timer v time cached live) (safe : Safe s) :
    ∃ t, X86Routine.run joined [0x333e0,0x333e5] 231 ⟨s,flags,0x333b1⟩ = some t ∧
      t.pc = exitPc (special s) ∧
      PreparedState.read (s.regs 2) (PlayerCaller.object s) t.core.memory =
        PreparedState.expected body anim cmd timer v time cached live ∧
      t.core.regs 4 = s.regs 4 ∧ t.core.regs 2 = s.regs 2 ∧
      (special s ≠ 0 → t.core.regs 0 = s.regs 2) ∧
      PlayerHeight.Frame s.memory t.core.memory (writes s) := by
  obtain ⟨t,run,pc,_,_,sp,_,edx⟩ := PlayerPreparation.execution_preserved s flags body anim cmd timer v time cached live h
  obtain ⟨u,run',_,fields,_,frame⟩ := PreparedState.execution s flags body anim cmd timer v time cached live h
  have same : u = t := Option.some.inj (run'.symm.trans run)
  subst u
  have value := special_preserved s t.core edx frame safe
  obtain ⟨n,bound,path,_⟩ := X86Routine.run_path run
  have first := path.transfer joined [0x333e0,0x333e5] contains_preparation (by
    intro pc hd; have hb := preparation_bound pc hd; simp only [List.mem_cons,List.not_mem_nil,or_false]; omega)
  have tail : X86Routine.run joined [0x333e0,0x333e5] 6 t = some (result t.core) := by
    have entry : t = ⟨t.core,t.flags,0x333d0⟩ := by rw [← pc]
    rw [entry]
    rw [X86Routine.run_sound joined program contains_dispatch _ _ _ (by rw [execution]; simp),execution]
  refine ⟨result t.core,first.finish tail 231 (by omega),?_,?_,?_,?_,?_,?_⟩
  · simp only [result,value]
  · exact fields
  · simpa [result,put,write] using sp
  · simpa [result,put,write] using edx
  · intro nonzero
    change (if special t.core = 0 then sector t.core else t.core.regs 2) = s.regs 2
    rw [value,if_neg nonzero]
    exact edx
  · exact frame

def observe (p obj : Word) (t : X86Control.State) :=
  (t.pc,PreparedState.read p obj t.core.memory,t.core.regs 4,t.core.regs 2)

theorem observation (s : X86Memory.State) (flags : Option Flags)
    (body : Motion) (anim : PlayerAnim.State) (cmd : Ticcmd) (timer : Int32)
    (v : ViewState) (time : Int32) (cached live : Bool)
    (h : PlayerHeightJoin.Inputs s body anim cmd timer v time cached live) (safe : Safe s) :
    (X86Routine.run joined [0x333e0,0x333e5] 231 ⟨s,flags,0x333b1⟩).map
      (observe (s.regs 2) (PlayerCaller.object s)) =
      some (exitPc (special s),PreparedState.expected body anim cmd timer v time cached live,s.regs 4,s.regs 2) := by
  obtain ⟨t,run,pc,fields,sp,edx,_,_⟩ := joined_execution s flags body anim cmd timer v time cached live h safe
  rw [run]
  simp only [Option.map_some,observe,pc,fields,sp,edx]

end Doom.Proofs.SectorDispatch
