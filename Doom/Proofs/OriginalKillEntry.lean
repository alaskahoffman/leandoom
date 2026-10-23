import Doom.Proofs.OriginalDamageRejected
import Doom.Death
import Doom.Proofs.DeathStack

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.KillEntry
open Verification X86 X86Memory X86Control BlockSummary

def handoffBytes : List UInt8 := [0x8b,0x44,0x24,0x4,0x89,0xf2,0xe8,0xff,0xfb,0xff,0xff]
def corpseBytes : List UInt8 := [0x53,0x51,0x56,0x57,0x55,0x89,0xc1,0x89,0xd3,0x8b,0x52,0x68,0x81,0xe2,0xfb,0xbf,0xff,0xfe,0x8b,0x73,0x58,0x89,0x53,0x68,0x83,0xfe,0x12,0x74,0x4,0x80,0x63,0x69,0xfd,0x8b,0x7b,0x68,0x8b,0x6b,0x44,0x81,0xcf,0x0,0x4,0x10,0x0,0xc1,0xfd,0x2,0x89,0x7b,0x68,0x89,0x6b,0x44]
def bytesProgram (handoff corpse : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2a6a6 ≤ pc ∧ pc < 0x2a6b1 then X86Routine.decodeAt handoff (pc-0x2a6a6)
  else if 0x2a2b0 ≤ pc ∧ pc < 0x2a2e6 then X86Routine.decodeAt corpse (pc-0x2a2b0)
  else none
def program := bytesProgram handoffBytes corpseBytes

def listed : X86Routine.Program
  | 0x2a6a6 => some (.control (.block (.load 0 ⟨some 4,none,0,4⟩)),4)
  | 0x2a6aa => some (.control (.block (.legacy (.mov 2 6))),2)
  | 0x2a6ac => some (.call (-1025),5)
  | 0x2a2b0 => some (.push 3,1)
  | 0x2a2b1 => some (.push 1,1)
  | 0x2a2b2 => some (.push 6,1)
  | 0x2a2b3 => some (.push 7,1)
  | 0x2a2b4 => some (.push 5,1)
  | 0x2a2b5 => some (.control (.block (.legacy (.mov 1 0))),2)
  | 0x2a2b7 => some (.control (.block (.legacy (.mov 3 2))),2)
  | 0x2a2b9 => some (.control (.block (.legacy (.load 2 2 104))),3)
  | 0x2a2bc => some (.andRegister 2 0xfeffbffb,6)
  | 0x2a2c2 => some (.control (.block (.legacy (.load 6 3 88))),3)
  | 0x2a2c5 => some (.control (.block (.store ⟨some 3,none,0,104⟩ 2)),3)
  | 0x2a2c8 => some (.compareRegister 6 18,3)
  | 0x2a2cb => some (.control (.jumpZero true 4),2)
  | 0x2a2cd => some (.andMemoryByte ⟨some 3,none,0,105⟩ 0xfd,4)
  | 0x2a2d1 => some (.control (.block (.legacy (.load 7 3 104))),3)
  | 0x2a2d4 => some (.control (.block (.legacy (.load 5 3 68))),3)
  | 0x2a2d7 => some (.orRegister 7 0x100400,6)
  | 0x2a2dd => some (.sar 5 2,3)
  | 0x2a2e0 => some (.control (.block (.store ⟨some 3,none,0,104⟩ 7)),3)
  | 0x2a2e3 => some (.control (.block (.store ⟨some 3,none,0,68⟩ 5)),3)
  | _ => none

theorem decoded (pc : Nat) (h : listed pc ≠ none) : program pc = listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def handed (s : X86Memory.State) :=
  X86Routine.pushWord (put (put s 0 (load32 s.memory (s.regs 4+4))) 2 (s.regs 6)) 0x2a6b1

theorem handoff_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run listed [0x2a2b0] 3 ⟨s,f,0x2a6a6⟩ = some ⟨handed s,f,0x2a2b0⟩ := by
  simp [X86Routine.run,listed,X86Routine.execute,X86Control.execute,X86Block.execute,
    X86Memory.execute,blockPreservesFlags,X86Block.Address.eval,handed,put,write]

def saved (s : X86Memory.State) :=
  X86Routine.pushWord (X86Routine.pushWord (X86Routine.pushWord (X86Routine.pushWord
    (X86Routine.pushWord s (s.regs 3)) (s.regs 1)) (s.regs 6)) (s.regs 7)) (s.regs 5)
def entered (s : X86Memory.State) := put (put (saved s) 1 (s.regs 0)) 3 (s.regs 2)

theorem prologue_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run listed [0x2a2b9] 7 ⟨s,f,0x2a2b0⟩ = some ⟨entered s,f,0x2a2b9⟩ := by
  simp [X86Routine.run,listed,X86Routine.execute,X86Control.execute,X86Block.execute,
    X86Memory.execute,blockPreservesFlags,entered,saved,X86Routine.pushWord,put,write]

def masked (s : X86Memory.State) := load32 s.memory (s.regs 3+104) &&& (0xfeffbffb#32)
def first (s : X86Memory.State) := store32 s.memory (s.regs 3+104) (masked s)
def grounded (s : X86Memory.State) :=
  PainHandoff.byteStore (first s) (s.regs 3+105) ((first s (s.regs 3+105)) &&& (0xfd#8))
def finalFlags (s : X86Memory.State) := load32 (grounded s) (s.regs 3+104) ||| (0x100400#32)
def height (s : X86Memory.State) := (load32 (grounded s) (s.regs 3+68)).sshiftRight 2
def resultMemory (s : X86Memory.State) := store32
  (store32 (grounded s) (s.regs 3+104) (finalFlags s)) (s.regs 3+68) (height s)
def result (s : X86Memory.State) : X86Control.State :=
  ⟨⟨write (write (write (write s.regs 2 (masked s)) 6 (load32 s.memory (s.regs 3+88)))
    7 (finalFlags s)) 5 (height s),resultMemory s⟩,none,0x2a2e6⟩

/-- Player branch. Type is loaded before the first flags store; memory aliasing
is otherwise retained in the exact machine result. -/
theorem corpse_execution (s : X86Memory.State) (f : Option Flags)
    (target : s.regs 2=s.regs 3) (kind : load32 s.memory (s.regs 3+88) ≠ 18) :
    X86Routine.run listed [0x2a2e6] 13 ⟨s,f,0x2a2b9⟩ = some (result s) := by
  have nz : load32 s.memory (s.regs 3+(88#32)) - (18#32) ≠ (0#32) := by
    intro eq
    apply kind
    have add := BitVec.eq_sub_iff_add_eq.mp eq.symm
    simpa using add.symm
  simp (maxSteps := 500000) [X86Routine.run,listed,X86Routine.execute,X86Control.execute,X86Block.execute,
    X86Memory.execute,blockPreservesFlags,X86Block.Address.eval,put,write,compare32,
    target,kind,nz,masked,first,grounded,finalFlags,height,resultMemory,result,PainHandoff.byteStore]
  constructor
  · funext r
    by_cases a : r=2 <;> by_cases b : r=5 <;> by_cases c : r=6 <;> by_cases d : r=7 <;>
      simp_all [write,PainHandoff.byteStore] <;> rfl
  · rfl


/-- The byte write clears NOGRAVITY without changing any other flag bit. -/
theorem byte_and_word (m : Memory) (a : Word) :
    load32 (PainHandoff.byteStore m (a+1) (m (a+1) &&& (0xfd#8))) a =
      load32 m a &&& (0xfffffdff#32) := by
  have h0 : a ≠ a+(1#32) := by
    simpa using (show a+(0#32) ≠ a+(1#32) by intro h; have := (BitVec.add_right_inj a).mp h; contradiction)
  have h2 : a+(2#32) ≠ a+(1#32) := by
    intro h; have := (BitVec.add_right_inj a).mp h; contradiction
  have h3 : a+(3#32) ≠ a+(1#32) := by
    intro h; have := (BitVec.add_right_inj a).mp h; contradiction
  simp only [load32,PainHandoff.byteStore,if_neg h0,if_neg h2,if_neg h3,ite_true]
  rw [show (0xfffffdff#32) = ((0xff#8 ++ 0xff#8) ++ (0xfd#8 ++ 0xff#8)) from by decide]
  rw [BitVec.and_append,BitVec.and_append,BitVec.and_append]
  have mask (v : BitVec 8) : v &&& (255#8) = v := BitVec.and_allOnes
  rw [mask,mask,mask]
  simp only [show (1 : Word)=(1#32) from rfl,show (2 : Word)=(2#32) from rfl,
    show (3 : Word)=(3#32) from rfl,if_neg h0,if_neg h2,if_neg h3]

def fields (s : X86Memory.State) := [s.regs 3+(104#32),s.regs 3+(68#32)]
theorem memory_frame (s : X86Memory.State) :
    PlayerHeight.Frame s.memory (resultMemory s) (fields s ++ [s.regs 3+(105#32)]) := by
  intro a safe
  unfold resultMemory grounded first
  repeat rw [load_store_apart _ _ _ _ (safe _ (by simp [fields]))]
  rw [PainHandoff.byteStore_word_apart _ _ _ _ (safe _ (by simp [fields]))]
  exact load_store_apart _ _ _ _ (safe _ (by simp [fields]))

structure CorpseInputs (s : X86Memory.State) (body : Death.Body) : Prop where
  target : s.regs 2=s.regs 3
  player : body.kind=0
  kind : load32 s.memory (s.regs 3+88)=0
  flags : load32 s.memory (s.regs 3+104)=body.flags.toBitVec
  tall : load32 s.memory (s.regs 3+68)=body.height.raw.toBitVec
  heightSafe : Apart (s.regs 3+68) (s.regs 3+104)
  byteSafe : Apart (s.regs 3+68) (s.regs 3+105)

theorem corpse_fields (s : X86Memory.State) (body : Death.Body) (h : CorpseInputs s body) :
    (load32 (resultMemory s) (s.regs 3+104),load32 (resultMemory s) (s.regs 3+68)) =
      ((Death.corpse body).flags.toBitVec,(Death.corpse body).height.raw.toBitVec) := by
  have fl : finalFlags s = (body.flags.toBitVec &&& (0xfeffbdfb#32)) ||| (0x100400#32) := by
    unfold finalFlags grounded
    rw [show s.regs 3+(105 : Word) = (s.regs 3+(104 : Word))+1 by simp [BitVec.add_assoc]]
    rw [byte_and_word,first,load_store,masked,h.flags,BitVec.and_assoc]
    rfl
  have ht : height s = body.height.raw.toBitVec.sshiftRight 2 := by
    unfold height grounded
    rw [PainHandoff.byteStore_word_apart _ _ _ _ h.byteSafe,first,load_store_apart _ _ _ _ h.heightSafe,h.tall]
  unfold resultMemory
  rw [load_store_apart _ _ _ _ (fun i j => (h.heightSafe j i).symm),load_store,load_store,fl,ht]
  simp [Death.corpse,h.player,BitVec.and_assoc,BitVec.or_assoc]


def setup (s : X86Memory.State) := entered (handed s)
def slots (s : X86Memory.State) := [s.regs 4-4,s.regs 4-8,s.regs 4-12,s.regs 4-16,s.regs 4-20,s.regs 4-24]

theorem setup_frame (s : X86Memory.State) : PlayerHeight.Frame s.memory (setup s).memory (slots s) := by
  intro a safe
  simp only [setup,entered,saved,handed,X86Routine.pushWord,put,write,↓reduceIte,BitVec.sub_sub]
  repeat rw [load_store_apart _ _ _ _ (safe _ (by simp [slots]))]

theorem setup_registers (s : X86Memory.State) :
    (setup s).regs 2=s.regs 6 ∧ (setup s).regs 3=s.regs 6 ∧
    (setup s).regs 1=load32 s.memory (s.regs 4+4) ∧ (setup s).regs 4=s.regs 4-24 := by
  simp [setup,entered,saved,handed,X86Routine.pushWord,put,write,BitVec.sub_sub]

theorem setup_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run listed [0x2a2b9] 10 ⟨s,f,0x2a6a6⟩ = some ⟨setup s,f,0x2a2b9⟩ := by
  simp (maxSteps := 500000) [X86Routine.run,listed,X86Routine.execute,X86Control.execute,X86Block.execute,
    X86Memory.execute,blockPreservesFlags,X86Block.Address.eval,setup,handed,entered,saved,X86Routine.pushWord,put,write]

structure Inputs (s : X86Memory.State) (body : Death.Body) : Prop where
  player : body.kind=0
  kind : load32 s.memory (s.regs 6+88)=0
  flags : load32 s.memory (s.regs 6+104)=body.flags.toBitVec
  tall : load32 s.memory (s.regs 6+68)=body.height.raw.toBitVec
  stackSafe : ∀ a, a ∈ [s.regs 6+88,s.regs 6+104,s.regs 6+68] → ∀ b, b ∈ slots s → Apart a b
  heightSafe : Apart (s.regs 6+68) (s.regs 6+104)
  byteSafe : Apart (s.regs 6+68) (s.regs 6+105)

theorem transport (s : X86Memory.State) (body : Death.Body) (h : Inputs s body) : CorpseInputs (setup s) body := by
  have regs := setup_registers s
  have keep (a : Word) (mem : a ∈ [s.regs 6+88,s.regs 6+104,s.regs 6+68]) :
      load32 (setup s).memory a=load32 s.memory a := setup_frame s a (h.stackSafe a mem)
  refine ⟨regs.1.trans regs.2.1.symm,h.player,?_,?_,?_,?_,?_⟩
  · rw [regs.2.1,keep _ (by simp),h.kind]
  · rw [regs.2.1,keep _ (by simp),h.flags]
  · rw [regs.2.1,keep _ (by simp),h.tall]
  · simpa [regs.2.1] using h.heightSafe
  · simpa [regs.2.1] using h.byteSafe

def final (s : X86Memory.State) := result (setup s)
theorem listed_active (pc : Nat) (h : listed pc ≠ none) : pc ∉ [0x2a2e6] := by
  simp only [List.mem_singleton]; intro eq; subst pc; contradiction

theorem execution (s : X86Memory.State) (f : Option Flags) (body : Death.Body) (h : Inputs s body) :
    X86Routine.run listed [0x2a2e6] 23 ⟨s,f,0x2a6a6⟩ = some (final s) := by
  obtain ⟨n,hn,path,_⟩ := X86Routine.run_path (setup_execution s f)
  have path := path.transfer listed [0x2a2e6] (fun _ _ => rfl) listed_active
  have ins := transport s body h
  exact path.finish (corpse_execution (setup s) f ins.target (by rw [ins.kind]; decide)) 23 (by omega)

theorem original_execution (s : X86Memory.State) (f : Option Flags) (body : Death.Body) (h : Inputs s body) :
    X86Routine.run program [0x2a2e6] 23 ⟨s,f,0x2a6a6⟩ = some (final s) := by
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [execution s f body h]; simp)]
  exact execution s f body h


def writes (s : X86Memory.State) := slots s ++ [s.regs 6+104,s.regs 6+68,s.regs 6+105]
theorem final_frame (s : X86Memory.State) : PlayerHeight.Frame s.memory (final s).core.memory (writes s) := by
  intro a safe
  change load32 (resultMemory (setup s)) a = _
  rw [memory_frame (setup s) a]
  · exact setup_frame s a (fun b hb => safe b (by simp [writes,hb]))
  · intro b hb
    apply safe
    simpa [fields,(setup_registers s).2.1,writes] using Or.inr hb

theorem setup_return (s : X86Memory.State) :
    load32 (setup s).memory (s.regs 4-4)=0x2a6b1 := by
  simp [setup,entered,saved,handed,X86Routine.pushWord,put,write,BitVec.sub_sub]
  rw [load_store_apart _ _ _ _ (show Apart (s.regs 4-(4#32)) (s.regs 4-(24#32)) from by simpa using DeathStack.slots_apart (s.regs 4) ⟨1,by decide⟩ ⟨6,by decide⟩ (by decide)),
    load_store_apart _ _ _ _ (show Apart (s.regs 4-(4#32)) (s.regs 4-(20#32)) from by simpa using DeathStack.slots_apart (s.regs 4) ⟨1,by decide⟩ ⟨5,by decide⟩ (by decide)),
    load_store_apart _ _ _ _ (show Apart (s.regs 4-(4#32)) (s.regs 4-(16#32)) from by simpa using DeathStack.slots_apart (s.regs 4) ⟨1,by decide⟩ ⟨4,by decide⟩ (by decide)),
    load_store_apart _ _ _ _ (show Apart (s.regs 4-(4#32)) (s.regs 4-(12#32)) from by simpa using DeathStack.slots_apart (s.regs 4) ⟨1,by decide⟩ ⟨3,by decide⟩ (by decide)),
    load_store_apart _ _ _ _ (show Apart (s.regs 4-(4#32)) (s.regs 4-(8#32)) from by simpa using DeathStack.slots_apart (s.regs 4) ⟨1,by decide⟩ ⟨2,by decide⟩ (by decide)),load_store]

def exits : List Nat := [0x2a2e6,0x2a6b6,0x2a747]
def joined : X86Routine.Program := fun pc =>
  if (0x2a6a6 ≤ pc ∧ pc < 0x2a6b1) ∨ (0x2a2b0 ≤ pc ∧ pc < 0x2a2e6) then program pc
  else ActorHealth.joined pc

theorem contains_previous (pc : Nat) (h : ActorHealth.joined pc ≠ none) : joined pc = ActorHealth.joined pc := by
  unfold joined
  split
  next yes =>
    have b1 : ¬(0x2a650 ≤ pc ∧ pc < 0x2a6a6) := by omega
    have b2 : ¬(0x1bb50 ≤ pc ∧ pc < 0x1bb66) := by omega
    have b3 : ¬(0x1bc41 ≤ pc ∧ pc < 0x1bc45) := by omega
    have b4 : ¬(0x2a616 ≤ pc ∧ pc < 0x2a650) := by omega
    have b5 : ¬(0x2a460 ≤ pc ∧ pc < 0x2a5d5) := by omega
    have b6 : ¬(0x2a5d5 ≤ pc ∧ pc < 0x2a616) := by omega
    simp [ActorHealth.joined,PlayerHealth.joined,PlayerDamageEntry.program,PlayerDamageEntry.bytesProgram,
      b1,b2,b3,b4,b5,b6,show pc ≠ 0x2fb76 by omega,show pc ≠ 0x2fba0 by omega,show pc ≠ 0x2fbd2 by omega] at h
  next => rfl

theorem previous_active (pc : Nat) (h : ActorHealth.joined pc ≠ none) : pc ∉ exits := by
  intro mem
  simp only [exits,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at mem
  rcases mem with rfl | rfl | rfl <;> contradiction

theorem contains_kill (pc : Nat) (h : program pc ≠ none) : joined pc = program pc := by
  unfold joined
  split
  next => rfl
  next hn =>
    have a : ¬(0x2a6a6 ≤ pc ∧ pc < 0x2a6b1) := by omega
    have b : ¬(0x2a2b0 ≤ pc ∧ pc < 0x2a2e6) := by omega
    simp [program,bytesProgram,a,b] at h

theorem kill_active (pc : Nat) (h : program pc ≠ none) : pc ∉ exits := by
  intro mem
  simp only [exits,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at mem
  rcases mem with rfl | rfl | rfl <;> contradiction

def initialReads (s : X86Memory.State) := [s.regs 0+88,s.regs 0+104,s.regs 0+68]
def callSlots (s : X86Memory.State) := [s.regs 4-32,s.regs 4-36,s.regs 4-40,s.regs 4-44,s.regs 4-48,s.regs 4-52]
def suffixWrites (s : X86Memory.State) := callSlots s ++ [s.regs 0+104,s.regs 0+68,s.regs 0+105]
def retained (s : X86Memory.State) := ActorHealth.fields s ++ [s.regs 0+108]
structure JoinedInputs (s : X86Memory.State) (v : PlayerDamage.State) (d : Int32) (baby : Bool)
    (body : Death.Body) extends toActor : ActorHealth.JoinedInputs s v d baby where
  player : body.kind=0
  kind : load32 s.memory (s.regs 0+88)=0
  flags : load32 s.memory (s.regs 0+104)=body.flags.toBitVec
  tall : load32 s.memory (s.regs 0+68)=body.height.raw.toBitVec
  readsSafe : ∀ a, a ∈ initialReads s → ∀ b, b ∈ ActorHealth.joinedWrites s → Apart a b
  killStackSafe : ∀ a, a ∈ initialReads s → ∀ b, b ∈ callSlots s → Apart a b
  heightSafe : Apart (s.regs 0+68) (s.regs 0+104)
  byteSafe : Apart (s.regs 0+68) (s.regs 0+105)
  sourceSafe : ∀ b, b ∈ ActorHealth.afterWrites s → Apart (s.regs 4-24) b
  retainedSafe : ∀ a, a ∈ retained s → ∀ b, b ∈ suffixWrites s → Apart a b

def damageFields (s : X86Memory.State) (m : Memory) :=
  let p := PlayerDamageEntry.inputPlayer s
  ((load32 m (p+36),load32 m (p+40),load32 m (p+32),load32 m (p+220),load32 m (p+228)),
    load32 m (s.regs 0+108))
def liveDamageFields (out : PlayerDamage.Result) :=
  ((out.state.armor.toBitVec,out.state.armorType.toBitVec,out.state.playerHealth.toBitVec,
    out.state.damageCount.toBitVec,(0#32)),out.state.health.toBitVec)
def observation (s : X86Memory.State) (t : X86Control.State) :=
  (damageFields s t.core.memory,load32 t.core.memory (s.regs 0+104),load32 t.core.memory (s.regs 0+68))
def liveObservation (out : PlayerDamage.Result) (body : Death.Body) :=
  (liveDamageFields out,(Death.corpse body).flags.toBitVec,(Death.corpse body).height.raw.toBitVec)


/-- Continuous lethal damage CALL through the kill CALL and corpse setup. Credit,
weapon lowering, death-state entry and both returns are subsequent obligations. -/
def stackWrites (s : X86Memory.State) := ActorHealth.afterWrites s ++ suffixWrites s
def returnWrites (s : X86Memory.State) : List Word := [s.regs 0+104,s.regs 0+68,s.regs 0+105]

theorem joined_execution_tracked (s : X86Memory.State) (f : Option Flags) (pc : Nat)
    (site : pc ∈ PlayerDamageEntry.sites) (v : PlayerDamage.State) (d : Int32) (baby : Bool)
    (rng : DoomRandom) (body : Death.Body) (h : JoinedInputs s v d baby body)
    (dead : (PlayerDamage.apply v d none false baby rng).killed=true) :
    ∃ t,
      DeathStack.Saved s pc t.core.memory (stackWrites s) (returnWrites s) ∧ X86Routine.run joined exits 131 ⟨s,f,pc⟩ = some t ∧
      observation s t = liveObservation (PlayerDamage.apply v d none false baby rng) body ∧
      t.pc=0x2a2e6 ∧ t.core.regs 1=0 ∧ t.core.regs 3=s.regs 0 ∧
      t.core.regs 4=s.regs 4-(52#32) ∧
      PlayerHeight.Frame s.memory t.core.memory (ActorHealth.joinedWrites s ++ suffixWrites s) := by
  have yes : (PlayerDamage.apply v d none false baby rng).applied=true := by
    by_cases yes : (PlayerDamage.apply v d none false baby rng).applied=true
    · exact yes
    · have no : (PlayerDamage.apply v d none false baby rng).applied=false := by simpa using yes
      rw [(DamageRejected.rejected_live v d baby rng h.liveSkull h.liveOrdinary no).2] at dead
      contradiction
  obtain ⟨g,grun,gobs,gsp,gobj,gframe,gsaved⟩ :=
    ActorHealth.joined_execution_detailed s f pc site v d baby h.toActor
  rw [← ActorHealth.live_answer v d baby rng h.liveSkull h.liveOrdinary] at gobs
  have gp : g.pc=0x2a6a6 := by
    have obs := congrArg Prod.snd gobs
    by_cases reject : g.pc=0x2a747
    · simp [ActorHealth.observation,ActorHealth.liveObservation,reject,yes] at obs
    · simp only [ActorHealth.observation,ActorHealth.liveObservation,reject,if_false,yes,if_true,
        Option.some.injEq,Prod.mk.injEq,dead] at obs
      exact of_decide_eq_true obs.2
  have source : load32 g.core.memory (g.core.regs 4+4)=0 := by
    rw [gsp,show s.regs 4-(28#32)+4 = s.regs 4-24 by simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]]
    rw [gsaved _ h.sourceSafe]
    exact (DamageReturn.saved_slots s pc).2.2.2.2.trans h.source
  have slotsEq : slots g.core = callSlots s := by simp [slots,callSlots,gsp,BitVec.sub_sub]
  have ins : Inputs g.core body := by
    have keep (a : Word) (ha : a ∈ initialReads s) : load32 g.core.memory a=load32 s.memory a :=
      gframe a (h.readsSafe a ha)
    refine ⟨h.player,?_,?_,?_,?_,?_,?_⟩
    · rw [gobj,keep _ (by simp [initialReads]),h.kind]
    · rw [gobj,keep _ (by simp [initialReads]),h.flags]
    · rw [gobj,keep _ (by simp [initialReads]),h.tall]
    · intro a ha b hb
      rw [gobj] at ha; rw [slotsEq] at hb
      exact h.killStackSafe a ha b hb
    · simpa [gobj] using h.heightSafe
    · simpa [gobj] using h.byteSafe
  have wr : writes g.core = suffixWrites s := by simp [writes,suffixWrites,slotsEq,gobj]
  have preserve (a : Word) (ha : a ∈ retained s) : load32 (final g.core).core.memory a = load32 g.core.memory a := by
    apply final_frame
    intro b hb; rw [wr] at hb; exact h.retainedSafe a ha b hb
  have damage : damageFields s g.core.memory = liveDamageFields (PlayerDamage.apply v d none false baby rng) := by
    simp only [ActorHealth.observation,ActorHealth.liveObservation,PlayerHealth.observation,
      PlayerHealth.liveObservation,gp,yes,if_true,show (0x2a6a6:Nat) ≠ 0x2a747 by decide,if_false,
      Option.some.injEq,Prod.mk.injEq] at gobs
    simp only [damageFields,liveDamageFields,Prod.mk.injEq]
    exact ⟨gobs.1.2,gobs.2.1⟩
  have keepDamage : damageFields s (final g.core).core.memory=damageFields s g.core.memory := by
    unfold damageFields
    dsimp only
    repeat rw [preserve _ (by simp [retained,ActorHealth.fields])]
  have corpse := corpse_fields (setup g.core) body (transport g.core body ins)
  rw [(setup_registers g.core).2.1,gobj] at corpse
  obtain ⟨n,hn,path,_⟩ := X86Routine.run_path grun
  have path := path.transfer joined exits contains_previous previous_active
  have tailrun := original_execution g.core g.flags body ins
  rw [← gp] at tailrun
  obtain ⟨k,hk,tail,_⟩ := X86Routine.run_path tailrun
  have tail := tail.transfer joined exits contains_kill kill_active
  have tailrun : X86Routine.run joined exits 23 g = some (final g.core) :=
    tail.finish (fuel := 0) (by simp [X86Routine.run,final,result,exits]) 23 (by omega)
  have tracked : DeathStack.Saved s pc (final g.core).core.memory (stackWrites s) (returnWrites s) := by
    constructor
    · intro a safe
      rw [final_frame g.core a]
      · exact gsaved a (fun b hb => safe b (List.mem_append_left _ hb))
      · intro b hb; rw [wr] at hb; exact safe b (List.mem_append_right _ hb)
    · intro safe
      have addr : s.regs 4-(32#32)=g.core.regs 4-4 := by rw [gsp]; simp [BitVec.sub_sub]
      change load32 (resultMemory (setup g.core)) (s.regs 4-32)=_
      rw [memory_frame (setup g.core) (s.regs 4-32)]
      · change load32 (setup g.core).memory (s.regs 4-(32#32))=_
        rw [addr]; exact setup_return g.core
      · intro b hb
        apply safe
        simpa [fields,(setup_registers g.core).2.1,gobj,returnWrites] using hb
  refine ⟨final g.core,tracked,path.finish tailrun 131 (by omega),?_,rfl,?_,?_,?_,?_⟩
  · exact Prod.ext (keepDamage.trans damage) corpse
  · change (setup g.core).regs 1=0
    exact (setup_registers g.core).2.2.1.trans source
  · simp [final,result,(setup_registers g.core).2.1,write,gobj]
  · simp [final,result,(setup_registers g.core).2.2.2,write,gsp,BitVec.sub_sub]
  · intro a safe
    rw [final_frame g.core a]
    · exact gframe a (fun b hb => safe b (by simp [hb]))
    · intro b hb; rw [wr] at hb; exact safe b (by simp [hb])

theorem joined_execution (s : X86Memory.State) (f : Option Flags) (pc : Nat)
    (site : pc ∈ PlayerDamageEntry.sites) (v : PlayerDamage.State) (d : Int32) (baby : Bool)
    (rng : DoomRandom) (body : Death.Body) (h : JoinedInputs s v d baby body)
    (dead : (PlayerDamage.apply v d none false baby rng).killed=true) :
    ∃ t, X86Routine.run joined exits 131 ⟨s,f,pc⟩ = some t ∧
      observation s t = liveObservation (PlayerDamage.apply v d none false baby rng) body ∧
      t.pc=0x2a2e6 ∧ t.core.regs 1=0 ∧ t.core.regs 3=s.regs 0 ∧
      t.core.regs 4=s.regs 4-(52#32) ∧
      PlayerHeight.Frame s.memory t.core.memory (ActorHealth.joinedWrites s ++ suffixWrites s) := by
  obtain ⟨t,_,rest⟩ :=
    joined_execution_tracked s f pc site v d baby rng body h dead
  exact ⟨t,rest⟩

theorem live_correspondence (s : X86Memory.State) (f : Option Flags) (pc : Nat)
    (site : pc ∈ PlayerDamageEntry.sites) (v : PlayerDamage.State) (d : Int32) (baby : Bool)
    (rng : DoomRandom) (body : Death.Body) (h : JoinedInputs s v d baby body)
    (dead : (PlayerDamage.apply v d none false baby rng).killed=true) :
    (X86Routine.run joined exits 131 ⟨s,f,pc⟩).map (observation s) =
      some (liveObservation (PlayerDamage.apply v d none false baby rng) body) := by
  obtain ⟨t,run,obs,_⟩ := joined_execution s f pc site v d baby rng body h dead
  simp [run,obs]

end Doom.Proofs.KillEntry



