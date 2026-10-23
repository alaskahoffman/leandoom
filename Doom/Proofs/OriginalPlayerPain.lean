import Doom.Proofs.OriginalActorHealth

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
namespace Doom.Proofs.PlayerPain
open Verification X86 X86Memory X86Control BlockSummary
open FloorDamage (nextIndex randomMemory increment_index mask_byte randomByte random_value)

def painBytes : List UInt8 := [0x8b,0x56,0x5c,0xe8,0xa2,0x9a,0xff,0xff,0x3b,0x42,0x20,0x7d,0x1c,0xf6,0x46,0x6b,0x1,0x75,0x16]
def bytesProgram (pain rng : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2a6b6 ≤ pc ∧ pc < 0x2a6c9 then X86Routine.decodeAt pain (pc-0x2a6b6)
  else if 0x24160 ≤ pc ∧ pc < 0x2417c then X86Routine.decodeAt rng (pc-0x24160)
  else none

def program := bytesProgram painBytes Doom19.playRandomBytes

def rngListed : X86Routine.Program
  | 0x24160 => some (.control (.block (.load 0 ⟨none,none,0,0x12720⟩)),5)
  | 0x24165 => some (.addImmediate 0 1,1)
  | 0x24166 => some (.control (.andEax 255),5)
  | 0x2416b => some (.control (.storeEax 0x12720),5)
  | 0x24170 => some (.control (.loadByte 0 ⟨some 0,none,0,0x1261c⟩),6)
  | 0x24176 => some (.control (.andEax 255),5)
  | 0x2417b => some (.ret,1)
  | _ => none

def randomEnd (s : X86Memory.State) (i : UInt8) (b : BitVec 8) : X86Control.State :=
  ⟨⟨write (write s.regs 0 (b.zeroExtend 32)) 4 (s.regs 4+(4#32)),randomMemory s i⟩,
    some (logical32 (b.zeroExtend 32)),0x2a6be⟩

/-- Real P_Random instructions and RET in the shared byte-addressed memory.
Table/return reads are from memory after the index write, so aliasing is never
silently discarded by the instruction proof. -/
theorem random_execution (s : X86Memory.State) (f : Option Flags) (i : UInt8) (b : BitVec 8)
    (index : load32 s.memory (0x12720#32) = BitVec.ofNat 32 i.toNat)
    (table : randomMemory s i ((0x1261c#32)+nextIndex i) = b)
    (ret : load32 (randomMemory s i) (s.regs 4) = (0x2a6be#32)) :
    X86Routine.run rngListed [0x2a6be] 7 ⟨s,f,0x24160⟩ = some (randomEnd s i b) := by
  let c1 := put s 0 (BitVec.ofNat 32 i.toNat)
  let c2 := put c1 0 (BitVec.ofNat 32 i.toNat+1)
  let c3 := put c2 0 (nextIndex i)
  let c4 : X86Memory.State := { c3 with memory := randomMemory s i }
  let c5 := putByte c4 0 b
  let c6 := put c5 0 (b.zeroExtend 32)
  have path : X86Routine.Prefix rngListed [0x2a6be] 7 ⟨s,f,0x24160⟩
      ⟨put c6 4 (s.regs 4+4),some (logical32 (b.zeroExtend 32)),0x2a6be⟩ := by
    apply X86Routine.Prefix.step (middle := ⟨c1,f,0x24165⟩) (by simp) (show rngListed 0x24160 = _ from rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,c1,index])
    apply X86Routine.Prefix.step (middle := ⟨c2,none,0x24166⟩) (by simp) (show rngListed 0x24165 = _ from rfl) (by
      simp [X86Routine.execute,c2,c1,put,write])
    apply X86Routine.Prefix.step (middle := ⟨c3,some (logical32 (nextIndex i)),0x2416b⟩) (by simp) (show rngListed 0x24166 = _ from rfl) (by
      simp [X86Routine.execute,X86Control.execute,c3,c2,c1,put,write,increment_index])
    apply X86Routine.Prefix.step (middle := ⟨c4,some (logical32 (nextIndex i)),0x24170⟩) (by simp) (show rngListed 0x2416b = _ from rfl) (by
      simp [X86Routine.execute,X86Control.execute,c4,c3,c2,c1,put,write,randomMemory])
    apply X86Routine.Prefix.step (middle := ⟨c5,some (logical32 (nextIndex i)),0x24176⟩) (by simp) (show rngListed 0x24170 = _ from rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.Address.eval,c5,c4,c3,c2,c1,put,write,BitVec.add_comm,table,eax])
    apply X86Routine.Prefix.step (middle := ⟨c6,some (logical32 (b.zeroExtend 32)),0x2417b⟩) (by simp) (show rngListed 0x24176 = _ from rfl) (by
      simp [X86Routine.execute,X86Control.execute,c6,c5,putByte,byteReg,put,write,mask_byte,eax])
    apply X86Routine.Prefix.step (middle := ⟨put c6 4 (s.regs 4+4),some (logical32 (b.zeroExtend 32)),0x2a6be⟩)
      (by simp) (show rngListed 0x2417b = _ from rfl) (by
        simp [X86Routine.execute,c6,c5,c4,c3,c2,c1,putByte,byteReg,put,write,ret])
    exact X86Routine.Prefix.nil _
  rw [show 7 = 7+0 from rfl,path.run 0]
  simp [X86Routine.run,randomEnd,c6,c5,c4,c3,c2,c1,putByte,byteReg,put,write]
  funext r
  by_cases h0 : r=0 <;> by_cases h4 : r=4 <;> simp_all [write]

def decisionListed : X86Routine.Program
  | 0x2a6be => some (.control (.cmpMemory 0 ⟨some 2,none,0,32⟩),3)
  | 0x2a6c1 => some (.jumpSigned 0 28,2)
  | 0x2a6c3 => some (.testMemoryByte ⟨some 6,none,0,107⟩ 1,4)
  | 0x2a6c7 => some (.control (.jumpZero false 22),2)
  | _ => none

def listed : X86Routine.Program := fun pc =>
  if pc = 0x2a6b6 then some (.control (.block (.legacy (.load 2 6 92))),3)
  else if pc = 0x2a6b9 then some (.call (-25950),5)
  else if 0x24160 ≤ pc ∧ pc < 0x2417c then rngListed pc else decisionListed pc

theorem decoded (pc : Nat) (h : listed pc ≠ none) : program pc = listed pc := by
  unfold listed at h ⊢
  split <;> (try next hp => subst pc; decide)
  split <;> (try next hp => subst pc; decide)
  split
  · fun_cases rngListed pc <;> simp_all [rngListed] <;> decide
  · fun_cases decisionListed pc <;> simp_all [decisionListed] <;> decide

def decisionEnd (s : X86Memory.State) : X86Control.State :=
  if (s.regs 0).toInt < (load32 s.memory (s.regs 2+(32#32))).toInt then
    ⟨s,some (logical8 (s.memory (s.regs 6+(107#32)) &&& (1#8))),
      if s.memory (s.regs 6+(107#32)) &&& (1#8) = (0#8) then 0x2a6c9 else 0x2a6df⟩
  else ⟨s,some (compare32 (s.regs 0) (load32 s.memory (s.regs 2+(32#32)))),0x2a6df⟩

/-- All signed pain chances and skull-flight flags, independently of player restrictions. -/
theorem decision_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run decisionListed [0x2a6c9,0x2a6df] 4 ⟨s,f,0x2a6be⟩ = some (decisionEnd s) := by
  by_cases small : (s.regs 0).toInt < (load32 s.memory (s.regs 2+(32#32))).toInt
  · have nge : ¬ (load32 s.memory (s.regs 2+(32#32))).toInt ≤ (s.regs 0).toInt := by omega
    by_cases skull : s.memory (s.regs 6+(107#32)) &&& (1#8) = (0#8) <;>
      simp [X86Routine.run,decisionListed,X86Routine.execute,X86Control.execute,
        X86Block.Address.eval,PlayerHeight.cmp_ge_prop,nge,decisionEnd,small,logical8,skull]
  · have ge : (load32 s.memory (s.regs 2+(32#32))).toInt ≤ (s.regs 0).toInt := by omega
    simp [X86Routine.run,decisionListed,X86Routine.execute,X86Control.execute,
      X86Block.Address.eval,PlayerHeight.cmp_ge_prop,ge,decisionEnd,small]

def info (s : X86Memory.State) := load32 s.memory (s.regs 6+(92#32))
def called (s : X86Memory.State) : X86Memory.State :=
  ⟨write (write s.regs 2 (info s)) 4 (s.regs 4-(4#32)),
    store32 s.memory (s.regs 4-(4#32)) (0x2a6be#32)⟩
def resultMemory (s : X86Memory.State) (i : UInt8) := randomMemory (called s) i
def rolled (s : X86Memory.State) (i : UInt8) :=
  (randomEnd (called s) i (randomByte i)).core

def reads (s : X86Memory.State) (i : UInt8) : List Word :=
  [info s+(32#32),s.regs 6+(107#32),(0x1261c#32)+nextIndex i]
structure Inputs (s : X86Memory.State) (i : UInt8) : Prop where
  index : load32 s.memory (0x12720#32) = BitVec.ofNat 32 i.toNat
  table : s.memory ((0x1261c#32)+nextIndex i) = randomByte i
  chance : load32 s.memory (info s+(32#32)) = (255#32)
  noSkull : s.memory (s.regs 6+(107#32)) &&& (1#8) = (0#8)
  indexSafe : Apart (0x12720#32) (s.regs 4-(4#32))
  readsSafe : ∀ a, a ∈ reads s i → Apart a (s.regs 4-(4#32)) ∧ Apart a (0x12720#32)

def writes (s : X86Memory.State) : List Word := [s.regs 4-(4#32),(0x12720#32)]
theorem memory_frame (s : X86Memory.State) (i : UInt8) :
    PlayerHeight.Frame s.memory (resultMemory s i) (writes s) := by
  intro a safe
  unfold resultMemory randomMemory called
  rw [load_store_apart _ _ _ _ (safe _ (by simp [writes])),
    load_store_apart _ _ _ _ (safe _ (by simp [writes]))]

theorem rolled_regs (s : X86Memory.State) (i : UInt8) :
    (rolled s i).regs = write (write s.regs 2 (info s)) 0 ((randomByte i).zeroExtend 32) := by
  funext r
  by_cases h0 : r=0 <;> by_cases h2 : r=2 <;> by_cases h4 : r=4 <;>
    simp [rolled,randomEnd,called,write,h0,h2,h4,BitVec.sub_eq_add_neg,BitVec.add_assoc]

theorem call_prefix (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix listed [0x2a6c9,0x2a6df] 2 ⟨s,f,0x2a6b6⟩ ⟨called s,f,0x24160⟩ := by
  apply X86Routine.Prefix.step (middle := ⟨put s 2 (info s),f,0x2a6b9⟩) (by simp)
    (show listed 0x2a6b6 = _ from rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,blockPreservesFlags,info])
  apply X86Routine.Prefix.step (middle := ⟨called s,f,0x24160⟩) (by simp)
    (show listed 0x2a6b9 = _ from rfl) (by
      simp [X86Routine.execute,X86Routine.pushWord,called,put,write])
  exact X86Routine.Prefix.nil _

theorem execution (s : X86Memory.State) (f : Option Flags) (i : UInt8) (h : Inputs s i) :
    X86Routine.run listed [0x2a6c9,0x2a6df] 13 ⟨s,f,0x2a6b6⟩ = some (decisionEnd (rolled s i)) := by
  have keep (a : Word) (ha : a ∈ reads s i) : load32 (resultMemory s i) a = load32 s.memory a :=
    memory_frame s i a (by intro b hb; simp only [writes,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hb; rcases hb with rfl | rfl; exact (h.readsSafe a ha).1; exact (h.readsSafe a ha).2)
  have byte (a : Word) (ha : a ∈ reads s i) : resultMemory s i a = s.memory a :=
    (memory_frame s i).byte a (by intro b hb; simp only [writes,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hb; rcases hb with rfl | rfl; exact (h.readsSafe a ha).1; exact (h.readsSafe a ha).2)
  have index : load32 (called s).memory (0x12720#32) = BitVec.ofNat 32 i.toNat := by
    rw [called,load_store_apart _ _ _ _ h.indexSafe,h.index]
  have table : randomMemory (called s) i ((0x1261c#32)+nextIndex i) = randomByte i :=
    (byte _ (by simp [reads])).trans h.table
  have ret : load32 (randomMemory (called s) i) ((called s).regs 4) = (0x2a6be#32) := by
    have safe : Apart (s.regs 4-(4#32)) (0x12720#32) := by
      intro a b eq; exact h.indexSafe b a eq.symm
    simpa [randomMemory,called,write,load_store_apart _ _ _ _ safe,load_store]
  obtain ⟨n,hn,rpath,_⟩ := X86Routine.run_path (random_execution (called s) f i (randomByte i) index table ret)
  have rpath := rpath.transfer listed [0x2a6c9,0x2a6df]
    (by intro pc hp; fun_cases rngListed pc <;> simp_all [rngListed,listed])
    (by intro pc hp; fun_cases rngListed pc <;> simp_all [rngListed])
  obtain ⟨k,hk,dpath,done⟩ := X86Routine.run_path (decision_execution (rolled s i) (randomEnd (called s) i (randomByte i)).flags)
  have dpath := dpath.transfer listed [0x2a6c9,0x2a6df]
    (by intro pc hp; fun_cases decisionListed pc <;> simp_all [decisionListed,listed])
    (by intro pc hp; fun_cases decisionListed pc <;> simp_all [decisionListed])
  have tail : X86Routine.run listed [0x2a6c9,0x2a6df] 4 (randomEnd (called s) i (randomByte i)) = some (decisionEnd (rolled s i)) :=
    dpath.finish (fuel := 0) (by simp [X86Routine.run,done]) 4 (by omega)
  exact (call_prefix s f).finish (rpath.finish tail 11 (by omega)) 13 (by omega)

theorem original_execution (s : X86Memory.State) (f : Option Flags) (i : UInt8) (h : Inputs s i) :
    X86Routine.run program [0x2a6c9,0x2a6df] 13 ⟨s,f,0x2a6b6⟩ = some (decisionEnd (rolled s i)) := by
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [execution s f i h]; simp)]
  exact execution s f i h

/-- The most significant byte can be framed via its containing word. This
avoids demanding separation between the flag byte at +107 and health at +108. -/
theorem high_byte (m : Memory) (a : Word) : (load32 m a).extractLsb' 24 8 = m (a+(3#32)) := by
  have fact (a b c d : BitVec 8) : ((a ++ b ++ (c ++ d)) : BitVec 32).extractLsb' 24 8 = a := by bv_decide
  exact fact _ _ _ _

theorem frame_high_byte {m m' : Memory} {ws : List Word} (h : PlayerHeight.Frame m m' ws)
    (a : Word) (safe : ∀ b, b ∈ ws → Apart a b) : m' (a+(3#32)) = m (a+(3#32)) := by
  have eq := congrArg (fun v : Word => v.extractLsb' 24 8) (h a safe)
  simpa only [high_byte] using eq

theorem result_core (s : X86Memory.State) (i : UInt8) :
    (decisionEnd (rolled s i)).core = rolled s i := by
  unfold decisionEnd; split <;> rfl

theorem result_pc (s : X86Memory.State) (i : UInt8) (h : Inputs s i) :
    (decisionEnd (rolled s i)).pc = if randomAt (i+1) < 255 then 0x2a6c9 else 0x2a6df := by
  have safe (a : Word) (ha : a ∈ reads s i) : ∀ b, b ∈ writes s → Apart a b := by
    intro b hb
    simp only [writes,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hb
    rcases hb with rfl | rfl
    · exact (h.readsSafe a ha).1
    · exact (h.readsSafe a ha).2
  have chance := (memory_frame s i (info s+(32#32)) (safe _ (by simp [reads]))).trans h.chance
  have skull : resultMemory s i (s.regs 6+(107#32)) &&& (1#8) = (0#8) := by
    rw [(memory_frame s i).byte _ (safe _ (by simp [reads])),h.noSkull]
  have val : ((randomByte i).zeroExtend 32).toInt = (randomAt (i+1) : Int) := by
    have bound := (randomByte i).isLt
    rw [BitVec.toInt_eq_toNat_of_lt (by simp only [BitVec.toNat_setWidth]; omega)]
    simp only [BitVec.toNat_setWidth]
    rw [Nat.mod_eq_of_lt (by omega),random_value]
  simp only [decisionEnd,rolled_regs,write,ite_true,
    show (6:Reg) ≠ 0 by decide,show (6:Reg) ≠ 2 by decide,
    show (2:Reg) ≠ 0 by decide,ite_false]
  have mem : (rolled s i).memory = resultMemory s i := rfl
  rw [mem,chance,val]
  have hc : (randomAt (i+1) : Int) < (255:Int) ↔ randomAt (i+1) < 255 := by omega
  simp only [show (255#32).toInt = (255:Int) from rfl,hc]
  split <;> simp_all


def exits : List Nat := [0x2a6a6,0x2a6c9,0x2a6df,0x2a747]
def joined (pc : Nat) : Option (X86Routine.Op × Nat) :=
  if (0x2a6b6 ≤ pc ∧ pc < 0x2a6c9) ∨ (0x24160 ≤ pc ∧ pc < 0x2417c) then program pc
  else ActorHealth.joined pc

theorem contains_actor (pc : Nat) (h : ActorHealth.joined pc ≠ none) : joined pc = ActorHealth.joined pc := by
  unfold joined
  split
  next bounds =>
    have b1 : ¬(0x2a650 ≤ pc ∧ pc < 0x2a6a6) := by omega
    have b2 : ¬(0x1bb50 ≤ pc ∧ pc < 0x1bb66) := by omega
    have b3 : ¬(0x1bc41 ≤ pc ∧ pc < 0x1bc45) := by omega
    have b4 : ¬(0x2a616 ≤ pc ∧ pc < 0x2a650) := by omega
    have b5 : ¬(0x2a460 ≤ pc ∧ pc < 0x2a5d5) := by omega
    have b6 : ¬(0x2a5d5 ≤ pc ∧ pc < 0x2a616) := by omega
    simp [ActorHealth.joined,PlayerHealth.joined,PlayerDamageEntry.program,PlayerDamageEntry.bytesProgram,
      b1,b2,b3,b4,b5,b6,show pc ≠ 0x2fb76 by omega,show pc ≠ 0x2fba0 by omega,show pc ≠ 0x2fbd2 by omega] at h
  next => rfl

theorem actor_active (pc : Nat) (h : ActorHealth.joined pc ≠ none) : pc ∉ exits := by
  intro hm
  simp only [exits,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl <;> contradiction

theorem contains_pain (pc : Nat) (h : program pc ≠ none) : joined pc = program pc := by
  unfold joined
  split
  next => rfl
  next hn =>
    simp [program,bytesProgram,show ¬(0x2a6b6 ≤ pc ∧ pc < 0x2a6c9) by omega,
      show ¬(0x24160 ≤ pc ∧ pc < 0x2417c) by omega] at h

theorem pain_active (pc : Nat) (h : program pc ≠ none) : pc ∉ exits := by
  intro hm
  simp only [exits,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl <;> contradiction

def inputInfo (s : X86Memory.State) := load32 s.memory (s.regs 0+(92#32))
def prefixReads (s : X86Memory.State) (i : UInt8) : List Word :=
  [(0x12720#32),s.regs 0+(92#32),inputInfo s+(32#32),s.regs 0+(104#32),(0x1261c#32)+nextIndex i]
def suffixReads (s : X86Memory.State) (i : UInt8) : List Word :=
  [inputInfo s+(32#32),s.regs 0+(107#32),(0x1261c#32)+nextIndex i] ++
    ActorHealth.fields s ++ [s.regs 0+(108#32)]
def suffixWrites (s : X86Memory.State) : List Word := [s.regs 4-(32#32),(0x12720#32)]
structure JoinedInputs (s : X86Memory.State) (v : PlayerDamage.State) (d : Int32) (baby : Bool) (i : UInt8)
    extends toActor : ActorHealth.JoinedInputs s v d baby where
  index : load32 s.memory (0x12720#32) = BitVec.ofNat 32 i.toNat
  table : s.memory ((0x1261c#32)+nextIndex i) = randomByte i
  chance : load32 s.memory (inputInfo s+(32#32)) = (255#32)
  prefixSafe : ∀ a, a ∈ prefixReads s i → ∀ b, b ∈ ActorHealth.joinedWrites s → Apart a b
  indexSafe : Apart (0x12720#32) (s.regs 4-(32#32))
  suffixSafe : ∀ a, a ∈ suffixReads s i → ∀ b, b ∈ suffixWrites s → Apart a b

def survives (v : PlayerDamage.State) (d : Int32) (baby : Bool) : Bool :=
  PlayerDamageEntry.accepted v d baby &&
    !decide (v.health-(PlayerDamage.absorbArmor v (PlayerDamageEntry.skillDamage d baby)).2 ≤ 0)
def observation (s : X86Memory.State) (t : X86Control.State) :=
  (ActorHealth.observation s t,load32 t.core.memory (0x12720#32),decide (t.pc=0x2a6c9))
def answer (v : PlayerDamage.State) (d : Int32) (baby : Bool) (i : UInt8) :=
  (ActorHealth.answer v d baby,
    if survives v d baby then nextIndex i else BitVec.ofNat 32 i.toNat,
    survives v d baby && decide (randomAt (i+1)<255))
def joinedWrites (s : X86Memory.State) := ActorHealth.joinedWrites s ++ suffixWrites s

def afterWrites (s : X86Memory.State) := ActorHealth.afterWrites s ++ suffixWrites s

/-- Initial-state contracts compose through the real damage prefix and RNG
CALL/RET, without any reset or new assumption about the intermediate state. -/
theorem joined_execution_detailed (s : X86Memory.State) (f : Option Flags) (pc : Nat)
    (site : pc ∈ PlayerDamageEntry.sites) (v : PlayerDamage.State) (d : Int32) (baby : Bool)
    (i : UInt8) (h : JoinedInputs s v d baby i) :
    ∃ t, X86Routine.run joined exits 121 ⟨s,f,pc⟩ = some t ∧
      observation s t = answer v d baby i ∧ t.core.regs 4 = s.regs 4-(28#32) ∧
      t.core.regs 6 = s.regs 0 ∧ PlayerHeight.Frame s.memory t.core.memory (joinedWrites s) ∧
      PlayerHeight.Frame (PlayerDamageEntry.saved s pc) t.core.memory (afterWrites s) := by
  obtain ⟨g,grun,gobs,gsp,gobj,gframe,gsaved⟩ := ActorHealth.joined_execution_detailed s f pc site v d baby h.toActor
  obtain ⟨n,hn,path,gexit⟩ := X86Routine.run_path grun
  have path := path.transfer joined exits contains_actor actor_active
  have keep (a : Word) (ha : a ∈ prefixReads s i) : load32 g.core.memory a = load32 s.memory a :=
    gframe a (h.prefixSafe a ha)
  have index := (keep (0x12720#32) (by simp [prefixReads])).trans h.index
  have shape : (g.pc = 0x2a6b6) ↔ survives v d baby = true := by
    have obs := congrArg Prod.snd gobs
    simp only [ActorHealth.observation,ActorHealth.answer] at obs
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at gexit
    rcases gexit with gp | gp | gp <;> rw [gp] at obs ⊢ <;>
      cases accept : PlayerDamageEntry.accepted v d baby <;>
      simp [accept] at obs <;> simp_all [survives]
  by_cases gp : g.pc=0x2a6b6
  · have survived := shape.mp gp
    have inf : info g.core = inputInfo s := by
      rw [info,gobj,keep _ (by simp [prefixReads])]; rfl
    have slots : writes g.core = suffixWrites s := by simp [writes,suffixWrites,gsp,BitVec.sub_sub]
    have ins : Inputs g.core i := by
      refine ⟨index,?_,?_,?_,?_,?_⟩
      · exact (gframe.byte _ (h.prefixSafe _ (by simp [prefixReads]))).trans h.table
      · rw [inf,keep _ (by simp [prefixReads]),h.chance]
      · rw [gobj]
        have flags := frame_high_byte gframe (s.regs 0+(104#32)) (h.prefixSafe _ (by simp [prefixReads]))
        have flags : g.core.memory (s.regs 0+(107#32)) = s.memory (s.regs 0+(107#32)) := by
          simpa [BitVec.add_assoc] using flags
        rw [flags,h.noSkull]
        rfl
      · simpa [gsp,BitVec.sub_sub] using h.indexSafe
      · intro a ha
        have mem : a ∈ suffixReads s i := by
          simp only [reads,inf,gobj] at ha
          exact List.mem_append_left _ (List.mem_append_left _ ha)
        constructor
        · simpa [gsp,BitVec.sub_sub] using h.suffixSafe a mem (s.regs 4-(32#32)) (by simp [suffixWrites])
        · exact h.suffixSafe a mem (0x12720#32) (by simp [suffixWrites])
    let t := decisionEnd (rolled g.core i)
    have trun := original_execution g.core g.flags i ins
    rw [← gp] at trun
    obtain ⟨k,hk,tail,done⟩ := X86Routine.run_path trun
    have tail := tail.transfer joined exits contains_pain pain_active
    have done' : t.pc ∈ exits := by
      simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at done
      change t.pc = 0x2a6c9 ∨ t.pc = 0x2a6df at done
      simp only [exits,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false]
      omega
    have result : X86Routine.run joined exits 13 g = some t :=
      tail.finish (fuel := 0) (by change X86Routine.run joined exits 0 t = some t; simp [X86Routine.run,done']) 13 (by omega)
    have tc : t.core = rolled g.core i := result_core _ _
    have tm : t.core.memory = resultMemory g.core i := congrArg X86Memory.State.memory tc
    have regs : t.core.regs = write (write g.core.regs 2 (info g.core)) 0 ((randomByte i).zeroExtend 32) :=
      (congrArg X86Memory.State.regs tc).trans (rolled_regs _ _)
    have tpc : t.pc = if randomAt (i+1)<255 then 0x2a6c9 else 0x2a6df := result_pc _ _ ins
    have npc : t.pc ≠ 0x2a747 := by rw [tpc]; split <;> decide
    have nd : t.pc ≠ 0x2a6a6 := by rw [tpc]; split <;> decide
    have preserve (a : Word) (ha : a ∈ ActorHealth.fields s ++ [s.regs 0+(108#32)]) :
        load32 t.core.memory a = load32 g.core.memory a := by
      rw [tm]
      exact memory_frame g.core i a (by
        intro b hb; rw [slots] at hb
        exact h.suffixSafe a (by simp [suffixReads,ha]) b hb)
    have old : ActorHealth.observation s t = ActorHealth.observation s g := by
      simp only [ActorHealth.observation,PlayerHealth.observation,npc,gp,nd,
        show (0x2a6b6:Nat) ≠ 0x2a747 by decide,
        show (0x2a6b6:Nat) ≠ 0x2a6a6 by decide,if_false,decide_false]
      rw [preserve (s.regs 0+(108#32)) (by simp)]
      simp only [regs,write]
      simp
      exact ⟨preserve _ (by simp [ActorHealth.fields]),preserve _ (by simp [ActorHealth.fields]),
        preserve _ (by simp [ActorHealth.fields]),preserve _ (by simp [ActorHealth.fields]),
        preserve _ (by simp [ActorHealth.fields])⟩
    refine ⟨t,path.finish result 121 (by omega),?_,?_,?_,?_,?_⟩
    · have ri : load32 t.core.memory (0x12720#32) = nextIndex i := by
        rw [tm,resultMemory,randomMemory,load_store]
      simp [observation,old,gobs,ri,answer,survived,tpc]
    · simpa [regs,write] using gsp
    · simpa [regs,write] using gobj
    · intro a safe
      rw [tm,memory_frame g.core i a]
      · exact gframe a (fun b hb => safe b (by simp [joinedWrites,hb]))
      · intro b hb; rw [slots] at hb; exact safe b (by simp [joinedWrites,hb])
    · intro a safe
      rw [tm,memory_frame g.core i a]
      · exact gsaved a (fun b hb => safe b (by simp [afterWrites,hb]))
      · intro b hb; rw [slots] at hb; exact safe b (by simp [afterWrites,hb])
  · have notSurvived : survives v d baby = false := by simpa using (mt shape.mpr gp)
    have done : g.pc ∈ exits := by
      simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at gexit
      rcases gexit with h | h | h
      · simp [exits,h]
      · contradiction
      · simp [exits,h]
    have noPain : g.pc ≠ 0x2a6c9 := by
      simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at gexit
      omega
    refine ⟨g,path.finish (fuel := 0) (by simp [X86Routine.run,done]) 121 (by omega),?_,gsp,gobj,?_,?_⟩
    · simp [observation,answer,gobs,index,notSurvived,noPain]
    · intro a safe
      exact gframe a (fun b hb => safe b (by simp [joinedWrites,hb]))
    · intro a safe
      exact gsaved a (fun b hb => safe b (by simp [afterWrites,hb]))

theorem joined_execution (s : X86Memory.State) (f : Option Flags) (pc : Nat)
    (site : pc ∈ PlayerDamageEntry.sites) (v : PlayerDamage.State) (d : Int32) (baby : Bool)
    (i : UInt8) (h : JoinedInputs s v d baby i) :
    ∃ t, X86Routine.run joined exits 121 ⟨s,f,pc⟩ = some t ∧
      observation s t = answer v d baby i ∧ t.core.regs 4 = s.regs 4-(28#32) ∧
      t.core.regs 6 = s.regs 0 ∧ PlayerHeight.Frame s.memory t.core.memory (joinedWrites s) := by
  obtain ⟨t,run,obs,sp,obj,frame,_⟩ := joined_execution_detailed s f pc site v d baby i h
  exact ⟨t,run,obs,sp,obj,frame⟩

def liveObservation (v : PlayerDamage.State) (out : PlayerDamage.Result) :=
  (ActorHealth.liveObservation v out,BitVec.ofNat 32 out.rng.play.toNat,out.pain)

theorem finish_pain (v : PlayerDamage.State) (d : Int32) (rng : DoomRandom)
    (skull : v.skullFly = false) :
    let out := PlayerDamage.finish v d rng
    (BitVec.ofNat 32 out.rng.play.toNat,out.pain) =
      if v.health-(PlayerDamage.absorbArmor v d).2 ≤ 0 then (BitVec.ofNat 32 rng.play.toNat,false)
      else (nextIndex rng.play,decide (randomAt (rng.play+1)<255)) := by
  have hp : (PlayerDamage.absorbArmor v d).1.health = v.health := by
    unfold PlayerDamage.absorbArmor; split <;> rfl
  have sk : (PlayerDamage.absorbArmor v d).1.skullFly = false := by
    unfold PlayerDamage.absorbArmor; split <;> exact skull
  unfold PlayerDamage.finish
  simp only [Id.run,pure,bind,PlayerDamage.bookkeep,hp,sk]
  split <;> simp_all [DoomRandom.nextPlay,nextIndex]

theorem live_answer (v : PlayerDamage.State) (d : Int32) (baby : Bool) (rng : DoomRandom)
    (skull : v.skullFly = false) (ordinary : v.sectorSpecial ≠ 11) :
    liveObservation v (PlayerDamage.apply v d none false baby rng) = answer v d baby rng.play := by
  unfold liveObservation answer
  rw [ActorHealth.live_answer v d baby rng skull ordinary]
  apply congrArg (fun pair => (ActorHealth.answer v d baby,pair))
  rw [PlayerDamageEntry.live_entry v d baby false rng skull ordinary]
  cases accept : PlayerDamageEntry.accepted v d baby
  · simp [accept,survives]
  · simp only [accept,if_true,finish_pain v _ rng skull]
    unfold survives
    rw [accept]
    split <;> simp_all

/-- Original floor CALL through pain choice, related to the actual engine
routine. State entry/actions, death actions and handler epilogue remain exits. -/
theorem live_correspondence (s : X86Memory.State) (f : Option Flags) (pc : Nat)
    (site : pc ∈ PlayerDamageEntry.sites) (v : PlayerDamage.State) (d : Int32)
    (baby : Bool) (rng : DoomRandom) (h : JoinedInputs s v d baby rng.play) :
    (X86Routine.run joined exits 121 ⟨s,f,pc⟩).map (observation s) =
      some (liveObservation v (PlayerDamage.apply v d none false baby rng)) := by
  obtain ⟨t,run,obs,_⟩ := joined_execution s f pc site v d baby rng.play h
  rw [live_answer v d baby rng h.liveSkull h.liveOrdinary]
  simp [run,obs]

end Doom.Proofs.PlayerPain
