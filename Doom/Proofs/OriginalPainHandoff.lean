import Doom.Proofs.OriginalPlayerPain
import Doom.PlayerAnim

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.PainHandoff
open Verification X86 X86Memory X86Control BlockSummary

def code : List UInt8 := [0x8a,0x4e,0x68,0x80,0xc9,0x40,0x8b,0x56,0x5c,0x88,0x4e,0x68,0x89,0xf0,0x8b,0x52,0x1c,0xe8,0xc1,0x67,0x0,0x0]
def bytesProgram (bytes : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2a6c9 ≤ pc ∧ pc < 0x2a6df then X86Routine.decodeAt bytes (pc-0x2a6c9) else none
def program := bytesProgram code

def listed : X86Routine.Program
  | 0x2a6c9 => some (.control (.loadByte 1 ⟨some 6,none,0,104⟩),3)
  | 0x2a6cc => some (.orByteImmediate 1 64,3)
  | 0x2a6cf => some (.control (.block (.legacy (.load 2 6 92))),3)
  | 0x2a6d2 => some (.storeByte ⟨some 6,none,0,104⟩ 1,3)
  | 0x2a6d5 => some (.control (.block (.legacy (.mov 0 6))),2)
  | 0x2a6d7 => some (.control (.block (.legacy (.load 2 2 28))),3)
  | 0x2a6da => some (.call 26561,5)
  | _ => none

theorem decoded (pc : Nat) (h : listed pc ≠ none) : program pc = listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def byteStore (m : Memory) (a : Word) (v : BitVec 8) : Memory := fun b => if b=a then v else m b

theorem byteStore_word_apart (m : Memory) (a b : Word) (v : BitVec 8) (h : Apart b a) :
    load32 (byteStore m a v) b = load32 m b := by
  have h0 : b ≠ a := by
    have hi := h 0 0
    change b+(0#32) ≠ a+(0#32) at hi
    simpa only [BitVec.add_zero] using hi
  have h1 : b+(1#32) ≠ a := by
    have hi := h 1 0
    change b+(1#32) ≠ a+(0#32) at hi
    simpa only [BitVec.add_zero] using hi
  have h2 : b+(2#32) ≠ a := by
    have hi := h 2 0
    change b+(2#32) ≠ a+(0#32) at hi
    simpa only [BitVec.add_zero] using hi
  have h3 : b+(3#32) ≠ a := by
    have hi := h 3 0
    change b+(3#32) ≠ a+(0#32) at hi
    simpa only [BitVec.add_zero] using hi
  simp [load32,byteStore,h0,h1,h2,h3]

/-- Setting the low-byte hit flag preserves every other flag bit. -/
theorem flag_word (m : Memory) (a : Word) :
    load32 (byteStore m a (m a ||| (64#8))) a = load32 m a ||| (64#32) := by
  have h1 : a+(1#32) ≠ a := by
    have ne : a+(1#32) ≠ a+(0#32) := fun eq => (by decide : (1#32) ≠ (0#32)) ((BitVec.add_right_inj a).mp eq)
    simpa only [BitVec.add_zero] using ne
  have h2 : a+(2#32) ≠ a := by
    have ne : a+(2#32) ≠ a+(0#32) := fun eq => (by decide : (2#32) ≠ (0#32)) ((BitVec.add_right_inj a).mp eq)
    simpa only [BitVec.add_zero] using ne
  have h3 : a+(3#32) ≠ a := by
    have ne : a+(3#32) ≠ a+(0#32) := fun eq => (by decide : (3#32) ≠ (0#32)) ((BitVec.add_right_inj a).mp eq)
    simpa only [BitVec.add_zero] using ne
  simp only [load32,byteStore,show (1:Word)=(1#32) from rfl,
    show (2:Word)=(2#32) from rfl,show (3:Word)=(3#32) from rfl,ite_true,if_neg h1,if_neg h2,if_neg h3]
  have fact (a b c d : BitVec 8) :
      ((a ++ b) ++ (c ++ (d ||| (64#8)))) = (((a ++ b) ++ (c ++ d)) ||| (64#32)) := by
    rw [show (64#32) = ((0#8 ++ 0#8) ++ (0#8 ++ 64#8)) from by decide]
    rw [@BitVec.or_append 16 16 (a ++ b) (0#8 ++ 0#8) (c ++ d) (0#8 ++ 64#8),
      @BitVec.or_append 8 8 a (0#8) b (0#8), @BitVec.or_append 8 8 c (0#8) d (64#8)]
    simp only [BitVec.or_zero]
  exact fact (m (a+(3#32))) (m (a+(2#32))) (m (a+(1#32))) (m a)

def flagsByte (s : X86Memory.State) := s.memory (s.regs 6+(104#32)) ||| (64#8)
def flagged (s : X86Memory.State) := byteStore s.memory (s.regs 6+(104#32)) (flagsByte s)
def info (s : X86Memory.State) := load32 s.memory (s.regs 6+(92#32))
def stateNumber (s : X86Memory.State) := load32 (flagged s) (info s+(28#32))
def resultMemory (s : X86Memory.State) := store32 (flagged s) (s.regs 4-(4#32)) (0x2a6df#32)
def result (s : X86Memory.State) : X86Control.State :=
  ⟨⟨write (write (write (putByte s 1 (flagsByte s)).regs 0 (s.regs 6)) 2 (stateNumber s)) 4 (s.regs 4-(4#32)),
    resultMemory s⟩,some (logical8 (flagsByte s)),0x30ea0⟩

theorem cl_written (s : X86Memory.State) (v : BitVec 8) : readByte (putByte s 1 v).regs 1 = v := by
  simp [readByte,putByte,put,write,byteReg,write_low_read]

theorem byte_high_zero (v : BitVec 8) : v.zeroExtend 32 &&& (0xffffff00#32) = 0 := by
  have shape : v.zeroExtend 32 = (0#24 ++ v) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_append (x := (0#24)) (y := v)]
    simp [Nat.mod_eq_of_lt (by have := v.isLt; omega : v.toNat < 2^32)]
  rw [shape,show (0xffffff00#32) = (0xffffff#24 ++ 0#8) from by decide]
  rw [@BitVec.and_append 24 8 (0#24) (0xffffff#24) v (0#8)]
  simp only [BitVec.zero_and,BitVec.and_zero,BitVec.zero_append_zero]
  rfl

/-- The original flag byte store and real CALL. Metadata is read after the
flag store, so even aliasing is represented by the isolated instruction proof. -/
theorem execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run listed [0x30ea0] 7 ⟨s,f,0x2a6c9⟩ = some (result s) := by
  let a := s.memory (s.regs 6+(104#32))
  let c1 := putByte s 1 a
  let c2 := putByte c1 1 (flagsByte s)
  let c3 := put c2 2 (info s)
  let c4 : X86Memory.State := {c3 with memory := flagged s}
  let c5 := put c4 0 (s.regs 6)
  let c6 := put c5 2 (stateNumber s)
  have path : X86Routine.Prefix listed [0x30ea0] 7 ⟨s,f,0x2a6c9⟩
      ⟨X86Routine.pushWord c6 (0x2a6df#32),some (logical8 (flagsByte s)),0x30ea0⟩ := by
    apply X86Routine.Prefix.step (middle := ⟨c1,f,0x2a6cc⟩) (by simp) (show listed 0x2a6c9 = _ from rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.Address.eval,c1,a])
    apply X86Routine.Prefix.step (middle := ⟨c2,some (logical8 (flagsByte s)),0x2a6cf⟩) (by simp) (show listed 0x2a6cc = _ from rfl) (by
      simp [X86Routine.execute,c2,c1,cl_written,flagsByte,a])
    apply X86Routine.Prefix.step (middle := ⟨c3,some (logical8 (flagsByte s)),0x2a6d2⟩) (by simp) (show listed 0x2a6cf = _ from rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,blockPreservesFlags,
        c3,c2,c1,putByte,byteReg,put,write,info])
    apply X86Routine.Prefix.step (middle := ⟨c4,some (logical8 (flagsByte s)),0x2a6d5⟩) (by simp) (show listed 0x2a6d2 = _ from rfl) (by
      have cl : readByte c3.regs 1 = flagsByte s := by
        simpa [c3,readByte,byteReg,put,write] using cl_written c1 (flagsByte s)
      simp only [X86Routine.execute,cl]
      simp [X86Block.Address.eval,c4,flagged,byteStore,c3,c2,c1,putByte,byteReg,put,write]
      rfl)
    apply X86Routine.Prefix.step (middle := ⟨c5,some (logical8 (flagsByte s)),0x2a6d7⟩) (by simp) (show listed 0x2a6d5 = _ from rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,blockPreservesFlags,
        c5,c4,c3,c2,c1,putByte,byteReg,put,write])
    apply X86Routine.Prefix.step (middle := ⟨c6,some (logical8 (flagsByte s)),0x2a6da⟩) (by simp) (show listed 0x2a6d7 = _ from rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,blockPreservesFlags,
        c6,c5,c4,c3,c2,c1,putByte,byteReg,put,write,stateNumber])
    apply X86Routine.Prefix.step (middle := ⟨X86Routine.pushWord c6 (0x2a6df#32),some (logical8 (flagsByte s)),0x30ea0⟩)
      (by simp) (show listed 0x2a6da = _ from rfl) (by simp [X86Routine.execute])
    exact X86Routine.Prefix.nil _
  have tail : X86Routine.run listed [0x30ea0] 0
      ⟨X86Routine.pushWord c6 (0x2a6df#32),some (logical8 (flagsByte s)),0x30ea0⟩ =
      some ⟨X86Routine.pushWord c6 (0x2a6df#32),some (logical8 (flagsByte s)),0x30ea0⟩ := rfl
  rw [path.finish tail 7 (by decide)]
  congr 2
  simp [result,resultMemory,c6,c5,c4,c3,c2,c1,X86Routine.pushWord,putByte,byteReg,put,write]
  funext r
  by_cases h0 : r=0 <;> by_cases h1 : r=1 <;> by_cases h2 : r=2 <;> by_cases h4 : r=4 <;>
    simp_all [write,BitVec.and_or_distrib_right,BitVec.and_assoc,BitVec.or_assoc,byte_high_zero]

theorem original_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x30ea0] 7 ⟨s,f,0x2a6c9⟩ = some (result s) := by
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [execution]; simp)]
  exact execution s f

def writes (s : X86Memory.State) := [s.regs 6+(104#32),s.regs 4-(4#32)]
theorem memory_frame (s : X86Memory.State) : PlayerHeight.Frame s.memory (resultMemory s) (writes s) := by
  intro a safe
  rw [resultMemory,load_store_apart _ _ _ _ (safe _ (by simp [writes]))]
  exact byteStore_word_apart _ _ _ _ (safe _ (by simp [writes]))

def exits : List Nat := [0x2a6a6,0x30ea0,0x2a6df,0x2a747]
def joined (pc : Nat) : Option (X86Routine.Op × Nat) :=
  if 0x2a6c9 ≤ pc ∧ pc < 0x2a6df then program pc else PlayerPain.joined pc

theorem contains_pain (pc : Nat) (h : PlayerPain.joined pc ≠ none) : joined pc = PlayerPain.joined pc := by
  unfold joined
  split
  next bounds =>
    have b1 : ¬(0x2a650 ≤ pc ∧ pc < 0x2a6a6) := by omega
    have b2 : ¬(0x1bb50 ≤ pc ∧ pc < 0x1bb66) := by omega
    have b3 : ¬(0x1bc41 ≤ pc ∧ pc < 0x1bc45) := by omega
    have b4 : ¬(0x2a616 ≤ pc ∧ pc < 0x2a650) := by omega
    have b5 : ¬(0x2a460 ≤ pc ∧ pc < 0x2a5d5) := by omega
    have b6 : ¬(0x2a5d5 ≤ pc ∧ pc < 0x2a616) := by omega
    have b7 : ¬(0x2a6b6 ≤ pc ∧ pc < 0x2a6c9) := by omega
    have b8 : ¬(0x24160 ≤ pc ∧ pc < 0x2417c) := by omega
    simp [PlayerPain.joined,ActorHealth.joined,PlayerHealth.joined,PlayerDamageEntry.program,PlayerDamageEntry.bytesProgram,
      b1,b2,b3,b4,b5,b6,b7,b8,show pc ≠ 0x2fb76 by omega,show pc ≠ 0x2fba0 by omega,show pc ≠ 0x2fbd2 by omega] at h
  next => rfl

theorem pain_active (pc : Nat) (h : PlayerPain.joined pc ≠ none) : pc ∉ exits := by
  intro hm
  simp only [exits,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl <;> contradiction

theorem contains_handoff (pc : Nat) (h : program pc ≠ none) : joined pc = program pc := by
  unfold joined
  split
  next => rfl
  next hn => simp [program,bytesProgram,hn] at h

theorem handoff_active (pc : Nat) (h : program pc ≠ none) : pc ∉ exits := by
  intro hm
  simp only [exits,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl <;> contradiction

def prefixReads (s : X86Memory.State) : List Word :=
  [s.regs 0+(104#32),s.regs 0+(92#32),PlayerPain.inputInfo s+(28#32)]
def suffixWrites (s : X86Memory.State) : List Word := [s.regs 0+(104#32),s.regs 4-(32#32)]
def retained (s : X86Memory.State) : List Word := ActorHealth.fields s ++ [s.regs 0+(108#32),(0x12720#32)]
structure JoinedInputs (s : X86Memory.State) (v : PlayerDamage.State) (d : Int32) (baby : Bool) (i : UInt8)
    extends toPain : PlayerPain.JoinedInputs s v d baby i where
  painState : load32 s.memory (PlayerPain.inputInfo s+(28#32)) = (156#32)
  handoffReadsSafe : ∀ a, a ∈ prefixReads s → ∀ b, b ∈ PlayerPain.joinedWrites s → Apart a b
  stateSafe : Apart (PlayerPain.inputInfo s+(28#32)) (s.regs 0+(104#32))
  flagSafe : Apart (s.regs 0+(104#32)) (s.regs 4-(32#32))
  retainedSafe : ∀ a, a ∈ retained s → ∀ b, b ∈ suffixWrites s → Apart a b

def observation (s : X86Memory.State) (t : X86Control.State) :=
  ((ActorHealth.observation s t,load32 t.core.memory (0x12720#32),decide (t.pc=0x30ea0)),
    load32 t.core.memory (s.regs 0+(104#32)),
    if t.pc=0x30ea0 then some (t.core.regs 0,t.core.regs 2,load32 t.core.memory (t.core.regs 4)) else none)
def answer (s : X86Memory.State) (v : PlayerDamage.State) (d : Int32) (baby : Bool) (i : UInt8) :=
  let pain := (PlayerPain.answer v d baby i).2.2
  (PlayerPain.answer v d baby i,
    load32 s.memory (s.regs 0+(104#32)) ||| (if pain then (64#32) else (0#32)),
    if pain then some (s.regs 0,(156#32),(0x2a6df#32)) else none)
def joinedWrites (s : X86Memory.State) := PlayerPain.joinedWrites s ++ suffixWrites s

def afterWrites (s : X86Memory.State) := PlayerPain.afterWrites s ++ suffixWrites s

/-- Continuous original damage execution to P_SetMobjState entry. The call
arguments, saved return address and entire flags word are observed. -/
theorem joined_execution_detailed (s : X86Memory.State) (f : Option Flags) (pc : Nat)
    (site : pc ∈ PlayerDamageEntry.sites) (v : PlayerDamage.State) (d : Int32) (baby : Bool)
    (i : UInt8) (h : JoinedInputs s v d baby i) :
    ∃ t, X86Routine.run joined exits 128 ⟨s,f,pc⟩ = some t ∧
      observation s t = answer s v d baby i ∧
      t.core.regs 4 = s.regs 4-(if t.pc=0x30ea0 then (32#32) else (28#32)) ∧
      t.core.regs 6 = s.regs 0 ∧ PlayerHeight.Frame s.memory t.core.memory (joinedWrites s) ∧
      PlayerHeight.Frame (PlayerDamageEntry.saved s pc) t.core.memory (afterWrites s) := by
  obtain ⟨g,grun,gobs,gsp,gobj,gframe,gsaved⟩ := PlayerPain.joined_execution_detailed s f pc site v d baby i h.toPain
  obtain ⟨n,hn,path,gexit⟩ := X86Routine.run_path grun
  have path := path.transfer joined exits contains_pain pain_active
  have keep (a : Word) (ha : a ∈ prefixReads s) : load32 g.core.memory a = load32 s.memory a :=
    gframe a (h.handoffReadsSafe a ha)
  have flags := keep (s.regs 0+(104#32)) (by simp [prefixReads])
  have choice : decide (g.pc=0x2a6c9) = (PlayerPain.answer v d baby i).2.2 := congrArg (fun x => x.2.2) gobs
  by_cases gp : g.pc=0x2a6c9
  · have selected : (PlayerPain.answer v d baby i).2.2 = true := by simpa [gp] using choice.symm
    have inf : info g.core = PlayerPain.inputInfo s := by
      rw [info,gobj,keep _ (by simp [prefixReads])]; rfl
    have state : stateNumber g.core = (156#32) := by
      rw [stateNumber,flagged,byteStore_word_apart]
      · rw [inf,keep _ (by simp [prefixReads]),h.painState]
      · rw [inf,gobj]; exact h.stateSafe
    have slots : writes g.core = suffixWrites s := by simp [writes,suffixWrites,gsp,gobj,BitVec.sub_sub]
    have trun := original_execution g.core g.flags
    rw [← gp] at trun
    obtain ⟨k,hk,tail,_⟩ := X86Routine.run_path trun
    have tail := tail.transfer joined exits contains_handoff handoff_active
    have done : (result g.core).pc ∈ exits := by simp [result,exits]
    have finalRun : X86Routine.run joined exits 7 g = some (result g.core) :=
      tail.finish (fuel := 0) (by simp [X86Routine.run,done]) 7 (by omega)
    have preserve (a : Word) (ha : a ∈ retained s) :
        load32 (resultMemory g.core) a = load32 g.core.memory a := by
      apply memory_frame
      intro b hb; rw [slots] at hb; exact h.retainedSafe a ha b hb
    have old : ActorHealth.observation s (result g.core) = ActorHealth.observation s g := by
      simp only [ActorHealth.observation,PlayerHealth.observation,result,gp]
      simp [putByte,byteReg,put,write]
      exact ⟨⟨preserve _ (by simp [retained,ActorHealth.fields]),preserve _ (by simp [retained,ActorHealth.fields]),
        preserve _ (by simp [retained,ActorHealth.fields]),preserve _ (by simp [retained,ActorHealth.fields]),
        preserve _ (by simp [retained,ActorHealth.fields])⟩,preserve _ (by simp [retained])⟩
    have flagResult : load32 (resultMemory g.core) (s.regs 0+(104#32)) =
        load32 s.memory (s.regs 0+(104#32)) ||| (64#32) := by
      rw [resultMemory,load_store_apart]
      · rw [← gobj]
        change load32 (byteStore g.core.memory _ _) _ = _
        unfold flagsByte
        rw [flag_word,gobj,flags]
      · simpa [gsp,BitVec.sub_sub] using h.flagSafe
    refine ⟨result g.core,path.finish finalRun 128 (by omega),?_,?_,?_,?_,?_⟩
    · have previous : (ActorHealth.observation s g,load32 g.core.memory (0x12720#32),true) = PlayerPain.answer v d baby i := by
        simpa [PlayerPain.observation,gp] using gobs
      have ret : load32 (resultMemory g.core) (g.core.regs 4-(4#32)) = (0x2a6df#32) := by
        rw [resultMemory,load_store]
      simp only [observation,old,answer,selected,if_true]
      simp only [result,putByte,byteReg,put,write]
      simp only [↓reduceIte,decide_true]
      rw [preserve (0x12720#32) (by simp [retained]),previous,flagResult,ret,state,gobj]
      simp
    · simp [result,putByte,byteReg,put,write,gsp,BitVec.sub_sub]
    · simp [result,putByte,byteReg,put,write,gobj]
    · intro a safe
      rw [show (result g.core).core.memory = resultMemory g.core from rfl,memory_frame g.core a]
      · exact gframe a (fun b hb => safe b (by simp [joinedWrites,hb]))
      · intro b hb; rw [slots] at hb; exact safe b (by simp [joinedWrites,hb])
    · intro a safe
      rw [show (result g.core).core.memory = resultMemory g.core from rfl,memory_frame g.core a]
      · exact gsaved a (fun b hb => safe b (by simp [afterWrites,hb]))
      · intro b hb; rw [slots] at hb; exact safe b (by simp [afterWrites,hb])
  · have selected : (PlayerPain.answer v d baby i).2.2 = false := by simpa [gp] using choice.symm
    have done : g.pc ∈ exits := by
      simp only [PlayerPain.exits,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at gexit
      simp only [exits,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false]
      omega
    have noCall : g.pc ≠ 0x30ea0 := by
      simp only [PlayerPain.exits,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at gexit
      omega
    refine ⟨g,path.finish (fuel := 0) (by simp [X86Routine.run,done]) 128 (by omega),?_,?_,gobj,?_,?_⟩
    · have previous : (ActorHealth.observation s g,load32 g.core.memory (0x12720#32),false) = PlayerPain.answer v d baby i := by
        simpa [PlayerPain.observation,gp] using gobs
      simp [observation,answer,selected,noCall,flags,previous]
    · simpa [noCall] using gsp
    · intro a safe; exact gframe a (fun b hb => safe b (by simp [joinedWrites,hb]))
    · intro a safe
      exact gsaved a (fun b hb => safe b (by simp [afterWrites,hb]))

theorem joined_execution (s : X86Memory.State) (f : Option Flags) (pc : Nat)
    (site : pc ∈ PlayerDamageEntry.sites) (v : PlayerDamage.State) (d : Int32) (baby : Bool)
    (i : UInt8) (h : JoinedInputs s v d baby i) :
    ∃ t, X86Routine.run joined exits 128 ⟨s,f,pc⟩ = some t ∧
      observation s t = answer s v d baby i ∧
      t.core.regs 4 = s.regs 4-(if t.pc=0x30ea0 then (32#32) else (28#32)) ∧
      t.core.regs 6 = s.regs 0 ∧ PlayerHeight.Frame s.memory t.core.memory (joinedWrites s) := by
  obtain ⟨t,run,obs,sp,obj,frame,_⟩ := joined_execution_detailed s f pc site v d baby i h
  exact ⟨t,run,obs,sp,obj,frame⟩

def liveObservation (s : X86Memory.State) (v : PlayerDamage.State) (out : PlayerDamage.Result) :=
  (PlayerPain.liveObservation v out,
    load32 s.memory (s.regs 0+(104#32)) ||| (if out.pain then (64#32) else (0#32)),
    if out.pain then some (s.regs 0,(156#32),(0x2a6df#32)) else none)

theorem live_answer (s : X86Memory.State) (v : PlayerDamage.State) (d : Int32) (baby : Bool) (rng : DoomRandom)
    (skull : v.skullFly=false) (ordinary : v.sectorSpecial ≠ 11) :
    liveObservation s v (PlayerDamage.apply v d none false baby rng) = answer s v d baby rng.play := by
  have eq := PlayerPain.live_answer v d baby rng skull ordinary
  have pain := congrArg (fun x => x.2.2) eq
  unfold liveObservation answer
  rw [eq,show (PlayerDamage.apply v d none false baby rng).pain = (PlayerPain.answer v d baby rng.play).2.2 from pain]

theorem live_correspondence (s : X86Memory.State) (f : Option Flags) (pc : Nat)
    (site : pc ∈ PlayerDamageEntry.sites) (v : PlayerDamage.State) (d : Int32)
    (baby : Bool) (rng : DoomRandom) (h : JoinedInputs s v d baby rng.play) :
    (X86Routine.run joined exits 128 ⟨s,f,pc⟩).map (observation s) =
      some (liveObservation s v (PlayerDamage.apply v d none false baby rng)) := by
  obtain ⟨t,run,obs,_⟩ := joined_execution s f pc site v d baby rng.play h
  rw [live_answer s v d baby rng h.liveSkull h.liveOrdinary]
  simp [run,obs]

/-- The requested player state is the existing engine's first pain frame;
it lasts four tics and does not request the later pain sound on entry. -/
theorem requested_animation : PlayerAnim.enter 156 = (⟨156,4⟩,false) := rfl

end Doom.Proofs.PainHandoff
