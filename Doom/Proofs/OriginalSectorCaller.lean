import Doom.Proofs.OriginalSectorEntry
import Doom.Proofs.OriginalSectorDispatch

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.SectorCaller
open Verification X86 X86Memory X86Control BlockSummary

/-- Original P_PlayerThink sector lookup and CALL, with absolute code-object PCs. -/
def callBytes : List UInt8 := SectorDispatch.code
def bytesProgram (caller entry secret epilogue : List UInt8) : X86Routine.Program := fun pc =>
  if 0x333d0 ≤ pc ∧ pc < 0x333e5 then X86Routine.decodeAt caller (pc-0x333d0)
  else SectorEntry.bytesProgram entry secret epilogue pc

def program := bytesProgram callBytes SectorEntry.entryBytes SectorSecret.code SectorEntry.returnBytes

def slots (s : X86Memory.State) : List Word :=
  [s.regs 4-(4#32),s.regs 4-(8#32),s.regs 4-(12#32),s.regs 4-(16#32),s.regs 4-(20#32)]

def saved (s : X86Memory.State) : Memory :=
  store32 (store32 (store32 (store32 (store32 s.memory
    (s.regs 4-(4#32)) 0x333e5) (s.regs 4-(8#32)) (s.regs 3))
    (s.regs 4-(12#32)) (s.regs 1)) (s.regs 4-(16#32)) (s.regs 2))
    (s.regs 4-(20#32)) (s.regs 6)

def enter (s : X86Memory.State) : X86Memory.State :=
  ⟨write s.regs 4 (s.regs 4-(20#32)),saved s⟩

def reads (s : X86Memory.State) : List Word :=
  [SectorEntry.player s,SectorEntry.object s+(52#32),SectorEntry.subsector s,
   SectorEntry.object s+(20#32),SectorEntry.sector s,SectorEntry.sector s+(14#32),
   SectorEntry.player s+(212#32)]

/-- All hypotheses describe memory before the actual CALL. No saved words or
return address are supplied: the instructions must create them. -/
structure Inputs (s : X86Memory.State) (z floor : Fixed) (n : Int32) : Prop where
  isSecret : SectorEntry.special s = 9
  height : SectorEntry.zWord s = z.raw.toBitVec
  floor : SectorEntry.floorWord s = floor.raw.toBitVec
  count : load32 s.memory (SectorEntry.player s+(212#32)) = n.toBitVec
  separate : SectorSecret.Separate (SectorEntry.afterSwitch s)
  stackApart : ∀ a, a ∈ reads s → ∀ b, b ∈ slots s → Apart a b

theorem saved_load (s : X86Memory.State) (a : Word)
    (safe : ∀ b, b ∈ slots s → Apart a b) : load32 (saved s) a = load32 s.memory a := by
  unfold saved
  repeat rw [load_store_apart _ _ _ _ (safe _ (by simp [slots]))]

/-- Adjacent stack slots cannot alias, including across address wraparound. -/
theorem saved_words (s : X86Memory.State) :
    (load32 (saved s) (s.regs 4-(4#32)),load32 (saved s) (s.regs 4-(8#32)),
     load32 (saved s) (s.regs 4-(12#32)),load32 (saved s) (s.regs 4-(16#32)),
     load32 (saved s) (s.regs 4-(20#32))) =
    ((0x333e5#32),s.regs 3,s.regs 1,s.regs 2,s.regs 6) := by
  have k12 : Apart (s.regs 4-(4#32)) (s.regs 4-(8#32)) := PlayerHeight.Function.slots_apart (s.regs 4) 1 2 (by decide)
  have k13 : Apart (s.regs 4-(4#32)) (s.regs 4-(12#32)) := PlayerHeight.Function.slots_apart (s.regs 4) 1 3 (by decide)
  have k14 : Apart (s.regs 4-(4#32)) (s.regs 4-(16#32)) := PlayerHeight.Function.slots_apart (s.regs 4) 1 4 (by decide)
  have k15 : Apart (s.regs 4-(4#32)) (s.regs 4-(20#32)) := PlayerHeight.Function.slots_apart (s.regs 4) 1 5 (by decide)
  have k23 : Apart (s.regs 4-(8#32)) (s.regs 4-(12#32)) := PlayerHeight.Function.slots_apart (s.regs 4) 2 3 (by decide)
  have k24 : Apart (s.regs 4-(8#32)) (s.regs 4-(16#32)) := PlayerHeight.Function.slots_apart (s.regs 4) 2 4 (by decide)
  have k25 : Apart (s.regs 4-(8#32)) (s.regs 4-(20#32)) := PlayerHeight.Function.slots_apart (s.regs 4) 2 5 (by decide)
  have k34 : Apart (s.regs 4-(12#32)) (s.regs 4-(16#32)) := PlayerHeight.Function.slots_apart (s.regs 4) 3 4 (by decide)
  have k35 : Apart (s.regs 4-(12#32)) (s.regs 4-(20#32)) := PlayerHeight.Function.slots_apart (s.regs 4) 3 5 (by decide)
  have k45 : Apart (s.regs 4-(16#32)) (s.regs 4-(20#32)) := PlayerHeight.Function.slots_apart (s.regs 4) 4 5 (by decide)
  simp only [saved,load_store,load_store_apart _ _ _ _ k12,load_store_apart _ _ _ _ k13,load_store_apart _ _ _ _ k14,load_store_apart _ _ _ _ k15,load_store_apart _ _ _ _ k23,load_store_apart _ _ _ _ k24,load_store_apart _ _ _ _ k25,load_store_apart _ _ _ _ k34,load_store_apart _ _ _ _ k35,load_store_apart _ _ _ _ k45]
  rfl

theorem return_address (s : X86Memory.State) : SectorSecret.returnPc (enter s) = 0x333e5 := by
  have h := congrArg Prod.fst (saved_words s)
  simpa [SectorSecret.returnPc,enter,write,BitVec.sub_eq_add_neg,BitVec.add_assoc] using congrArg BitVec.toNat h

theorem call_prefix (s : X86Memory.State) (flags : Option Flags) :
    X86CodeMemory.Prefix (SectorEntry.codeMemory SectorEntry.tableBytes) program [0x333e5] 5
      ⟨s,flags,0x333e0⟩ ⟨enter s,flags,0x2fb24⟩ := by
  let c := X86Routine.pushWord s (0x333e5#32)
  let p1 := X86Routine.pushWord c (s.regs 3)
  let p2 := X86Routine.pushWord p1 (s.regs 1)
  let p3 := X86Routine.pushWord p2 (s.regs 2)
  let p4 := X86Routine.pushWord p3 (s.regs 6)
  apply X86CodeMemory.Prefix.step (middle := ⟨c,flags,0x2fb20⟩) (by simp)
    (show program 0x333e0 = some (.call (-14533),5) from by decide) (by
      simp [X86CodeMemory.execute,X86Routine.execute,c])
  apply X86CodeMemory.Prefix.step (middle := ⟨p1,flags,0x2fb21⟩)
    (by simp) (show program 0x2fb20 = some (.push 3,1) from by decide) (by
      simp [X86CodeMemory.execute,X86Routine.execute,c,p1,p2,p3,p4,X86Routine.pushWord,put,write])
  apply X86CodeMemory.Prefix.step (middle := ⟨p2,flags,0x2fb22⟩)
    (by simp) (show program 0x2fb21 = some (.push 1,1) from by decide) (by
      simp [X86CodeMemory.execute,X86Routine.execute,c,p1,p2,p3,p4,X86Routine.pushWord,put,write])
  apply X86CodeMemory.Prefix.step (middle := ⟨p3,flags,0x2fb23⟩)
    (by simp) (show program 0x2fb22 = some (.push 2,1) from by decide) (by
      simp [X86CodeMemory.execute,X86Routine.execute,c,p1,p2,p3,p4,X86Routine.pushWord,put,write])
  apply X86CodeMemory.Prefix.step (middle := ⟨p4,flags,0x2fb24⟩)
    (by simp) (show program 0x2fb23 = some (.push 6,1) from by decide) (by
      simp [X86CodeMemory.execute,X86Routine.execute,c,p1,p2,p3,p4,X86Routine.pushWord,put,write])

  simpa [c,p1,p2,p3,p4,enter,saved,X86Routine.pushWord,put,write,BitVec.sub_sub,
    BitVec.sub_eq_add_neg,BitVec.add_assoc,PlayerHeight.Function.write_shadow] using
    (X86CodeMemory.Prefix.nil (cm := SectorEntry.codeMemory SectorEntry.tableBytes)
      (program := program) (exits := [0x333e5]) ⟨enter s,flags,0x2fb24⟩)

theorem lookup_preserved (s : X86Memory.State) (z floor : Fixed) (n : Int32) (h : Inputs s z floor n) :
    SectorEntry.player (enter s) = SectorEntry.player s ∧
    SectorEntry.object (enter s) = SectorEntry.object s ∧
    SectorEntry.subsector (enter s) = SectorEntry.subsector s ∧
    SectorEntry.sector (enter s) = SectorEntry.sector s ∧
    SectorEntry.zWord (enter s) = SectorEntry.zWord s ∧
    SectorEntry.floorWord (enter s) = SectorEntry.floorWord s ∧
    SectorEntry.special (enter s) = SectorEntry.special s := by
  have keep (a : Word) (ha : a ∈ reads s) := saved_load s a (h.stackApart a ha)
  have player : SectorEntry.player (enter s) = SectorEntry.player s := rfl
  have obj : SectorEntry.object (enter s) = SectorEntry.object s := by
    unfold SectorEntry.object; rw [player]; exact keep _ (by simp [reads])
  have sub : SectorEntry.subsector (enter s) = SectorEntry.subsector s := by
    unfold SectorEntry.subsector; rw [obj]; exact keep _ (by simp [reads])
  have sec : SectorEntry.sector (enter s) = SectorEntry.sector s := by
    unfold SectorEntry.sector; rw [sub]; exact keep _ (by simp [reads])
  refine ⟨player,obj,sub,sec,?_,?_,?_⟩
  · unfold SectorEntry.zWord; rw [obj]; exact keep _ (by simp [reads])
  · unfold SectorEntry.floorWord; rw [sec]; exact keep _ (by simp [reads])
  · unfold SectorEntry.special; rw [sec,← SectorDispatch.load_half]
    rw [show (enter s).memory = saved s from rfl,keep _ (by simp [reads]),SectorDispatch.load_half]

theorem establishes_inputs (s : X86Memory.State) (z floor : Fixed) (n : Int32) (h : Inputs s z floor n) :
    SectorEntry.Inputs (enter s) z floor n := by
  obtain ⟨player,obj,sub,sec,zkeep,fkeep,special⟩ := lookup_preserved s z floor n h
  have keep (a : Word) (ha : a ∈ reads s) := saved_load s a (h.stackApart a ha)
  refine ⟨special.trans h.isSecret,zkeep.trans h.height,fkeep.trans h.floor,?_,?_,?_,?_⟩
  · rw [player]; exact (keep _ (by simp [reads])).trans h.count
  · simpa [SectorSecret.Separate,SectorSecret.countAddress,SectorSecret.specialAddress,
      SectorEntry.afterSwitch,SectorEntry.prepared,put,write,player,sec] using h.separate
  · intro j i
    have base : (enter s).regs 4 + BitVec.ofNat 32 (j.val*4) ∈ slots s := by
      have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by
        have bound := j.isLt; simp only [Fin.ext_iff]; omega
      rcases hj with rfl|rfl|rfl|rfl|rfl <;>
        simp [enter,write,slots,BitVec.sub_eq_add_neg,BitVec.add_assoc] <;> decide
    have c := h.stackApart _ (by simp [reads] : SectorEntry.player s+(212#32) ∈ reads s) _ base
    have v := h.stackApart _ (by simp [reads] : SectorEntry.sector s+(14#32) ∈ reads s) _ base
    change ¬ SectorSecret.Written (SectorEntry.afterSwitch (enter s)) _
    simp only [SectorSecret.Written,SectorSecret.countAddress,SectorSecret.specialAddress,
      SectorEntry.afterSwitch,SectorEntry.prepared,put,write,↓reduceIte]
    simp only [player,sec]
    rintro (⟨k,hk⟩|h0|h1)
    · exact c k i hk.symm
    · have bad := v 0 i; exact bad (by simpa using h0.symm)
    · exact v 1 i h1.symm
  · rw [return_address]; decide

theorem contains_entry (pc : Nat) (h : SectorEntry.program pc ≠ none) :
    program pc = SectorEntry.program pc := by
  have bound := SectorEntry.program_bound pc h
  simp only [program,bytesProgram,show ¬(0x333d0 ≤ pc ∧ pc < 0x333e5) from by omega,↓reduceIte,SectorEntry.program]

/-- CALL and PUSHes establish the already-proved handler path, continuously. -/
theorem execution (s : X86Memory.State) (flags : Option Flags) (z floor : Fixed) (n : Int32)
    (h : Inputs s z floor n) :
    X86CodeMemory.run (SectorEntry.codeMemory SectorEntry.tableBytes) program [0x333e5] 25
      ⟨s,flags,0x333e0⟩ = some (SectorEntry.result (enter s)) := by
  have tail := SectorEntry.execution (enter s) flags z floor n (establishes_inputs s z floor n h)
  rw [return_address] at tail
  have actual : X86CodeMemory.run (SectorEntry.codeMemory SectorEntry.tableBytes) program [0x333e5] 20
      ⟨enter s,flags,0x2fb24⟩ = some (SectorEntry.result (enter s)) := by
    rw [X86CodeMemory.run_sound _ program SectorEntry.program contains_entry _ _ _ (by rw [tail]; simp),tail]
  exact (call_prefix s flags).finish actual 25 (by decide)

def preserved (s : X86Memory.State) := (s.regs 1,s.regs 2,s.regs 3,s.regs 4,s.regs 5,s.regs 6,s.regs 7)

theorem restores (s : X86Memory.State) :
    preserved (SectorEntry.result (enter s)).core = preserved s := by
  have words := saved_words s
  simp only [Prod.mk.injEq] at words
  simp [SectorEntry.result,SectorSecret.final,SectorSecret.restored,preserved,
    SectorEntry.afterSwitch,SectorEntry.prepared,enter,put,write,
    BitVec.sub_eq_add_neg,BitVec.add_assoc] at words ⊢
  split <;> simp_all [write,BitVec.add_assoc]

theorem observation (s : X86Memory.State) (flags : Option Flags) (z floor : Fixed) (n : Int32)
    (h : Inputs s z floor n) :
    (X86CodeMemory.run (SectorEntry.codeMemory SectorEntry.tableBytes) program [0x333e5] 25
      ⟨s,flags,0x333e0⟩).map (fun t =>
      (t.pc,load16 t.core.memory (SectorEntry.sector s+(14#32)),
        load32 t.core.memory (SectorEntry.player s+(212#32)),preserved t.core)) =
      some (0x333e5,BitVec.ofNat 16 (LevelSpecials.secret 9 z floor n).1,
        (LevelSpecials.secret 9 z floor n).2.toBitVec,preserved s) := by
  rw [execution s flags z floor n h]
  have fields := SectorEntry.fields (enter s) z floor n (establishes_inputs s z floor n h)
  obtain ⟨player,obj,sub,sec,rest⟩ := lookup_preserved s z floor n h
  rw [player,sec] at fields
  simp only [Prod.mk.injEq] at fields
  simp only [Option.map_some,fields.1,fields.2,restores]
  have pc : (SectorEntry.result (enter s)).pc = 0x333e5 := by
    unfold SectorEntry.result
    split <;> exact return_address s
  rw [pc]

/-- The caller obtains the handler argument from EDX, without changing memory. -/
def argument (s : X86Memory.State) : X86Memory.State := put s 0 (s.regs 2)

theorem dispatch_prefix (s : X86Memory.State) (flags : Option Flags)
    (secret : SectorDispatch.special s = 9) :
    X86CodeMemory.Prefix (SectorEntry.codeMemory SectorEntry.tableBytes) program [0x333e5] 6
      ⟨s,flags,0x333d0⟩ ⟨argument s,some (X86Routine.compare16 9 0),0x333e0⟩ := by
  let a := put s 0 (SectorDispatch.object s)
  let b := put s 0 (SectorDispatch.subsector s)
  let c := put s 0 (SectorDispatch.sector s)
  have shadow (t : X86Memory.State) (r : Reg) (v w : Word) : put (put t r v) r w = put t r w := by
    simp only [put,PlayerHeight.Function.write_shadow]
  apply X86CodeMemory.Prefix.step (middle := ⟨a,flags,0x333d2⟩) (by simp)
    (show program 0x333d0 = some (.control (.block (.legacy (.load 0 2 0))),2) from by decide) (by
      simp [X86CodeMemory.execute,X86Routine.execute,X86Control.execute,X86Block.execute,
        X86Memory.execute,blockPreservesFlags,a,SectorDispatch.object])
  apply X86CodeMemory.Prefix.step (middle := ⟨b,flags,0x333d5⟩) (by simp)
    (show program 0x333d2 = some (.control (.block (.legacy (.load 0 0 52))),3) from by decide) (by
      simp [X86CodeMemory.execute,X86Routine.execute,X86Control.execute,X86Block.execute,
        X86Memory.execute,blockPreservesFlags,a,b,SectorDispatch.subsector,put,write,PlayerHeight.Function.write_shadow])
  apply X86CodeMemory.Prefix.step (middle := ⟨c,flags,0x333d7⟩) (by simp)
    (show program 0x333d5 = some (.control (.block (.legacy (.load 0 0 0))),2) from by decide) (by
      simp [X86CodeMemory.execute,X86Routine.execute,X86Control.execute,X86Block.execute,
        X86Memory.execute,blockPreservesFlags,b,c,SectorDispatch.sector,put,write,PlayerHeight.Function.write_shadow])
  apply X86CodeMemory.Prefix.step (middle := ⟨c,some (X86Routine.compare16 9 0),0x333dc⟩) (by simp)
    (show program 0x333d7 = some (.compareHalf ⟨some 0,none,0,14⟩ 0,5) from by decide) (by
      have hs : load16 s.memory (SectorDispatch.sector s+(14#32)) = (9#16) := secret
      simp [X86CodeMemory.execute,X86Routine.execute,X86Block.Address.eval,c,put,write,hs])
  apply X86CodeMemory.Prefix.step (middle := ⟨c,some (X86Routine.compare16 9 0),0x333de⟩) (by simp)
    (show program 0x333dc = some (.control (.jumpZero true 7),2) from by decide) (by rfl)
  apply X86CodeMemory.Prefix.step (middle := ⟨argument s,some (X86Routine.compare16 9 0),0x333e0⟩) (by simp)
    (show program 0x333de = some (.control (.block (.legacy (.mov 0 2))),2) from by decide) (by
      simp [X86CodeMemory.execute,X86Routine.execute,X86Control.execute,X86Block.execute,
        X86Memory.execute,blockPreservesFlags,c,argument,put,write,PlayerHeight.Function.write_shadow])
  exact X86CodeMemory.Prefix.nil _

/-- Start before the sector lookup and continue through the actual CALL/RET.
The contract on `argument s` describes initial memory addressed by EDX; it does
not assume an intermediate execution result or preinstalled stack contents. -/
theorem dispatched_execution (s : X86Memory.State) (flags : Option Flags) (z floor : Fixed) (n : Int32)
    (h : Inputs (argument s) z floor n) :
    X86CodeMemory.run (SectorEntry.codeMemory SectorEntry.tableBytes) program [0x333e5] 31
      ⟨s,flags,0x333d0⟩ = some (SectorEntry.result (enter (argument s))) := by
  have special : SectorDispatch.special s = 9 := by
    simpa [SectorEntry.special,SectorEntry.sector,SectorEntry.subsector,SectorEntry.object,SectorEntry.player,
      SectorDispatch.special,SectorDispatch.sector,SectorDispatch.subsector,SectorDispatch.object,argument,put,write] using h.isSecret
  exact (dispatch_prefix s flags special).finish
    (execution (argument s) (some (X86Routine.compare16 9 0)) z floor n h) 31 (by decide)

theorem dispatched_observation (s : X86Memory.State) (flags : Option Flags) (z floor : Fixed) (n : Int32)
    (h : Inputs (argument s) z floor n) :
    (X86CodeMemory.run (SectorEntry.codeMemory SectorEntry.tableBytes) program [0x333e5] 31
      ⟨s,flags,0x333d0⟩).map (fun t =>
      (t.pc,load16 t.core.memory (SectorDispatch.sector s+(14#32)),
        load32 t.core.memory (s.regs 2+(212#32)),preserved t.core)) =
      some (0x333e5,BitVec.ofNat 16 (LevelSpecials.secret 9 z floor n).1,
        (LevelSpecials.secret 9 z floor n).2.toBitVec,preserved s) := by
  have obs := observation (argument s) (some (X86Routine.compare16 9 0)) z floor n h
  rw [execution (argument s) (some (X86Routine.compare16 9 0)) z floor n h] at obs
  rw [dispatched_execution s flags z floor n h]
  simpa [SectorEntry.sector,SectorEntry.subsector,SectorEntry.object,SectorEntry.player,
    SectorDispatch.sector,SectorDispatch.subsector,SectorDispatch.object,argument,preserved,put,write] using obs

end Doom.Proofs.SectorCaller
