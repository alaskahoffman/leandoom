import Doom.Proofs.OriginalFloorEntry
import Doom.Proofs.OriginalSectorCaller

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.FloorCaller
open Verification X86 X86Memory X86Control BlockSummary
open FloorDamage (Kind)

/-- The original outer dispatch, CALL, handler entry, and damaging-floor cases. -/
def bytesProgram (caller entry cases rng : List UInt8) : X86Routine.Program := fun pc =>
  if 0x333d0 ≤ pc ∧ pc < 0x333e5 then X86Routine.decodeAt caller (pc-0x333d0)
  else FloorEntry.bytesProgram entry cases rng pc

def program := bytesProgram SectorCaller.callBytes SectorEntry.entryBytes FloorDamage.code Doom19.playRandomBytes
abbrev cm := FloorEntry.cm
abbrev argument := SectorCaller.argument
abbrev enter := SectorCaller.enter
abbrev saved := SectorCaller.saved

def entered (s : X86Memory.State) := enter (argument s)
def rngSlot (s : X86Memory.State) := s.regs 4-(24#32)
def slots (s : X86Memory.State) := SectorCaller.slots s ++ [rngSlot s]
def reads (s : X86Memory.State) : List Word :=
  [s.regs 2,SectorDispatch.object s+(52#32),SectorDispatch.subsector s,
   SectorDispatch.object s+(20#32),SectorDispatch.sector s,SectorDispatch.sector s+(14#32),
   s.regs 2+(56#32),(0x2cf80#32),(0x12720#32),(0x1271c#32)]
def tableAddress (rng : DoomRandom) := (0x1261c#32)+FloorDamage.nextIndex rng.play

/-- All facts refer to initial memory and registers, before the outer dispatch.
The six stack slots include the possible nested P_Random return address. -/
structure Inputs (kind : Kind) (s : X86Memory.State) (z floor : Fixed) (time : Nat)
    (suit : Bool) (rng : DoomRandom) : Prop where
  isKind : SectorDispatch.special s = BitVec.ofNat 16 kind.special
  height : load32 s.memory (SectorDispatch.object s+(20#32)) = z.raw.toBitVec
  floor : load32 s.memory (SectorDispatch.sector s) = floor.raw.toBitVec
  suit : load32 s.memory (s.regs 2+(56#32)) = (0#32) ↔ suit = false
  clock : s.memory (0x2cf80#32) = BitVec.ofNat 8 time
  index : load32 s.memory (0x12720#32) = BitVec.ofNat 32 rng.play.toNat
  misc : load32 s.memory (0x1271c#32) = BitVec.ofNat 32 rng.misc.toNat
  table : s.memory (tableAddress rng) = FloorDamage.randomByte rng.play
  stackSafe : ∀ a, a ∈ reads s → ∀ b, b ∈ slots s → Apart a b
  tableSafe : ∀ b, b ∈ slots s → ∀ j : Fin 4, tableAddress rng ≠ b+BitVec.ofNat 32 j.val
  targetIndexSafe : Apart (s.regs 2) (0x12720#32)

theorem saved_byte (s : X86Memory.State) (a : Word)
    (safe : ∀ b, b ∈ SectorCaller.slots s → ∀ j : Fin 4, a ≠ b+BitVec.ofNat 32 j.val) :
    saved s a = s.memory a := by
  unfold saved SectorCaller.saved
  repeat rw [FloorDamage.byte_store _ _ _ _ (safe _ (by simp [SectorCaller.slots]))]

theorem entered_memory (s : X86Memory.State) : (entered s).memory = saved s := rfl
theorem entered_player (s : X86Memory.State) : (entered s).regs 0 = s.regs 2 := by
  simp [entered,enter,SectorCaller.enter,argument,SectorCaller.argument,put,write]
theorem entered_sp (s : X86Memory.State) : (entered s).regs 4 = s.regs 4-(20#32) := by
  simp [entered,enter,SectorCaller.enter,argument,SectorCaller.argument,put,write]

theorem called_memory (s : X86Memory.State) :
    (FloorDamage.called (entered s)).memory = store32 (saved s) (rngSlot s) (0x2fbb5#32) := by
  simp [FloorDamage.called,X86Routine.pushWord,entered_memory,entered_sp,rngSlot,BitVec.sub_sub]
theorem called_sp (s : X86Memory.State) :
    (FloorDamage.called (entered s)).regs 4 = rngSlot s := by
  simp [FloorDamage.called,X86Routine.pushWord,put,write,entered_sp,rngSlot,BitVec.sub_sub]

theorem apart_symm {a b : Word} (h : Apart a b) : Apart b a := fun i j => (h j i).symm

theorem table_index_apart (rng : DoomRandom) :
    ∀ j : Fin 4, tableAddress rng ≠ (0x12720#32)+BitVec.ofNat 32 j.val := by
  intro j eq
  have bound := (rng.play+1).toBitVec.isLt
  have jb := j.isLt
  have eq := congrArg BitVec.toNat eq
  simp only [tableAddress,FloorDamage.nextIndex,BitVec.toNat_add,BitVec.toNat_ofNat] at eq
  change (rng.play+1).toNat < 256 at bound
  omega

theorem call_prefix (s : X86Memory.State) (flags : Option Flags) :
    X86CodeMemory.Prefix cm program FloorDamage.exits 5
      ⟨s,flags,0x333e0⟩ ⟨enter s,flags,0x2fb24⟩ := by
  let c := X86Routine.pushWord s (0x333e5#32)
  let p1 := X86Routine.pushWord c (s.regs 3)
  let p2 := X86Routine.pushWord p1 (s.regs 1)
  let p3 := X86Routine.pushWord p2 (s.regs 2)
  let p4 := X86Routine.pushWord p3 (s.regs 6)
  apply X86CodeMemory.Prefix.step (middle := ⟨c,flags,0x2fb20⟩) (by simp [FloorDamage.exits])
    (show program 0x333e0 = some (.call (-14533),5) from by decide) (by
      simp [X86CodeMemory.execute,X86Routine.execute,c])
  apply X86CodeMemory.Prefix.step (middle := ⟨p1,flags,0x2fb21⟩)
    (by simp [FloorDamage.exits]) (show program 0x2fb20 = some (.push 3,1) from by decide) (by
      simp [X86CodeMemory.execute,X86Routine.execute,c,p1,p2,p3,p4,X86Routine.pushWord,put,write])
  apply X86CodeMemory.Prefix.step (middle := ⟨p2,flags,0x2fb22⟩)
    (by simp [FloorDamage.exits]) (show program 0x2fb21 = some (.push 1,1) from by decide) (by
      simp [X86CodeMemory.execute,X86Routine.execute,c,p1,p2,p3,p4,X86Routine.pushWord,put,write])
  apply X86CodeMemory.Prefix.step (middle := ⟨p3,flags,0x2fb23⟩)
    (by simp [FloorDamage.exits]) (show program 0x2fb22 = some (.push 2,1) from by decide) (by
      simp [X86CodeMemory.execute,X86Routine.execute,c,p1,p2,p3,p4,X86Routine.pushWord,put,write])
  apply X86CodeMemory.Prefix.step (middle := ⟨p4,flags,0x2fb24⟩)
    (by simp [FloorDamage.exits]) (show program 0x2fb23 = some (.push 6,1) from by decide) (by
      simp [X86CodeMemory.execute,X86Routine.execute,c,p1,p2,p3,p4,X86Routine.pushWord,put,write])

  simpa [c,p1,p2,p3,p4,enter,saved,SectorCaller.enter,SectorCaller.saved,X86Routine.pushWord,put,write,BitVec.sub_sub,
    BitVec.sub_eq_add_neg,BitVec.add_assoc,PlayerHeight.Function.write_shadow] using
    (X86CodeMemory.Prefix.nil (cm := SectorEntry.codeMemory SectorEntry.tableBytes)
      (program := program) (exits := FloorDamage.exits) ⟨enter s,flags,0x2fb24⟩)

theorem dispatch_prefix (kind : Kind) (s : X86Memory.State) (flags : Option Flags)
    (isKind : SectorDispatch.special s = BitVec.ofNat 16 kind.special) :
    X86CodeMemory.Prefix cm program FloorDamage.exits 6
      ⟨s,flags,0x333d0⟩ ⟨argument s,some (X86Routine.compare16 (BitVec.ofNat 16 kind.special) 0),0x333e0⟩ := by
  let a := put s 0 (SectorDispatch.object s)
  let b := put s 0 (SectorDispatch.subsector s)
  let c := put s 0 (SectorDispatch.sector s)
  have shadow (t : X86Memory.State) (r : Reg) (v w : Word) : put (put t r v) r w = put t r w := by
    simp only [put,PlayerHeight.Function.write_shadow]
  apply X86CodeMemory.Prefix.step (middle := ⟨a,flags,0x333d2⟩) (by simp [FloorDamage.exits])
    (show program 0x333d0 = some (.control (.block (.legacy (.load 0 2 0))),2) from by decide) (by
      simp [X86CodeMemory.execute,X86Routine.execute,X86Control.execute,X86Block.execute,
        X86Memory.execute,blockPreservesFlags,a,SectorDispatch.object])
  apply X86CodeMemory.Prefix.step (middle := ⟨b,flags,0x333d5⟩) (by simp [FloorDamage.exits])
    (show program 0x333d2 = some (.control (.block (.legacy (.load 0 0 52))),3) from by decide) (by
      simp [X86CodeMemory.execute,X86Routine.execute,X86Control.execute,X86Block.execute,
        X86Memory.execute,blockPreservesFlags,a,b,SectorDispatch.subsector,put,write,PlayerHeight.Function.write_shadow])
  apply X86CodeMemory.Prefix.step (middle := ⟨c,flags,0x333d7⟩) (by simp [FloorDamage.exits])
    (show program 0x333d5 = some (.control (.block (.legacy (.load 0 0 0))),2) from by decide) (by
      simp [X86CodeMemory.execute,X86Routine.execute,X86Control.execute,X86Block.execute,
        X86Memory.execute,blockPreservesFlags,b,c,SectorDispatch.sector,put,write,PlayerHeight.Function.write_shadow])
  apply X86CodeMemory.Prefix.step (middle := ⟨c,some (X86Routine.compare16 (BitVec.ofNat 16 kind.special) 0),0x333dc⟩) (by simp [FloorDamage.exits])
    (show program 0x333d7 = some (.compareHalf ⟨some 0,none,0,14⟩ 0,5) from by decide) (by
      have hs : load16 s.memory (SectorDispatch.sector s+(14#32)) = (BitVec.ofNat 16 kind.special) := isKind
      simp [X86CodeMemory.execute,X86Routine.execute,X86Block.Address.eval,c,put,write,hs])
  apply X86CodeMemory.Prefix.step (middle := ⟨c,some (X86Routine.compare16 (BitVec.ofNat 16 kind.special) 0),0x333de⟩) (by simp [FloorDamage.exits])
    (show program 0x333dc = some (.control (.jumpZero true 7),2) from by decide) (by cases kind <;> rfl)
  apply X86CodeMemory.Prefix.step (middle := ⟨argument s,some (X86Routine.compare16 (BitVec.ofNat 16 kind.special) 0),0x333e0⟩) (by simp [FloorDamage.exits])
    (show program 0x333de = some (.control (.block (.legacy (.mov 0 2))),2) from by decide) (by
      simp [X86CodeMemory.execute,X86Routine.execute,X86Control.execute,X86Block.execute,
        X86Memory.execute,blockPreservesFlags,c,argument,SectorCaller.argument,put,write,PlayerHeight.Function.write_shadow])
  exact X86CodeMemory.Prefix.nil _


/-- The actual five outer stack writes preserve every input word. -/
theorem saved_read (kind : Kind) (s : X86Memory.State) (z floor : Fixed) (time : Nat)
    (suit : Bool) (rng : DoomRandom) (h : Inputs kind s z floor time suit rng)
    (a : Word) (ha : a ∈ reads s) : load32 (saved s) a = load32 s.memory a :=
  SectorCaller.saved_load s a (fun b hb => h.stackSafe a ha b (by simp [slots,hb]))

/-- The possible nested random CALL also preserves those words. -/
theorem called_read (kind : Kind) (s : X86Memory.State) (z floor : Fixed) (time : Nat)
    (suit : Bool) (rng : DoomRandom) (h : Inputs kind s z floor time suit rng)
    (a : Word) (ha : a ∈ reads s) :
    load32 (FloorDamage.called (entered s)).memory a = load32 s.memory a := by
  rw [called_memory,load_store_apart _ _ _ _ (h.stackSafe a ha _ (by simp [slots]))]
  exact saved_read kind s z floor time suit rng h a ha

theorem lookup_preserved (kind : Kind) (s : X86Memory.State) (z floor : Fixed) (time : Nat)
    (suit : Bool) (rng : DoomRandom) (h : Inputs kind s z floor time suit rng) :
    SectorEntry.object (entered s) = SectorDispatch.object s ∧
    SectorEntry.subsector (entered s) = SectorDispatch.subsector s ∧
    SectorEntry.sector (entered s) = SectorDispatch.sector s ∧
    FloorEntry.zWord (entered s) = load32 s.memory (SectorDispatch.object s+(20#32)) ∧
    FloorEntry.floorWord (entered s) = load32 s.memory (SectorDispatch.sector s) ∧
    FloorEntry.special (entered s) = SectorDispatch.special s := by
  have keep := saved_read kind s z floor time suit rng h
  have obj : SectorEntry.object (entered s) = SectorDispatch.object s := by
    simp only [SectorEntry.object,SectorEntry.player,entered_player,entered_memory]
    exact keep _ (by simp [reads])
  have sub : SectorEntry.subsector (entered s) = SectorDispatch.subsector s := by
    simp only [SectorEntry.subsector,obj,entered_memory]
    exact keep _ (by simp [reads])
  have sec : SectorEntry.sector (entered s) = SectorDispatch.sector s := by
    simp only [SectorEntry.sector,sub,entered_memory]
    exact keep _ (by simp [reads])
  refine ⟨obj,sub,sec,?_,?_,?_⟩
  · simp only [FloorEntry.zWord,SectorEntry.zWord,obj,entered_memory]
    exact keep _ (by simp [reads])
  · simp only [FloorEntry.floorWord,SectorEntry.floorWord,sec,entered_memory]
    exact keep _ (by simp [reads])
  · simp only [FloorEntry.special,SectorEntry.special,sec,entered_memory,SectorDispatch.special]
    rw [← SectorDispatch.load_half,keep _ (by simp [reads]),SectorDispatch.load_half]

/-- Derive the entire entry contract from initial fields and byte separation.
No intermediate machine state or successful execution is a premise. -/
theorem establishes_inputs (kind : Kind) (s : X86Memory.State) (z floor : Fixed) (time : Nat)
    (suit : Bool) (rng : DoomRandom) (h : Inputs kind s z floor time suit rng) :
    FloorEntry.Inputs kind (entered s) z floor time suit rng := by
  obtain ⟨obj,sub,sec,hz,hf,hs⟩ := lookup_preserved kind s z floor time suit rng h
  have keep := saved_read kind s z floor time suit rng h
  have nested := called_read kind s z floor time suit rng h
  have safeByte (a : Word) (ha : a ∈ reads s) (b : Word) (hb : b ∈ slots s) :
      ∀ j : Fin 4, a ≠ b+BitVec.ofNat 32 j.val := by
    intro j; simpa using h.stackSafe a ha b hb 0 j
  have clock : saved s (0x2cf80#32) = s.memory (0x2cf80#32) :=
    saved_byte s _ (fun b hb => safeByte _ (by simp [reads]) b (by simp [slots,hb]))
  have randomClock : FloorDamage.randomMemory (FloorDamage.called (entered s)) rng.play (0x2cf80#32) = s.memory (0x2cf80#32) := by
    unfold FloorDamage.randomMemory
    rw [FloorDamage.byte_store _ _ _ _ (by decide),called_memory,
      FloorDamage.byte_store _ _ _ _ (safeByte _ (by simp [reads]) _ (by simp [slots])),clock]
  refine ⟨hs.trans h.isKind,hz.trans h.height,hf.trans h.floor,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [entered_player,entered_memory,keep _ (by simp [reads])]; exact h.suit
  · exact clock.trans h.clock
  · exact (keep _ (by simp [reads])).trans h.index
  · exact (keep _ (by simp [reads])).trans h.misc
  · intro _
    constructor
    · exact (nested _ (by simp [reads])).trans h.index
    · unfold FloorDamage.randomMemory
      change store32 _ _ _ (tableAddress rng) = _
      rw [FloorDamage.byte_store _ _ _ _ (table_index_apart rng),called_memory,
        FloorDamage.byte_store _ _ _ _ (h.tableSafe _ (by simp [slots]))]
      exact (saved_byte s _ (fun b hb => h.tableSafe b (by simp [slots,hb]))).trans h.table
    · simp only [FloorDamage.randomMemory,called_sp]
      rw [load_store_apart _ _ _ _ (apart_symm (h.stackSafe _ (by simp [reads]) _ (by simp [slots]))),
        called_memory,load_store]
  · exact randomClock.trans clock.symm
  · rw [entered_player,entered_memory]
    unfold FloorDamage.randomMemory
    rw [load_store_apart _ _ _ _ h.targetIndexSafe,nested _ (by simp [reads]),keep _ (by simp [reads])]
  · unfold FloorDamage.randomMemory
    rw [load_store_apart _ _ _ _ (by unfold Apart; decide : Apart (0x1271c#32) (0x12720#32)),
      nested _ (by simp [reads]),entered_memory,keep _ (by simp [reads])]

/-- The added caller interval does not overlap any handler or RNG byte. -/
theorem contains_entry (pc : Nat) (h : FloorEntry.program pc ≠ none) :
    program pc = FloorEntry.program pc := by
  unfold program bytesProgram
  split
  · rename_i range
    have e : SectorEntry.entryBytes.length = 55 := by decide
    have c : FloorDamage.code.length = 133 := by decide
    have r : Doom19.playRandomBytes.length = 28 := by decide
    have he : ¬(0x2fb20 ≤ pc ∧ pc < 0x2fb20+SectorEntry.entryBytes.length) := by omega
    have hc : ¬(0x2fb57 ≤ pc ∧ pc < 0x2fb57+FloorDamage.code.length) := by omega
    have hr : ¬(0x24160 ≤ pc ∧ pc < 0x24160+Doom19.playRandomBytes.length) := by omega
    simp [FloorEntry.program,FloorEntry.bytesProgram,FloorDamage.bytesProgram,he,hc,hr] at h
  · rfl

def result (kind : Kind) (s : X86Memory.State) (rng : DoomRandom) :=
  FloorEntry.result kind (entered s) rng

theorem execution (kind : Kind) (s : X86Memory.State) (flags : Option Flags)
    (z floor : Fixed) (time : Nat) (suit : Bool) (rng : DoomRandom)
    (h : Inputs kind s z floor time suit rng) :
    X86CodeMemory.run cm program FloorDamage.exits 42 ⟨s,flags,0x333d0⟩ = some (result kind s rng) := by
  have entry := establishes_inputs kind s z floor time suit rng h
  have caseInputs := FloorEntry.case_inputs kind (entered s) z floor time suit rng entry
  let f := some (X86Routine.compare16 (BitVec.ofNat 16 kind.special) 0)
  have tail := FloorEntry.execution kind (entered s) f rng entry.isKind caseInputs.random
  have lifted : X86CodeMemory.run cm program FloorDamage.exits 31 ⟨entered s,f,0x2fb24⟩ = some (result kind s rng) := by
    rw [X86CodeMemory.run_sound _ program FloorEntry.program contains_entry _ _ _ (by rw [tail]; simp),tail]
    rfl
  have called := (call_prefix (argument s) f).finish lifted 36 (by decide)
  exact (dispatch_prefix kind s flags h.isKind).finish called 42 (by decide)

theorem correspondence (kind : Kind) (s : X86Memory.State) (flags : Option Flags)
    (z floor : Fixed) (time : Nat) (suit : Bool) (rng : DoomRandom)
    (h : Inputs kind s z floor time suit rng) :
    (X86CodeMemory.run cm program FloorDamage.exits 42 ⟨s,flags,0x333d0⟩).map FloorDamage.observe =
      let answer := LevelSpecials.floorDamage kind.special z floor suit time rng
      some (answer.1,BitVec.ofNat 32 answer.2.play.toNat,BitVec.ofNat 32 answer.2.misc.toNat) := by
  have entry := establishes_inputs kind s z floor time suit rng h
  have caseInputs := FloorEntry.case_inputs kind (entered s) z floor time suit rng entry
  have obs := FloorEntry.correspondence kind (entered s) flags z floor time suit rng entry
  rw [FloorEntry.execution kind (entered s) flags rng entry.isKind caseInputs.random,Option.map_some] at obs
  rw [execution kind s flags z floor time suit rng h,Option.map_some]
  exact obs

theorem damage_arguments (kind : Kind) (s : X86Memory.State) (z floor : Fixed)
    (time : Nat) (suit : Bool) (rng : DoomRandom) (h : Inputs kind s z floor time suit rng)
    (nonzero : FloorDamage.requested (result kind s rng) ≠ 0) :
    let t := result kind s rng
    t.core.regs 0 = SectorDispatch.object s ∧ t.core.regs 2 = (0#32) ∧ t.core.regs 3 = (0#32) ∧
    program t.pc = some (.call ((0x2a460 : Int)-(t.pc+5)),5) := by
  obtain ⟨target,inflictor,source,call⟩ := FloorEntry.damage_arguments kind (entered s) z floor time suit rng
    (establishes_inputs kind s z floor time suit rng h) nonzero
  refine ⟨target.trans (lookup_preserved kind s z floor time suit rng h).1,inflictor,source,?_⟩
  change program (FloorEntry.result kind (entered s) rng).pc = _
  rw [contains_entry _ (by rw [call]; simp),call]
  rfl

/-- Five outer stack stores occur even off-floor. Only a suited heavy-floor
contact adds the nested return-address store and gameplay RNG-index store. -/
theorem memory_frame (kind : Kind) (s : X86Memory.State) (z floor : Fixed)
    (time : Nat) (suit : Bool) (rng : DoomRandom) (h : Inputs kind s z floor time suit rng) :
    (result kind s rng).core.memory =
      if z = floor ∧ (kind = .four ∨ kind = .sixteen) ∧ suit = true then
        store32 (store32 (saved s) (rngSlot s) (0x2fbb5#32)) (0x12720#32) (FloorDamage.nextIndex rng.play)
      else saved s := by
  have entry := establishes_inputs kind s z floor time suit rng h
  have ground := FloorEntry.floor_relation kind (entered s) z floor time suit rng entry
  have suitOn : load32 (entered s).memory ((entered s).regs 0+(56#32)) ≠ (0#32) ↔ suit = true := by
    simp only [ne_eq,entry.suit]; cases suit <;> simp
  unfold result
  rw [FloorEntry.memory_frame]
  simp only [ground,ne_eq,suitOn]
  simp only [FloorDamage.randomMemory,called_memory,entered_memory]

/-- Every byte outside the six potential stack words and RNG-index word is
unchanged. This includes all unmentioned caller memory, not only observed fields. -/
theorem memory_unchanged (kind : Kind) (s : X86Memory.State) (z floor : Fixed)
    (time : Nat) (suit : Bool) (rng : DoomRandom) (h : Inputs kind s z floor time suit rng)
    (a : Word) (stackSafe : ∀ b, b ∈ slots s → ∀ j : Fin 4, a ≠ b+BitVec.ofNat 32 j.val)
    (indexSafe : ∀ j : Fin 4, a ≠ (0x12720#32)+BitVec.ofNat 32 j.val) :
    (result kind s rng).core.memory a = s.memory a := by
  rw [memory_frame kind s z floor time suit rng h]
  split
  · rw [FloorDamage.byte_store _ _ _ _ indexSafe,
      FloorDamage.byte_store _ _ _ _ (stackSafe _ (by simp [slots]))]
    exact saved_byte s a (fun b hb => stackSafe b (by simp [slots,hb]))
  · exact saved_byte s a (fun b hb => stackSafe b (by simp [slots,hb]))

theorem stack_position (kind : Kind) (s : X86Memory.State) (rng : DoomRandom) :
    (result kind s rng).core.regs 4 = s.regs 4-(20#32) :=
  (FloorEntry.stack_preserved kind (entered s) rng).trans (entered_sp s)

end Doom.Proofs.FloorCaller
