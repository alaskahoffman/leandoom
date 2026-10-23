import Doom.Proofs.OriginalFloorCaller
import Doom.Proofs.OriginalSectorJoined

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.FloorJoined
open Verification X86 X86Memory X86Control BlockSummary
open FloorDamage (Kind)

/-- Transport the initial floor contract through a memory frame, not through
an assumed intermediate execution. Only EDX and ESP must survive in registers. -/
theorem transport (kind : Kind) (s t : X86Memory.State) (z floor : Fixed) (tick : Nat)
    (suit : Bool) (rng : DoomRandom) (h : FloorCaller.Inputs kind s z floor tick suit rng)
    (player : t.regs 2 = s.regs 2) (stack : t.regs 4 = s.regs 4)
    (keep : ∀ a, a ∈ FloorCaller.reads s → load32 t.memory a = load32 s.memory a)
    (table : t.memory (FloorCaller.tableAddress rng) = s.memory (FloorCaller.tableAddress rng)) :
    FloorCaller.Inputs kind t z floor tick suit rng := by
  have obj : SectorDispatch.object t = SectorDispatch.object s := by
    unfold SectorDispatch.object; rw [player,keep _ (by simp [FloorCaller.reads])]
  have sub : SectorDispatch.subsector t = SectorDispatch.subsector s := by
    unfold SectorDispatch.subsector; rw [obj,keep _ (by simp [FloorCaller.reads])]
  have sec : SectorDispatch.sector t = SectorDispatch.sector s := by
    unfold SectorDispatch.sector; rw [sub,keep _ (by simp [FloorCaller.reads])]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,table.trans h.table,?_,?_,?_⟩
  · unfold SectorDispatch.special
    rw [sec,← SectorDispatch.load_half,keep _ (by simp [FloorCaller.reads]),SectorDispatch.load_half]
    exact h.isKind
  · rw [obj,keep _ (by simp [FloorCaller.reads])]; exact h.height
  · rw [sec,keep _ (by simp [FloorCaller.reads])]; exact h.floor
  · rw [player,keep _ (by simp [FloorCaller.reads])]; exact h.suit
  · have byte := congrArg (fun w : Word => w.extractLsb' 0 8)
      (keep (0x2cf80#32) (by simp [FloorCaller.reads]))
    simp only [PlayerHeight.load_byte] at byte
    exact byte.trans h.clock
  · exact (keep _ (by simp [FloorCaller.reads])).trans h.index
  · exact (keep _ (by simp [FloorCaller.reads])).trans h.misc
  · simpa [FloorCaller.reads,FloorCaller.slots,SectorCaller.slots,FloorCaller.rngSlot,player,stack,obj,sub,sec] using h.stackSafe
  · simpa [FloorCaller.slots,SectorCaller.slots,FloorCaller.rngSlot,stack] using h.tableSafe
  · simpa only [player] using h.targetIndexSafe

/-- The floor decision can write only these six stack words and the RNG index. -/
def effectWrites (s : X86Memory.State) := FloorCaller.slots s ++ [(0x12720#32)]

theorem effect_locations (s t : X86Memory.State) (stack : t.regs 4 = s.regs 4) :
    effectWrites t = effectWrites s := by
  simp only [effectWrites,FloorCaller.slots,SectorCaller.slots,FloorCaller.rngSlot,stack]

theorem handler_frame (kind : Kind) (s : X86Memory.State) (z floor : Fixed) (tick : Nat)
    (suit : Bool) (rng : DoomRandom) (h : FloorCaller.Inputs kind s z floor tick suit rng) :
    PlayerHeight.Frame s.memory (FloorCaller.result kind s rng).core.memory (effectWrites s) := by
  intro a ha
  have saved := SectorCaller.saved_load s a (fun b hb => ha b (by simp [effectWrites,FloorCaller.slots,hb]))
  rw [FloorCaller.memory_frame kind s z floor tick suit rng h]
  split
  · rw [load_store_apart _ _ _ _ (ha _ (by simp [effectWrites])),
      load_store_apart _ _ _ _ (ha _ (by simp [effectWrites,FloorCaller.slots]))]
    exact saved
  · exact saved

/-- Both directions of preservation are stated on the original entry state:
preparation preserves floor inputs; the handler preserves prepared outputs. -/
structure Inputs (kind : Kind) (s : X86Memory.State) (body : Motion) (anim : PlayerAnim.State)
    (cmd : Ticcmd) (timer : Int32) (v : ViewState) (time : Int32) (cached live : Bool)
    (floor : Fixed) (tick : Nat) (suit : Bool) (rng : DoomRandom) : Prop where
  preparation : PlayerHeightJoin.Inputs s body anim cmd timer v time cached live
  floorInputs : FloorCaller.Inputs kind s body.z floor tick suit rng
  floorReads : ∀ a, a ∈ FloorCaller.reads s → ∀ b, b ∈ SectorDispatch.writes s → Apart a b
  tableRead : ∀ b, b ∈ SectorDispatch.writes s → Apart (FloorCaller.tableAddress rng) b
  preparedReads : ∀ a, a ∈ SectorJoined.preparedReads s → ∀ b, b ∈ effectWrites s → Apart a b

def bytesProgram (reaction movement setter heightCaller height caller entry cases rng : List UInt8) : X86Routine.Program := fun pc =>
  match FloorCaller.bytesProgram caller entry cases rng pc with
  | some op => some op
  | none => PlayerPreparation.bytesProgram reaction movement setter heightCaller height pc

def program := bytesProgram PlayerReactionProof.callerBytes PlayerFunction.functionBytes Doom19.setMobjStateBytes
  PlayerHeight.Caller.callBytes PlayerHeight.code SectorCaller.callBytes SectorEntry.entryBytes FloorDamage.code Doom19.playRandomBytes
abbrev cm := FloorEntry.cm

theorem contains_caller (pc : Nat) (h : FloorCaller.program pc ≠ none) : program pc = FloorCaller.program pc := by
  change (match FloorCaller.program pc with | some op => some op | none => PlayerPreparation.program pc) = _
  cases he : FloorCaller.program pc <;> simp_all

theorem contains_preparation (pc : Nat) (h : PlayerPreparation.program pc ≠ none) : program pc = PlayerPreparation.program pc := by
  have bound := SectorDispatch.preparation_bound pc h
  have lower : 0x30ea0 ≤ pc := by
    change (match PlayerHeight.Shared.program pc with | some op => some op | none => PlayerReactionProof.program pc) ≠ none at h
    cases hh : PlayerHeight.Shared.program pc with
    | none =>
      rw [hh] at h
      have r := PlayerPreparation.reaction_region pc h
      omega
    | some op =>
      unfold PlayerHeight.Shared.program PlayerHeight.Shared.bytesProgram at hh
      split at hh
      next hp => omega
      next hp => split at hh
                 next hc => change 0x33030 ≤ pc ∧ _ at hc; omega
                 next hc => simp_all
  have absent : FloorCaller.program pc = none := by
    unfold FloorCaller.program FloorCaller.bytesProgram
    rw [if_neg (by omega)]
    unfold FloorEntry.bytesProgram FloorDamage.bytesProgram
    rw [if_neg (by change ¬(0x2fb20 ≤ pc ∧ pc < 0x2fb20+55); omega),
      if_neg (by change ¬(0x2fb57 ≤ pc ∧ pc < 0x2fb57+133); omega),
      if_neg (by change ¬(0x24160 ≤ pc ∧ pc < 0x24160+28); omega)]
  change (match FloorCaller.program pc with | some op => some op | none => PlayerPreparation.program pc) = _
  rw [absent]

/-- No preparation instruction is a floor exit, even though all floor exits
are numerically below the preparation code. -/
theorem preparation_active (pc : Nat) (h : PlayerPreparation.program pc ≠ none) : pc ∉ FloorDamage.exits := by
  simp only [FloorDamage.exits,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false,not_or]
  constructor
  · intro eq; subst pc; exact h (by decide)
  constructor
  · intro eq; subst pc; exact h (by decide)
  constructor <;> intro eq <;> subst pc <;> exact h (by decide)

/-- One uninterrupted original-byte run. The floor contract at the handoff
is derived using preparation's frame and preserved registers. -/
theorem execution (kind : Kind) (s : X86Memory.State) (flags : Option Flags)
    (body : Motion) (anim : PlayerAnim.State) (cmd : Ticcmd) (timer : Int32)
    (v : ViewState) (time : Int32) (cached live : Bool) (floor : Fixed)
    (tick : Nat) (suit : Bool) (rng : DoomRandom)
    (h : Inputs kind s body anim cmd timer v time cached live floor tick suit rng) :
    ∃ u, X86CodeMemory.run cm program FloorDamage.exits 267 ⟨s,flags,0x333b1⟩ = some u ∧
      PreparedState.read (s.regs 2) (PlayerCaller.object s) u.core.memory =
        PreparedState.expected body anim cmd timer v time cached live ∧
      FloorDamage.observe u =
        (let answer := LevelSpecials.floorDamage kind.special body.z floor suit tick rng
        (answer.1,BitVec.ofNat 32 answer.2.play.toNat,BitVec.ofNat 32 answer.2.misc.toNat)) ∧
      u.core.regs 4 = s.regs 4-(20#32) ∧
      (FloorDamage.requested u ≠ 0 → u.core.regs 0 = PlayerCaller.object s ∧
        u.core.regs 2 = (0#32) ∧ u.core.regs 3 = (0#32) ∧
        program u.pc = some (.call ((0x2a460 : Int)-(u.pc+5)),5)) ∧
      PlayerHeight.Frame s.memory u.core.memory (SectorDispatch.writes s ++ effectWrites s) := by
  obtain ⟨t,run,pc,_,_,sp,_,edx⟩ := PlayerPreparation.execution_preserved s flags body anim cmd timer v time cached live h.preparation
  obtain ⟨t',run',_,prepared,_,frame⟩ := PreparedState.execution s flags body anim cmd timer v time cached live h.preparation
  have same : t' = t := Option.some.inj (run'.symm.trans run)
  subst t'
  have keep (a : Word) (ha : a ∈ FloorCaller.reads s) : load32 t.core.memory a = load32 s.memory a :=
    frame a (h.floorReads a ha)
  have ht := transport kind s t.core body.z floor tick suit rng h.floorInputs edx sp keep (frame.byte _ h.tableRead)
  let u := FloorCaller.result kind t.core rng
  have tail := FloorCaller.execution kind t.core t.flags body.z floor tick suit rng ht
  have obs := FloorCaller.correspondence kind t.core t.flags body.z floor tick suit rng ht
  rw [tail] at obs
  simp only [Option.map_some,Option.some.injEq] at obs
  have memory := handler_frame kind t.core body.z floor tick suit rng ht
  rw [effect_locations s t.core sp] at memory
  have words : PreparedState.read (s.regs 2) (PlayerCaller.object s) u.core.memory =
      PreparedState.read (s.regs 2) (PlayerCaller.object s) t.core.memory :=
    SectorJoined.prepared_read_frame s _ _ (fun a ha => memory a (h.preparedReads a ha))
  obtain ⟨k,bound,path,_⟩ := X86Routine.run_path run
  have first := (X86CodeMemory.lift_routine path cm SectorJoined.preparation_ordinary).transfer
    program FloorDamage.exits contains_preparation preparation_active
  have actual : X86CodeMemory.run cm program FloorDamage.exits 42 t = some u := by
    have entry : t = ⟨t.core,t.flags,0x333d0⟩ := by rw [← pc]
    rw [entry,X86CodeMemory.run_sound _ program FloorCaller.program contains_caller _ _ _ (by rw [tail]; simp),tail]
  refine ⟨u,first.finish actual 267 (by omega),words.trans prepared,obs,?_,?_,?_⟩
  · exact (FloorCaller.stack_position kind t.core rng).trans (congrArg (·-(20#32)) sp)
  · intro nonzero
    obtain ⟨target,inflictor,source,call⟩ := FloorCaller.damage_arguments kind t.core body.z floor tick suit rng ht nonzero
    refine ⟨?_,inflictor,source,?_⟩
    · have obj : SectorDispatch.object t.core = PlayerCaller.object s := by
        unfold SectorDispatch.object
        rw [edx,keep _ (by simp [FloorCaller.reads])]
        rfl
      exact target.trans obj
    · change program (FloorCaller.result kind t.core rng).pc = _
      rw [contains_caller _ (by rw [call]; simp),call]
  · intro a ha
    exact (memory a (fun b hb => ha b (List.mem_append_right _ hb))).trans
      (frame a (fun b hb => ha b (List.mem_append_left _ hb)))

def observe (s : X86Memory.State) (t : X86Control.State) :=
  (PreparedState.read (s.regs 2) (PlayerCaller.object s) t.core.memory,FloorDamage.observe t,t.core.regs 4)

theorem correspondence (kind : Kind) (s : X86Memory.State) (flags : Option Flags)
    (body : Motion) (anim : PlayerAnim.State) (cmd : Ticcmd) (timer : Int32)
    (v : ViewState) (time : Int32) (cached live : Bool) (floor : Fixed)
    (tick : Nat) (suit : Bool) (rng : DoomRandom)
    (h : Inputs kind s body anim cmd timer v time cached live floor tick suit rng) :
    (X86CodeMemory.run cm program FloorDamage.exits 267 ⟨s,flags,0x333b1⟩).map (observe s) =
      let answer := LevelSpecials.floorDamage kind.special body.z floor suit tick rng
      some (PreparedState.expected body anim cmd timer v time cached live,
        (answer.1,BitVec.ofNat 32 answer.2.play.toNat,BitVec.ofNat 32 answer.2.misc.toNat),s.regs 4-(20#32)) := by
  obtain ⟨u,run,words,damage,sp,_,_⟩ := execution kind s flags body anim cmd timer v time cached live floor tick suit rng h
  rw [run]
  simp only [Option.map_some,observe,words,damage,sp]

end Doom.Proofs.FloorJoined
