import Doom.Proofs.OriginalSectorCaller
import Doom.Verification.X86CodeBridge

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.SectorJoined
open Verification X86 X86Memory X86Control BlockSummary

/-- Transport only initial input reads, with the player and stack pointers fixed. -/
theorem transport (s t : X86Memory.State) (z floor : Fixed) (n : Int32)
    (h : SectorCaller.Inputs s z floor n)
    (player : t.regs 0 = s.regs 0) (stack : t.regs 4 = s.regs 4)
    (keep : ∀ a, a ∈ SectorCaller.reads s → load32 t.memory a = load32 s.memory a) :
    SectorCaller.Inputs t z floor n := by
  have p : SectorEntry.player t = SectorEntry.player s := player
  have obj : SectorEntry.object t = SectorEntry.object s := by
    unfold SectorEntry.object; rw [p,keep _ (by simp [SectorCaller.reads])]
  have sub : SectorEntry.subsector t = SectorEntry.subsector s := by
    unfold SectorEntry.subsector; rw [obj,keep _ (by simp [SectorCaller.reads])]
  have sec : SectorEntry.sector t = SectorEntry.sector s := by
    unfold SectorEntry.sector; rw [sub,keep _ (by simp [SectorCaller.reads])]
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · change load16 t.memory (SectorEntry.sector t+(14#32)) = 9
    rw [sec,← SectorDispatch.load_half,keep _ (by simp [SectorCaller.reads]),SectorDispatch.load_half]
    exact h.isSecret
  · unfold SectorEntry.zWord; rw [obj,keep _ (by simp [SectorCaller.reads])]; exact h.height
  · unfold SectorEntry.floorWord; rw [sec,keep _ (by simp [SectorCaller.reads])]; exact h.floor
  · rw [p,keep _ (by simp [SectorCaller.reads])]; exact h.count
  · simpa [SectorSecret.Separate,SectorSecret.countAddress,SectorSecret.specialAddress,
      SectorEntry.afterSwitch,SectorEntry.prepared,put,write,p,sec] using h.separate
  · simpa [SectorCaller.reads,SectorCaller.slots,p,obj,sub,sec,stack] using h.stackApart

def effectWrites (s : X86Memory.State) : List Word :=
  SectorCaller.slots s ++ [SectorEntry.player s+(212#32),SectorEntry.sector s+(14#32)]

/-- Words outside the caller's stack and secret-field writes survive the whole handler. -/
theorem handler_frame (s : X86Memory.State) (z floor : Fixed) (n : Int32)
    (h : SectorCaller.Inputs s z floor n) :
    PlayerHeight.Frame s.memory (SectorEntry.result (SectorCaller.enter s)).core.memory (effectWrites s) := by
  obtain ⟨p,obj,sub,sec,rest⟩ := SectorCaller.lookup_preserved s z floor n h
  intro a ha
  have stack := SectorCaller.saved_load s a (fun b hb => ha b (List.mem_append_left _ hb))
  have count := ha (SectorEntry.player s+(212#32)) (by simp [effectWrites])
  have special := ha (SectorEntry.sector s+(14#32)) (by simp [effectWrites])
  have half : ∀ i : Fin 4, a+BitVec.ofNat 32 i.val ≠ SectorEntry.sector s+(14#32) ∧
      a+BitVec.ofNat 32 i.val ≠ SectorEntry.sector s+(14#32)+1 := by
    intro i; exact ⟨by simpa using special i 0,by simpa using special i 1⟩
  unfold SectorEntry.result
  split
  · change load32 (SectorSecret.updated (SectorEntry.afterSwitch (SectorCaller.enter s))).memory a = _
    simp only [SectorSecret.updated,SectorSecret.countAddress,SectorSecret.specialAddress,
      SectorEntry.afterSwitch,SectorEntry.prepared,put,write,↓reduceIte]
    simp only [p,sec]
    simp only [show (6 : Reg) ≠ 2 by decide,show (6 : Reg) ≠ 1 by decide,show (6 : Reg) ≠ 0 by decide,show (1 : Reg) ≠ 2 by decide,↓reduceIte]
    rw [SectorSecret.load32_store16 _ _ _ _ half,load_store_apart _ _ _ _ count]
    exact stack
  · exact stack

/-- Every word in the already-proved eleven-field projection. -/
def preparedReads (s : X86Memory.State) : List Word :=
  PreparedState.retainedReads s ++ PlayerHeight.viewWrites (s.regs 2) ++ [s.regs 2+(16#32)]

theorem prepared_read_frame (s : X86Memory.State) (m m' : Memory)
    (keep : ∀ a, a ∈ preparedReads s → load32 m' a = load32 m a) :
    PreparedState.read (s.regs 2) (PlayerCaller.object s) m' =
      PreparedState.read (s.regs 2) (PlayerCaller.object s) m := by
  unfold PreparedState.read
  rw [
    keep (PlayerCaller.object s+(32#32)) (by simp [preparedReads,PreparedState.retainedReads,PlayerHeight.viewWrites,PlayerReactionProof.timerAddress]),
    keep (PlayerCaller.object s+(72#32)) (by simp [preparedReads,PreparedState.retainedReads,PlayerHeight.viewWrites,PlayerReactionProof.timerAddress]),
    keep (PlayerCaller.object s+(76#32)) (by simp [preparedReads,PreparedState.retainedReads,PlayerHeight.viewWrites,PlayerReactionProof.timerAddress]),
    keep (PlayerCaller.object s+(100#32)) (by simp [preparedReads,PreparedState.retainedReads,PlayerHeight.viewWrites,PlayerReactionProof.timerAddress]),
    keep (PlayerCaller.object s+(96#32)) (by simp [preparedReads,PreparedState.retainedReads,PlayerHeight.viewWrites,PlayerReactionProof.timerAddress]),
    keep (PlayerCaller.object s+(124#32)) (by simp [preparedReads,PreparedState.retainedReads,PlayerHeight.viewWrites,PlayerReactionProof.timerAddress]),
    keep (s.regs 2+(20#32)) (by simp [preparedReads,PreparedState.retainedReads,PlayerHeight.viewWrites,PlayerReactionProof.timerAddress]),
    keep (s.regs 2+(24#32)) (by simp [preparedReads,PreparedState.retainedReads,PlayerHeight.viewWrites,PlayerReactionProof.timerAddress]),
    keep (s.regs 2+(16#32)) (by simp [preparedReads,PreparedState.retainedReads,PlayerHeight.viewWrites,PlayerReactionProof.timerAddress]),
    keep (s.regs 2+(28#32)) (by simp [preparedReads,PreparedState.retainedReads,PlayerHeight.viewWrites,PlayerReactionProof.timerAddress]),
    keep (0x2cf90) (by simp [preparedReads,PreparedState.retainedReads,PlayerHeight.viewWrites,PlayerReactionProof.timerAddress])]

structure Inputs (s : X86Memory.State) (body : Motion) (anim : PlayerAnim.State) (cmd : Ticcmd)
    (timer : Int32) (v : ViewState) (time : Int32) (cached live : Bool) (floor : Fixed) (n : Int32) : Prop where
  preparation : PlayerHeightJoin.Inputs s body anim cmd timer v time cached live
  sector : SectorCaller.Inputs (SectorCaller.argument s) body.z floor n
  sectorReads : ∀ a, a ∈ SectorCaller.reads (SectorCaller.argument s) →
    ∀ b, b ∈ SectorDispatch.writes s → Apart a b
  preparedReads : ∀ a, a ∈ SectorJoined.preparedReads s →
    ∀ b, b ∈ effectWrites (SectorCaller.argument s) → Apart a b

def bytesProgram (reaction movement setter heightCaller height caller entry secret epilogue : List UInt8) : X86Routine.Program := fun pc =>
  match SectorCaller.bytesProgram caller entry secret epilogue pc with
  | some op => some op
  | none => PlayerPreparation.bytesProgram reaction movement setter heightCaller height pc

def program := bytesProgram PlayerReactionProof.callerBytes PlayerFunction.functionBytes Doom19.setMobjStateBytes
  PlayerHeight.Caller.callBytes PlayerHeight.code SectorCaller.callBytes SectorEntry.entryBytes SectorSecret.code SectorEntry.returnBytes

theorem contains_caller (pc : Nat) (h : SectorCaller.program pc ≠ none) : program pc = SectorCaller.program pc := by
  change (match SectorCaller.program pc with | some op => some op | none => PlayerPreparation.program pc) = _
  cases he : SectorCaller.program pc <;> simp_all

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
  have absent : SectorCaller.program pc = none := by
    unfold SectorCaller.program SectorCaller.bytesProgram
    rw [if_neg (by omega)]
    unfold SectorEntry.bytesProgram
    rw [if_neg (by change ¬(0x2fb20 ≤ pc ∧ pc < 0x2fb20+55); omega),
      if_neg (by change ¬(0x2fbdc ≤ pc ∧ pc < 0x2fbdc+17); omega),
      if_neg (by change ¬(0x2fc39 ≤ pc ∧ pc < 0x2fc39+5); omega)]
  change (match SectorCaller.program pc with | some op => some op | none => PlayerPreparation.program pc) = _
  rw [absent]

theorem preparation_ordinary (pc : Nat) (op : X86Routine.Op) (len : Nat)
    (h : PlayerPreparation.program pc = some (op,len)) : X86CodeMemory.routineOnly op = true := by
  have reaction := X86CodeMemory.routine_decode PlayerReactionProof.callerBytes (by decide)
  have movement := X86CodeMemory.routine_decode PlayerFunction.functionBytes (by decide)
  have setter := X86CodeMemory.routine_decode Doom19.setMobjStateBytes (by decide)
  have caller := X86CodeMemory.routine_decode PlayerHeight.Caller.callBytes (by decide)
  have height := X86CodeMemory.routine_decode PlayerHeight.code (by decide)
  have ordinaryHeight (k : Nat) : ((PlayerHeight.Shared.program k).map (fun p => X86CodeMemory.routineOnly p.1)).getD true = true := by
    unfold PlayerHeight.Shared.program PlayerHeight.Shared.bytesProgram
    split
    · exact caller 0
    · split
      · exact height _
      · rfl
  have ordinaryReaction (k : Nat) : ((PlayerReactionProof.program k).map (fun p => X86CodeMemory.routineOnly p.1)).getD true = true := by
    unfold PlayerReactionProof.program PlayerReactionProof.bytesProgram PlayerFunction.bytesProgram
    split
    · exact reaction _
    · split
      · exact movement _
      · split
        · exact setter _
        · rfl
  have ordinary (k : Nat) : ((PlayerPreparation.program k).map (fun p => X86CodeMemory.routineOnly p.1)).getD true = true := by
    change ((match PlayerHeight.Shared.program k with | some op => some op | none => PlayerReactionProof.program k).map _).getD true = true
    cases he : PlayerHeight.Shared.program k with
    | none => exact ordinaryReaction k
    | some instruction => simpa only [he] using ordinaryHeight k
  simpa only [h,Option.map_some,Option.getD_some] using ordinary pc

theorem locations (s t : X86Memory.State) (player : t.regs 0 = s.regs 0) (stack : t.regs 4 = s.regs 4)
    (keep : ∀ a, a ∈ SectorCaller.reads s → load32 t.memory a = load32 s.memory a) :
    SectorEntry.sector t = SectorEntry.sector s ∧ effectWrites t = effectWrites s := by
  have p : SectorEntry.player t = SectorEntry.player s := player
  have obj : SectorEntry.object t = SectorEntry.object s := by
    unfold SectorEntry.object; rw [p,keep _ (by simp [SectorCaller.reads])]
  have sub : SectorEntry.subsector t = SectorEntry.subsector s := by
    unfold SectorEntry.subsector; rw [obj,keep _ (by simp [SectorCaller.reads])]
  have sec : SectorEntry.sector t = SectorEntry.sector s := by
    unfold SectorEntry.sector; rw [sub,keep _ (by simp [SectorCaller.reads])]
  exact ⟨sec,by simp [effectWrites,SectorCaller.slots,p,sec,stack]⟩

/-- One run, from the reaction branch through preparation, sector lookup and
secret-handler return. All contracts refer to the original entry state. -/
theorem execution (s : X86Memory.State) (flags : Option Flags)
    (body : Motion) (anim : PlayerAnim.State) (cmd : Ticcmd) (timer : Int32)
    (v : ViewState) (time : Int32) (cached live : Bool) (floor : Fixed) (n : Int32)
    (h : Inputs s body anim cmd timer v time cached live floor n) :
    ∃ u, X86CodeMemory.run (SectorEntry.codeMemory SectorEntry.tableBytes) program [0x333e5] 256
      ⟨s,flags,0x333b1⟩ = some u ∧ u.pc = 0x333e5 ∧
      PreparedState.read (s.regs 2) (PlayerCaller.object s) u.core.memory =
        PreparedState.expected body anim cmd timer v time cached live ∧
      (load16 u.core.memory (SectorDispatch.sector s+(14#32)),load32 u.core.memory (s.regs 2+(212#32))) =
        (BitVec.ofNat 16 (LevelSpecials.secret 9 body.z floor n).1,(LevelSpecials.secret 9 body.z floor n).2.toBitVec) ∧
      u.core.regs 4 = s.regs 4 ∧ u.core.regs 2 = s.regs 2 := by
  obtain ⟨t,run,pc,_,_,sp,_,edx⟩ := PlayerPreparation.execution_preserved s flags body anim cmd timer v time cached live h.preparation
  obtain ⟨t',run',_,prepared,_,frame⟩ := PreparedState.execution s flags body anim cmd timer v time cached live h.preparation
  have same : t' = t := Option.some.inj (run'.symm.trans run)
  subst t'
  have keep (a : Word) (ha : a ∈ SectorCaller.reads (SectorCaller.argument s)) :
      load32 (SectorCaller.argument t.core).memory a = load32 (SectorCaller.argument s).memory a :=
    frame a (h.sectorReads a ha)
  have p : (SectorCaller.argument t.core).regs 0 = (SectorCaller.argument s).regs 0 := edx
  have stack : (SectorCaller.argument t.core).regs 4 = (SectorCaller.argument s).regs 4 := sp
  have ht := transport _ _ body.z floor n h.sector p stack keep
  obtain ⟨sec,writes⟩ := locations _ _ p stack keep
  have sec' : SectorDispatch.sector t.core = SectorDispatch.sector s := by
    simpa [SectorEntry.sector,SectorEntry.subsector,SectorEntry.object,SectorEntry.player,
      SectorDispatch.sector,SectorDispatch.subsector,SectorDispatch.object,SectorCaller.argument,put,write] using sec
  let u := SectorEntry.result (SectorCaller.enter (SectorCaller.argument t.core))
  have tail := SectorCaller.dispatched_execution t.core t.flags body.z floor n ht
  have obs := SectorCaller.dispatched_observation t.core t.flags body.z floor n ht
  rw [tail] at obs
  simp only [Option.map_some,Option.some.injEq,Prod.mk.injEq] at obs
  obtain ⟨ret,special,count,regs⟩ := obs
  have memory := handler_frame (SectorCaller.argument t.core) body.z floor n ht
  rw [writes] at memory
  have words : PreparedState.read (s.regs 2) (PlayerCaller.object s) u.core.memory =
      PreparedState.read (s.regs 2) (PlayerCaller.object s) t.core.memory :=
    prepared_read_frame s _ _ (fun a ha => memory a (h.preparedReads a ha))
  obtain ⟨k,bound,path,_⟩ := X86Routine.run_path run
  have first := (X86CodeMemory.lift_routine path (SectorEntry.codeMemory SectorEntry.tableBytes) preparation_ordinary).transfer
    program [0x333e5] contains_preparation (by
      intro addr hd; have hb := SectorDispatch.preparation_bound addr hd; simp only [List.mem_singleton]; omega)
  have actual : X86CodeMemory.run (SectorEntry.codeMemory SectorEntry.tableBytes) program [0x333e5] 31 t = some u := by
    have entry : t = ⟨t.core,t.flags,0x333d0⟩ := by rw [← pc]
    rw [entry,X86CodeMemory.run_sound _ program SectorCaller.program contains_caller _ _ _ (by rw [tail]; simp),tail]
  refine ⟨u,first.finish actual 256 (by omega),ret,words.trans prepared,?_,?_,?_⟩
  · rw [sec'] at special
    rw [edx] at count
    exact Prod.ext special count
  · exact (congrArg (fun r => r.2.2.2.1) regs).trans sp
  · exact (congrArg (fun r => r.2.1) regs).trans edx

def observe (s : X86Memory.State) (t : X86Control.State) :=
  (t.pc,PreparedState.read (s.regs 2) (PlayerCaller.object s) t.core.memory,
    load16 t.core.memory (SectorDispatch.sector s+(14#32)),load32 t.core.memory (s.regs 2+(212#32)),t.core.regs 4,t.core.regs 2)

theorem observation (s : X86Memory.State) (flags : Option Flags)
    (body : Motion) (anim : PlayerAnim.State) (cmd : Ticcmd) (timer : Int32)
    (v : ViewState) (time : Int32) (cached live : Bool) (floor : Fixed) (n : Int32)
    (h : Inputs s body anim cmd timer v time cached live floor n) :
    (X86CodeMemory.run (SectorEntry.codeMemory SectorEntry.tableBytes) program [0x333e5] 256
      ⟨s,flags,0x333b1⟩).map (observe s) =
      some (0x333e5,PreparedState.expected body anim cmd timer v time cached live,
        BitVec.ofNat 16 (LevelSpecials.secret 9 body.z floor n).1,(LevelSpecials.secret 9 body.z floor n).2.toBitVec,s.regs 4,s.regs 2) := by
  obtain ⟨t,run,pc,words,fields,sp,edx⟩ := execution s flags body anim cmd timer v time cached live floor n h
  rw [run]
  simp only [Prod.mk.injEq] at fields
  simp only [Option.map_some,observe,pc,words,fields.1,fields.2,sp,edx]

end Doom.Proofs.SectorJoined
