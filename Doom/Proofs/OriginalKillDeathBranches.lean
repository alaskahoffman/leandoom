import Doom.Proofs.OriginalKillWeaponDrop
import Doom.Proofs.OriginalDeathBranches
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.KillDeathBranches
open Verification X86 X86Memory X86Control BlockSummary

def bytesProgram (guard choice : List UInt8) : X86Routine.Program := fun pc =>
  match KillWeaponDrop.program pc with
  | some op => some op
  | none => DeathBranches.bytesProgram guard choice pc
def program := bytesProgram DeathAutomap.code DeathChoice.code

theorem contains_previous (pc : Nat) (h : KillWeaponDrop.program pc≠none) :
    program pc=KillWeaponDrop.program pc := by
  unfold program bytesProgram
  cases eq : KillWeaponDrop.program pc with
  | none => exact False.elim (h eq)
  | some op => rfl

theorem contains_branches (pc : Nat) (h : DeathBranches.program pc≠none) :
    program pc=DeathBranches.program pc := by
  have bound : 0x2a38c ≤ pc ∧ pc < 0x2a3f1 := by
    by_cases yes : 0x2a38c ≤ pc ∧ pc < 0x2a3f1
    · exact yes
    · have a : ¬(0x2a38c ≤ pc ∧ pc < 0x2a3c8) := by omega
      have b : ¬(0x2a3c8 ≤ pc ∧ pc < 0x2a3f1) := by omega
      simp [DeathBranches.program,DeathBranches.bytesProgram,DeathAutomap.bytesProgram,DeathChoice.bytesProgram,a,b] at h
  have b0 : ¬(0x2a2e6 ≤ pc ∧ pc < 0x2a38c) := by omega
  have b1 : ¬(0x2a6a6 ≤ pc ∧ pc < 0x2a6b1) := by omega
  have b2 : ¬(0x2a2b0 ≤ pc ∧ pc < 0x2a2e6) := by omega
  have b3 : ¬(0x2a650 ≤ pc ∧ pc < 0x2a6a6) := by omega
  have b4 : ¬(0x1bb50 ≤ pc ∧ pc < 0x1bb66) := by omega
  have b5 : ¬(0x1bc41 ≤ pc ∧ pc < 0x1bc45) := by omega
  have b6 : ¬(0x2a616 ≤ pc ∧ pc < 0x2a650) := by omega
  have b7 : ¬(0x2a460 ≤ pc ∧ pc < 0x2a5d5) := by omega
  have b8 : ¬(0x2a5d5 ≤ pc ∧ pc < 0x2a616) := by omega
  have b9 : ¬(0x2d2c0 ≤ pc ∧ pc < 0x2d2e3) := by omega
  have b10 : ¬(0x2d040 ≤ pc ∧ pc < 0x2d0af) := by omega
  have b11 : ¬(0x2d490 ≤ pc ∧ pc < 0x2d4cc) := by omega
  simp [program,bytesProgram,KillWeaponDrop.program,KillBookkeeping.joined,KillEntry.joined,
    ActorHealth.joined,PlayerHealth.joined,PlayerDamageEntry.program,PlayerDamageEntry.bytesProgram,
    WeaponDrop.program,WeaponDrop.bytesProgram,WeaponLower.bytesProgram,
    b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,
    show pc ≠ 0x2fb76 by omega,show pc ≠ 0x2fba0 by omega,show pc ≠ 0x2fbd2 by omega,
    DeathBranches.program]

theorem previous_active (pc : Nat) (h : KillWeaponDrop.program pc≠none) : pc ∉ [0x24f90,0x30ea0] := by
  simp only [List.mem_cons,List.not_mem_nil,or_false]; intro eq
  rcases eq with rfl|rfl <;> exact h (by decide)
theorem branches_active (pc : Nat) (h : DeathBranches.program pc≠none) : pc ∉ [0x24f90,0x30ea0] := by
  simp only [List.mem_cons,List.not_mem_nil,or_false]; intro eq
  rcases eq with rfl|rfl <;> exact h (by decide)

/-- All new read locations are described in the original damage-entry memory. -/
def infoPointer (s : X86Memory.State) := load32 s.memory (s.regs 0+92)
def reads (s : X86Memory.State) :=
  [0x2b3dc,0x12c5c,s.regs 0+132,s.regs 0+92,infoPointer s+8,infoPointer s+48,infoPointer s+52]
def priorWrites (s : X86Memory.State) (i : Fin 4) :=
  KillWeaponDrop.priorWrites s i ++ WeaponDrop.writes (KillWeaponDrop.dropView s i)
def retained (s : X86Memory.State) (i : Fin 4) :=
  KillWeaponDrop.retained s i ++ [KillBookkeeping.player i+244,KillBookkeeping.player i+248,KillBookkeeping.player i+256]

structure Inputs (s : X86Memory.State) (v : PlayerDamage.State) (d : Int32) (baby : Bool)
    (i : Fin 4) (body : Death.Body) (world : Death.World) (w : Fin 3) (y : Fixed) : Prop where
  prior : KillWeaponDrop.Inputs s v d baby i body world w y
  console : load32 s.memory (0x2b3dc#32)=BitVec.ofNat 32 world.console.val
  automap : (load32 s.memory (0x12c5c#32)≠0) ↔ world.automap=true
  spawn : load32 s.memory (infoPointer s+8)=body.info.spawnHealth.toBitVec
  normal : load32 s.memory (infoPointer s+48)=BitVec.ofNat 32 body.info.normal
  extreme : load32 s.memory (infoPointer s+52)=BitVec.ofNat 32 body.info.extreme
  extremeBound : body.info.extreme < 4294967296
  readsSafe : ∀ a, a ∈ reads s → ∀ b, b ∈ priorWrites s i → Apart a b
  retainedSafe : ∀ a, a ∈ retained s i → Apart a (s.regs 4-56)

/-- Continuous original execution from a floor damage CALL. Post-damage health
and every new branch input are derived; no intermediate-state contract is assumed. -/
def stackWrites (s : X86Memory.State) (i : Fin 4) := KillWeaponDrop.stackWrites s i ++ [s.regs 4-56]
def returnWrites (s : X86Memory.State) (i : Fin 4) := KillWeaponDrop.returnWrites s i ++ [s.regs 4-56]

theorem joined_execution_tracked (s : X86Memory.State) (f : Option Flags) (pc : Nat)
    (site : pc ∈ PlayerDamageEntry.sites) (v : PlayerDamage.State) (d : Int32) (baby : Bool)
    (rng : DoomRandom) (i : Fin 4) (body : Death.Body) (world : Death.World) (w : Fin 3) (y : Fixed)
    (h : Inputs s v d baby i body world w y)
    (dead : (PlayerDamage.apply v d none false baby rng).killed=true) :
    ∃ t,
      DeathStack.Saved s pc t.core.memory (stackWrites s i) (returnWrites s i) ∧ X86Routine.run program [0x24f90,0x30ea0] 239 ⟨s,f,pc⟩=some t ∧
      KillBookkeeping.joinedObservation s i t=KillBookkeeping.joinedLiveObservation
        (PlayerDamage.apply v d none false baby rng) i body world ∧
      load32 t.core.memory (KillBookkeeping.player i+244)=0x15a28+BitVec.ofNat 32 (Weapon.down w.val)*28 ∧
      load32 t.core.memory (KillBookkeeping.player i+248)=1 ∧
      load32 t.core.memory (KillBookkeeping.player i+256)=(Weapon.lowerHeight y true).raw.toBitVec ∧
      t.pc=(if Death.shouldStopAutomap i world then 0x24f90 else 0x30ea0) ∧
      (Death.shouldStopAutomap i world=false → t.core.regs 0=s.regs 0 ∧
        t.core.regs 2=BitVec.ofNat 32 (Death.deathState (PlayerDamage.apply v d none false baby rng).state.health body.info)) ∧
      t.core.regs 3=s.regs 0 ∧ t.core.regs 4=s.regs 4-56 ∧
      load32 t.core.memory (s.regs 4-56)=(if Death.shouldStopAutomap i world then 0x2a3c8 else 0x2a3f1) ∧
      PlayerHeight.Frame s.memory t.core.memory (priorWrites s i ++ [s.regs 4-56]) := by
  obtain ⟨g,gsaved,grun,gobs,gstate,gtics,gy,gpc,gsp,gobj,gframe⟩ :=
    KillWeaponDrop.joined_execution_detailed_tracked s f pc site v d baby rng i body world w y h.prior dead
  have keep (a : Word) (ha : a ∈ reads s) : load32 g.core.memory a=load32 s.memory a :=
    gframe a (h.readsSafe a ha)
  have ptr : DeathChoice.infoPointer g.core=infoPointer s := by
    change load32 g.core.memory (g.core.regs 3+(92#32))=load32 s.memory (s.regs 0+(92#32))
    rw [gobj,keep _ (by simp [reads])]
  have hp : DeathChoice.health g.core=(PlayerDamage.apply v d none false baby rng).state.health.toBitVec := by
    have eq := congrArg (fun x => x.1.2) gobs
    simpa [KillBookkeeping.joinedObservation,KillBookkeeping.joinedLiveObservation,
      KillEntry.damageFields,KillEntry.liveDamageFields,DeathChoice.health,gobj] using eq
  have ins : DeathChoice.Inputs g.core (PlayerDamage.apply v d none false baby rng).state.health body.info := by
    refine ⟨hp,?_,?_,?_,h.extremeBound⟩
    · unfold DeathChoice.spawn; rw [ptr,keep _ (by simp [reads])]; exact h.spawn
    · unfold DeathChoice.normal; rw [ptr,keep _ (by simp [reads])]; exact h.normal
    · unfold DeathChoice.extreme; rw [ptr,keep _ (by simp [reads])]; exact h.extreme
  have console : load32 g.core.memory (0x2b3dc#32)=BitVec.ofNat 32 world.console.val :=
    (keep _ (by simp [reads])).trans h.console
  have auto : (DeathAutomap.active g.core≠0) ↔ world.automap=true := by
    unfold DeathAutomap.active; rw [keep _ (by simp [reads])]; exact h.automap
  have victim : load32 g.core.memory (g.core.regs 3+(132#32))=DeathAutomap.player i := by
    rw [gobj,keep _ (by simp [reads])]
    exact h.prior.prior.book.ptr
  obtain ⟨t,trun,tpc,tchoice,tobj,tsp,tret,tframe⟩ :=
    DeathBranches.execution g.core g.flags i world (PlayerDamage.apply v d none false baby rng).state.health body.info console victim auto ins
  have slot : g.core.regs 4-(4#32)=s.regs 4-(56#32) := by rw [gsp]; simp [BitVec.sub_sub]
  have stable (a : Word) (ha : a ∈ retained s i) : load32 t.core.memory a=load32 g.core.memory a := by
    apply tframe
    intro b hb
    simp only [List.mem_singleton] at hb; subst b
    change Apart a (g.core.regs 4-(4#32))
    rw [slot]; exact h.retainedSafe a ha
  have obs : KillBookkeeping.joinedObservation s i t=KillBookkeeping.joinedObservation s i g := by
    unfold KillBookkeeping.joinedObservation KillEntry.damageFields KillBookkeeping.observation
    dsimp only
    repeat rw [stable _ (by simp [retained,KillWeaponDrop.retained,KillBookkeeping.retained,KillEntry.retained,ActorHealth.fields])]
  obtain ⟨n,hn,first,_⟩ := X86Routine.run_path grun
  have first := first.transfer program [0x24f90,0x30ea0] contains_previous previous_active
  obtain ⟨k,hk,tail,_⟩ := X86Routine.run_path trun
  have tail := tail.transfer program [0x24f90,0x30ea0] contains_branches branches_active
  have tailRun : X86Routine.run program [0x24f90,0x30ea0] 26 g=some t := by
    have geq : g=⟨g.core,g.flags,0x2a38c⟩ := by rw [← gpc]
    rw [geq]
    apply tail.finish (fuel := 0) ?_ 26 (by omega)
    cases eq : Death.shouldStopAutomap i world <;> simp [X86Routine.run,tpc,eq]
  have tracked : DeathStack.Saved s pc t.core.memory (stackWrites s i) (returnWrites s i) := by
    have fr : PlayerHeight.Frame g.core.memory t.core.memory [s.regs 4-56] := by simpa [slot] using tframe
    exact gsaved.then_frame _ _ _ _ _ _ _ fr
  refine ⟨t,tracked,first.finish tailRun 239 (by omega),obs.trans gobs,?_,?_,?_,tpc,?_,tobj.trans gobj,?_,?_,?_⟩
  · rw [stable _ (by simp [retained]),gstate]
  · rw [stable _ (by simp [retained]),gtics]
  · rw [stable _ (by simp [retained]),gy]
  · intro off; obtain ⟨obj,state⟩ := tchoice off; exact ⟨obj.trans gobj,state⟩
  · exact tsp.trans slot
  · simpa [slot] using tret
  · intro a safe
    rw [tframe a (fun b hb => safe b (List.mem_append.mpr (Or.inr (by simpa [slot] using hb))))]
    exact gframe a (fun b hb => safe b (List.mem_append.mpr (Or.inl hb)))

theorem joined_execution (s : X86Memory.State) (f : Option Flags) (pc : Nat)
    (site : pc ∈ PlayerDamageEntry.sites) (v : PlayerDamage.State) (d : Int32) (baby : Bool)
    (rng : DoomRandom) (i : Fin 4) (body : Death.Body) (world : Death.World) (w : Fin 3) (y : Fixed)
    (h : Inputs s v d baby i body world w y)
    (dead : (PlayerDamage.apply v d none false baby rng).killed=true) :
    ∃ t, X86Routine.run program [0x24f90,0x30ea0] 239 ⟨s,f,pc⟩=some t ∧
      KillBookkeeping.joinedObservation s i t=KillBookkeeping.joinedLiveObservation
        (PlayerDamage.apply v d none false baby rng) i body world ∧
      load32 t.core.memory (KillBookkeeping.player i+244)=0x15a28+BitVec.ofNat 32 (Weapon.down w.val)*28 ∧
      load32 t.core.memory (KillBookkeeping.player i+248)=1 ∧
      load32 t.core.memory (KillBookkeeping.player i+256)=(Weapon.lowerHeight y true).raw.toBitVec ∧
      t.pc=(if Death.shouldStopAutomap i world then 0x24f90 else 0x30ea0) ∧
      (Death.shouldStopAutomap i world=false → t.core.regs 0=s.regs 0 ∧
        t.core.regs 2=BitVec.ofNat 32 (Death.deathState (PlayerDamage.apply v d none false baby rng).state.health body.info)) ∧
      t.core.regs 3=s.regs 0 ∧ t.core.regs 4=s.regs 4-56 ∧
      load32 t.core.memory (s.regs 4-56)=(if Death.shouldStopAutomap i world then 0x2a3c8 else 0x2a3f1) ∧
      PlayerHeight.Frame s.memory t.core.memory (priorWrites s i ++ [s.regs 4-56]) := by
  obtain ⟨t,_,rest⟩ :=
    joined_execution_tracked s f pc site v d baby rng i body world w y h dead
  exact ⟨t,rest⟩

end Doom.Proofs.KillDeathBranches
