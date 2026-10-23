import Doom.Proofs.OriginalDeathTiming
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1DeathTiming
open Verification X86 X86Memory X86Control BlockSummary
open FloorDamage (nextIndex randomByte)

def program (pc : Nat) : Option (X86Routine.Op × Nat) :=
  match E1M1DeathSetter.program pc with
  | some op => some op
  | none => DeathTiming.program pc

theorem contains_previous (pc : Nat) (h : E1M1DeathSetter.program pc≠none) :
    program pc=E1M1DeathSetter.program pc := by
  unfold program
  cases eq : E1M1DeathSetter.program pc with
  | none => exact False.elim (h eq)
  | some op => rfl

theorem contains_timing (pc : Nat) (h : DeathTiming.program pc≠none) :
    program pc=DeathTiming.program pc := by
  have bound : (0x2a3f1 ≤ pc ∧ pc < 0x2a40d) ∨ (0x24160 ≤ pc ∧ pc < 0x2417c) := by
    by_cases yes : (0x2a3f1 ≤ pc ∧ pc < 0x2a40d) ∨ (0x24160 ≤ pc ∧ pc < 0x2417c)
    · exact yes
    · have h1 : ¬(0x2a3f1 ≤ pc ∧ pc < 0x2a40d) := by omega
      have h2 : ¬(0x24160 ≤ pc ∧ pc < 0x2417c) := by omega
      simp [DeathTiming.program,DeathTiming.bytesProgram,h1,h2] at h
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
  have b12 : ¬(0x2a38c ≤ pc ∧ pc < 0x2a3c8) := by omega
  have b13 : ¬(0x2a3c8 ≤ pc ∧ pc < 0x2a3f1) := by omega
  have b14 : ¬(0x30ea0 ≤ pc ∧ pc < 0x30efb) := by omega
  simp [program,E1M1DeathSetter.program,DeathSetter.program,PainSetter.program,PainSetter.bytesProgram,b14,KillDeathBranches.program,KillDeathBranches.bytesProgram,
    KillWeaponDrop.program,KillBookkeeping.joined,KillEntry.joined,
    ActorHealth.joined,PlayerHealth.joined,PlayerDamageEntry.program,PlayerDamageEntry.bytesProgram,
    WeaponDrop.program,WeaponDrop.bytesProgram,WeaponLower.bytesProgram,
    DeathBranches.bytesProgram,DeathAutomap.bytesProgram,DeathChoice.bytesProgram,
    b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,
    show pc ≠ 0x2fb76 by omega,show pc ≠ 0x2fba0 by omega,show pc ≠ 0x2fbd2 by omega]


def previousWrites (s : X86Memory.State) := E1M1DeathSetter.previousWrites s ++ E1M1DeathSetter.suffixWrites s
def timingWrites (s : X86Memory.State) : List Word := [s.regs 4-56,0x12720,s.regs 0+96]
def retained (s : X86Memory.State) := KillDeathBranches.retained s 0 ++
  [0x12c5c,0x1271c,s.regs 0+100,s.regs 0+36,s.regs 0+40]
structure Inputs (s : X86Memory.State) (rng : DoomRandom) : Prop where
  previous : E1M1DeathSetter.Inputs s
  index : load32 s.memory (0x12720#32)=BitVec.ofNat 32 rng.play.toNat
  misc : load32 s.memory (0x1271c#32)=BitVec.ofNat 32 rng.misc.toNat
  table : s.memory ((0x1261c#32)+nextIndex rng.play)=randomByte rng.play
  readsPreviousSafe : ∀ a, a ∈ [(0x12720#32),0x1271c,(0x1261c#32)+nextIndex rng.play] →
    ∀ b, b ∈ previousWrites s → Apart a b
  indexStackSafe : Apart (0x12720#32) (s.regs 4-56)
  tableTimingSafe : Apart ((0x1261c#32)+nextIndex rng.play) (s.regs 4-56) ∧
    Apart ((0x1261c#32)+nextIndex rng.play) (0x12720#32)
  ticsTimingSafe : Apart (s.regs 0+96) (s.regs 4-56) ∧ Apart (s.regs 0+96) (0x12720#32)
  retainedTimingSafe : ∀ a, a ∈ retained s → ∀ b, b ∈ timingWrites s → Apart a b

def stackWrites (s : X86Memory.State) := E1M1DeathSetter.stackWrites s ++ timingWrites s
def returnWrites (s : X86Memory.State) := E1M1DeathSetter.returnWrites s ++ timingWrites s

theorem joined_execution_tracked (s : X86Memory.State) (f : Option Flags) (pc : Nat)
    (site : pc ∈ PlayerDamageEntry.sites) (v : PlayerDamage.State) (d : Int32)
    (sim : Simulation) (map : sim.map.name="E1M1") (skill : load32 s.memory (0x2b3e0#32)=2)
    (body : Death.Body) (info : body.info=E1M1Death.playerInfo) (w : Fin 3) (y : Fixed)
    (h : KillDeathBranches.Inputs s v d false 0 body sim.deathWorld w y)
    (dead : (PlayerDamage.apply v d none false false sim.rng).killed=true)
    (stackSafe : Apart (0x12c5c#32) (s.regs 4-(56#32))) (ins : Inputs s sim.rng) :
    ∃ (extreme : Bool) (t : X86Control.State),
      DeathStack.Saved s pc t.core.memory (stackWrites s) (returnWrites s) ∧
      E1M1DeathSetter.stateId extreme=Death.deathState
        (PlayerDamage.apply v d none false false sim.rng).state.health E1M1Death.playerInfo ∧
      X86Routine.run program [0x2a40d] 278 ⟨s,f,pc⟩=some t ∧
      t.pc=0x2a40d ∧ t.core.regs 3=s.regs 0 ∧ t.core.regs 4=s.regs 4-52 ∧
      DeathSetter.observeFields t.core.memory (s.regs 0)=
        ((E1M1DeathSetter.entry extreme).pointer,DeathTiming.playerTicks extreme sim.rng.play,
         (E1M1DeathSetter.entry extreme).sprite,(E1M1DeathSetter.entry extreme).frame) ∧
      load32 t.core.memory (0x12720#32)=nextIndex sim.rng.play ∧
      load32 t.core.memory (0x1271c#32)=BitVec.ofNat 32 sim.rng.misc.toNat ∧
      load32 t.core.memory (0x12c5c#32)=0 ∧
      KillBookkeeping.joinedObservation s 0 t=KillBookkeeping.joinedLiveObservation
        (PlayerDamage.apply v d none false false sim.rng) 0 body sim.deathWorld ∧
      load32 t.core.memory (KillBookkeeping.player 0+244)=0x15a28+BitVec.ofNat 32 (Weapon.down w.val)*28 ∧
      load32 t.core.memory (KillBookkeeping.player 0+248)=1 ∧
      load32 t.core.memory (KillBookkeeping.player 0+256)=(Weapon.lowerHeight y true).raw.toBitVec ∧
      PlayerHeight.Frame s.memory t.core.memory (previousWrites s ++ timingWrites s) := by
  obtain ⟨extreme,g,gsaved,choice,grun,gpc,_,obj,sp,fields,off,obs,weapon,tics,height,frame⟩ :=
    E1M1DeathSetter.joined_execution_tracked s f pc site v d sim map skill body info w y h dead stackSafe ins.previous
  have slots : DeathTiming.writes g.core=timingWrites s := by
    simp [DeathTiming.writes,timingWrites,obj,sp,BitVec.sub_sub]
  have keep (a : Word) (ha : a ∈ [(0x12720#32),0x1271c,(0x1261c#32)+nextIndex sim.rng.play]) :
      load32 g.core.memory a=load32 s.memory a := frame a (ins.readsPreviousSafe a ha)
  have input : DeathTiming.Inputs g.core sim.rng.play := by
    refine ⟨?_,?_,?_,?_,?_⟩
    · rw [keep _ (by simp),ins.index]
    · exact ((frame.byte _ (ins.readsPreviousSafe _ (by simp))).trans ins.table)
    · simpa [sp,BitVec.sub_sub] using ins.indexStackSafe
    · simpa [sp,BitVec.sub_sub] using ins.tableTimingSafe
    · simpa [obj,sp,BitVec.sub_sub] using ins.ticsTimingSafe
  have ticInput : load32 g.core.memory (g.core.regs 3+96)=(E1M1DeathSetter.entry extreme).tics := by
    simpa [DeathSetter.observeFields,obj] using congrArg (fun f => f.2.1) fields
  let t := DeathTiming.result g.core sim.rng.play
  have trun := DeathTiming.original_execution g.core g.flags sim.rng.play input
  rw [← gpc] at trun
  obtain ⟨n,hn,path,_⟩ := X86Routine.run_path grun
  have path := path.transfer program [0x2a40d] contains_previous (by
    intro pc hp; simp only [List.mem_singleton]; intro eq; subst pc; exact hp (by decide))
  obtain ⟨k,hk,tail,_⟩ := X86Routine.run_path trun
  have tail := tail.transfer program [0x2a40d] contains_timing (by
    intro pc hp; simp only [List.mem_singleton]; intro eq; subst pc; exact hp (by decide))
  have rest : X86Routine.run program [0x2a40d] 15 g=some t :=
    tail.finish (fuel := 0) (by simp [X86Routine.run,t,DeathTiming.result,DeathTiming.tailEnd]) 15 (by omega)
  have preserve (a : Word) (ha : a ∈ retained s) : load32 t.core.memory a=load32 g.core.memory a := by
    apply DeathTiming.memory_frame
    intro b hb; rw [slots] at hb; exact ins.retainedTimingSafe a ha b hb
  have obsKeep : KillBookkeeping.joinedObservation s 0 t=KillBookkeeping.joinedObservation s 0 g := by
    simp only [KillBookkeeping.joinedObservation,KillEntry.damageFields,KillBookkeeping.observation]
    repeat rw [preserve _ (by simp [retained,KillDeathBranches.retained,KillWeaponDrop.retained,
      KillBookkeeping.retained,KillEntry.retained,ActorHealth.fields])]
  have ticks := DeathTiming.player_tics g.core sim.rng.play input extreme ticInput
  rw [obj] at ticks
  have tracked : DeathStack.Saved s pc t.core.memory (stackWrites s) (returnWrites s) := by
    have fr := DeathTiming.memory_frame g.core sim.rng.play
    rw [slots] at fr
    exact gsaved.then_frame _ _ _ _ _ _ _ fr
  refine ⟨extreme,t,tracked,choice,path.finish rest 278 (by omega),rfl,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa [t,DeathTiming.result,DeathTiming.tailEnd,DeathTiming.rolled_regs,write] using obj
  · simp [t,DeathTiming.result,DeathTiming.tailEnd,DeathTiming.rolled_regs,write,sp]
  · simp only [DeathSetter.observeFields] at fields ⊢
    have tickWord : load32 t.core.memory (s.regs 0+(96#32))=DeathTiming.playerTicks extreme sim.rng.play := by
      simpa [t] using ticks
    rw [preserve (s.regs 0+(100#32)) (by simp [retained]),
      preserve (s.regs 0+(36#32)) (by simp [retained]),
      preserve (s.regs 0+(40#32)) (by simp [retained]),tickWord]
    exact Prod.ext (congrArg (fun f => f.1) fields) (Prod.ext rfl (congrArg (fun f => f.2.2) fields))
  · exact DeathTiming.result_index g.core sim.rng.play input
  · rw [preserve _ (by simp [retained]),keep _ (by simp),ins.misc]
  · rw [preserve _ (by simp [retained]),off]
  · exact obsKeep.trans obs
  · rw [preserve _ (by simp [retained,KillDeathBranches.retained]),weapon]
  · rw [preserve _ (by simp [retained,KillDeathBranches.retained]),tics]
  · rw [preserve _ (by simp [retained,KillDeathBranches.retained]),height]
  · intro a safe
    rw [DeathTiming.memory_frame g.core sim.rng.play a]
    · exact frame a (fun b hb => safe b (List.mem_append_left _ hb))
    · intro b hb; rw [slots] at hb; exact safe b (List.mem_append_right _ hb)

theorem joined_execution (s : X86Memory.State) (f : Option Flags) (pc : Nat)
    (site : pc ∈ PlayerDamageEntry.sites) (v : PlayerDamage.State) (d : Int32)
    (sim : Simulation) (map : sim.map.name="E1M1") (skill : load32 s.memory (0x2b3e0#32)=2)
    (body : Death.Body) (info : body.info=E1M1Death.playerInfo) (w : Fin 3) (y : Fixed)
    (h : KillDeathBranches.Inputs s v d false 0 body sim.deathWorld w y)
    (dead : (PlayerDamage.apply v d none false false sim.rng).killed=true)
    (stackSafe : Apart (0x12c5c#32) (s.regs 4-(56#32))) (ins : Inputs s sim.rng) :
    ∃ (extreme : Bool) (t : X86Control.State),
      E1M1DeathSetter.stateId extreme=Death.deathState
        (PlayerDamage.apply v d none false false sim.rng).state.health E1M1Death.playerInfo ∧
      X86Routine.run program [0x2a40d] 278 ⟨s,f,pc⟩=some t ∧
      t.pc=0x2a40d ∧ t.core.regs 3=s.regs 0 ∧ t.core.regs 4=s.regs 4-52 ∧
      DeathSetter.observeFields t.core.memory (s.regs 0)=
        ((E1M1DeathSetter.entry extreme).pointer,DeathTiming.playerTicks extreme sim.rng.play,
         (E1M1DeathSetter.entry extreme).sprite,(E1M1DeathSetter.entry extreme).frame) ∧
      load32 t.core.memory (0x12720#32)=nextIndex sim.rng.play ∧
      load32 t.core.memory (0x1271c#32)=BitVec.ofNat 32 sim.rng.misc.toNat ∧
      load32 t.core.memory (0x12c5c#32)=0 ∧
      KillBookkeeping.joinedObservation s 0 t=KillBookkeeping.joinedLiveObservation
        (PlayerDamage.apply v d none false false sim.rng) 0 body sim.deathWorld ∧
      load32 t.core.memory (KillBookkeeping.player 0+244)=0x15a28+BitVec.ofNat 32 (Weapon.down w.val)*28 ∧
      load32 t.core.memory (KillBookkeeping.player 0+248)=1 ∧
      load32 t.core.memory (KillBookkeeping.player 0+256)=(Weapon.lowerHeight y true).raw.toBitVec ∧
      PlayerHeight.Frame s.memory t.core.memory (previousWrites s ++ timingWrites s) := by
  obtain ⟨extreme,t,_,rest⟩ :=
    joined_execution_tracked s f pc site v d sim map skill body info w y h dead stackSafe ins
  exact ⟨extreme,t,rest⟩

end Doom.Proofs.E1M1DeathTiming
