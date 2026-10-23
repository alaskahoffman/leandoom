import Doom.Proofs.OriginalKillDeathBranches
import Doom.DeathRuntime
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1Death
open Verification X86 X86Memory X86Control BlockSummary

/-- These are the runtime adapter's actual defaults, not a replacement model. -/
theorem runtime_profile (sim : Simulation) (map : sim.map.name="E1M1") :
    sim.deathWorld.netgame=false ∧ sim.deathWorld.console=0 ∧
    sim.deathWorld.automap=false ∧ sim.deathWorld.commercial=false ∧
    sim.deathWorld.source=none := by
  simp [Simulation.deathWorld,map]

theorem no_automap (sim : Simulation) : Death.shouldStopAutomap 0 sim.deathWorld=false := by
  simp [Death.shouldStopAutomap,Simulation.deathWorld]

def playerInfo : Death.Info := ⟨100,158,165,"pldeth",33557510⟩
theorem player_info : Death.info 0=some playerInfo := rfl

theorem player_states (health : Int32) :
    Death.deathState health playerInfo=158 ∨ Death.deathState health playerInfo=165 := by
  simp [Death.deathState,playerInfo]

/-- Fixed HMP/player-1 environmental lethal damage: no automap-callee contract
is required. The DOS inactive flag is still an explicit initial relation, not
an assumed whole-game invariant. -/

theorem floor_death_tracked (s : X86Memory.State) (f : Option Flags) (pc : Nat)
    (site : pc ∈ PlayerDamageEntry.sites) (v : PlayerDamage.State) (d : Int32)
    (sim : Simulation) (_map : sim.map.name="E1M1")
    (_skill : load32 s.memory (0x2b3e0#32)=2)
    (body : Death.Body) (info : body.info=playerInfo) (w : Fin 3) (y : Fixed)
    (h : KillDeathBranches.Inputs s v d false 0 body sim.deathWorld w y)
    (dead : (PlayerDamage.apply v d none false false sim.rng).killed=true)
    (stackSafe : Apart (0x12c5c#32) (s.regs 4-(56#32))) :
    ∃ t,
      DeathStack.Saved s pc t.core.memory (KillDeathBranches.stackWrites s 0) (KillDeathBranches.returnWrites s 0) ∧ X86Routine.run KillDeathBranches.program [0x30ea0] 239 ⟨s,f,pc⟩=some t ∧
      t.pc=0x30ea0 ∧ t.core.regs 0=s.regs 0 ∧
      t.core.regs 2=BitVec.ofNat 32 (Death.deathState (PlayerDamage.apply v d none false false sim.rng).state.health playerInfo) ∧
      (t.core.regs 2=158 ∨ t.core.regs 2=165) ∧
      load32 t.core.memory (0x12c5c#32)=0 ∧
      KillBookkeeping.joinedObservation s 0 t=KillBookkeeping.joinedLiveObservation
        (PlayerDamage.apply v d none false false sim.rng) 0 body sim.deathWorld ∧
      load32 t.core.memory (KillBookkeeping.player 0+244)=0x15a28+BitVec.ofNat 32 (Weapon.down w.val)*28 ∧
      load32 t.core.memory (KillBookkeeping.player 0+248)=1 ∧
      load32 t.core.memory (KillBookkeeping.player 0+256)=(Weapon.lowerHeight y true).raw.toBitVec ∧
      t.core.regs 3=s.regs 0 ∧ t.core.regs 4=s.regs 4-56 ∧
      load32 t.core.memory (s.regs 4-56)=0x2a3f1 ∧
      PlayerHeight.Frame s.memory t.core.memory (KillDeathBranches.priorWrites s 0 ++ [s.regs 4-56]) := by
  obtain ⟨t,tracked,run,obs,state,tics,height,pcOut,args,obj,sp,ret,frame⟩ :=
    KillDeathBranches.joined_execution_tracked s f pc site v d false sim.rng 0 body sim.deathWorld w y h dead
  have off := no_automap sim
  simp only [off,Bool.false_eq_true,↓reduceIte] at pcOut ret
  obtain ⟨a,b⟩ := args off
  rw [info] at b
  have states : t.core.regs 2=158 ∨ t.core.regs 2=165 := by
    rcases player_states (PlayerDamage.apply v d none false false sim.rng).state.health with normal|extreme
    · left; simpa [normal] using b
    · right; simpa [extreme] using b
  have inactive : load32 s.memory (0x12c5c#32)=0 := by
    have rel := h.automap
    simp [Simulation.deathWorld] at rel
    exact rel
  have keep : load32 t.core.memory (0x12c5c#32)=0 := by
    rw [frame _ (by
      intro q hq
      rcases List.mem_append.mp hq with prior|last
      · exact h.readsSafe _ (by simp [KillDeathBranches.reads]) q prior
      · simpa using (show Apart (0x12c5c#32) q from by simpa using (List.mem_singleton.mp last ▸ stackSafe)))]
    exact inactive
  obtain ⟨n,hn,path,_⟩ := X86Routine.run_path run
  have path := path.transfer KillDeathBranches.program [0x30ea0] (fun _ _ => rfl) (by
    intro pc hp; simp only [List.mem_singleton]; intro eq; subst pc; exact hp (by decide))

  refine ⟨t,tracked,path.finish (fuel := 0) (by simp [X86Routine.run,pcOut]) 239 (by omega),
    pcOut,a,b,states,keep,obs,state,tics,height,obj,sp,ret,frame⟩

theorem floor_death (s : X86Memory.State) (f : Option Flags) (pc : Nat)
    (site : pc ∈ PlayerDamageEntry.sites) (v : PlayerDamage.State) (d : Int32)
    (sim : Simulation) (_map : sim.map.name="E1M1")
    (_skill : load32 s.memory (0x2b3e0#32)=2)
    (body : Death.Body) (info : body.info=playerInfo) (w : Fin 3) (y : Fixed)
    (h : KillDeathBranches.Inputs s v d false 0 body sim.deathWorld w y)
    (dead : (PlayerDamage.apply v d none false false sim.rng).killed=true)
    (stackSafe : Apart (0x12c5c#32) (s.regs 4-(56#32))) :
    ∃ t, X86Routine.run KillDeathBranches.program [0x30ea0] 239 ⟨s,f,pc⟩=some t ∧
      t.pc=0x30ea0 ∧ t.core.regs 0=s.regs 0 ∧
      t.core.regs 2=BitVec.ofNat 32 (Death.deathState (PlayerDamage.apply v d none false false sim.rng).state.health playerInfo) ∧
      (t.core.regs 2=158 ∨ t.core.regs 2=165) ∧
      load32 t.core.memory (0x12c5c#32)=0 ∧
      KillBookkeeping.joinedObservation s 0 t=KillBookkeeping.joinedLiveObservation
        (PlayerDamage.apply v d none false false sim.rng) 0 body sim.deathWorld ∧
      load32 t.core.memory (KillBookkeeping.player 0+244)=0x15a28+BitVec.ofNat 32 (Weapon.down w.val)*28 ∧
      load32 t.core.memory (KillBookkeeping.player 0+248)=1 ∧
      load32 t.core.memory (KillBookkeeping.player 0+256)=(Weapon.lowerHeight y true).raw.toBitVec ∧
      t.core.regs 3=s.regs 0 ∧ t.core.regs 4=s.regs 4-56 ∧
      load32 t.core.memory (s.regs 4-56)=0x2a3f1 ∧
      PlayerHeight.Frame s.memory t.core.memory (KillDeathBranches.priorWrites s 0 ++ [s.regs 4-56]) := by
  obtain ⟨t,_,rest⟩ :=
    floor_death_tracked s f pc site v d sim _map _skill body info w y h dead stackSafe
  exact ⟨t,rest⟩

end Doom.Proofs.E1M1Death
