theorem joined_checked (s : X86Memory.State) (f : Option Flags) (pc : Nat)
    (site : pc ∈ PlayerDamageEntry.sites) (v : PlayerDamage.State) (d : Int32)
    (sim : Simulation) (map : sim.map.name="E1M1") (skill : load32 s.memory (0x2b3e0#32)=2)
    (body : Death.Body) (info : body.info=E1M1Death.playerInfo) (w : Fin 3) (y : Fixed)
    (h : KillDeathBranches.Inputs s v d false 0 body sim.deathWorld w y)
    (dead : (PlayerDamage.apply v d none false false sim.rng).killed=true)
    (stackSafe : Apart (0x12c5c#32) (s.regs 4-(56#32)))
    (timing : E1M1DeathTiming.Inputs s sim.rng) (ins : E1M1FloorReturn.Inputs s) :
    ∃ (extreme : Bool) (k t : X86Control.State),
      E1M1DeathSetter.stateId extreme=Death.deathState
        (PlayerDamage.apply v d none false false sim.rng).state.health E1M1Death.playerInfo ∧
      X86Routine.run E1M1FloorReturn.program [0x2a6b1] 289 ⟨s,f,pc⟩=some k ∧
      k.pc=0x2a6b1 ∧ k.core.regs 4=s.regs 4-28 ∧
      X86Routine.run E1M1FloorReturn.program [pc+5] 295 ⟨s,f,pc⟩=some t ∧
      t.pc=pc+5 ∧ t.core.regs 4=s.regs 4 ∧
      t.core.regs 5=s.regs 5 ∧ t.core.regs 7=s.regs 7 ∧ t.core.regs 6=s.regs 6 ∧
      t.core.memory=k.core.memory ∧
      DeathSetter.observeFields t.core.memory (s.regs 0)=
        ((E1M1DeathSetter.entry extreme).pointer,DeathTiming.playerTicks extreme sim.rng.play,
         (E1M1DeathSetter.entry extreme).sprite,(E1M1DeathSetter.entry extreme).frame) ∧
      load32 t.core.memory (0x12720#32)=FloorDamage.nextIndex sim.rng.play ∧
      load32 t.core.memory (0x1271c#32)=BitVec.ofNat 32 sim.rng.misc.toNat ∧
      load32 t.core.memory (0x12c5c#32)=0 ∧
      KillBookkeeping.joinedObservation s 0 t=KillBookkeeping.joinedLiveObservation
        (PlayerDamage.apply v d none false false sim.rng) 0 body sim.deathWorld ∧
      load32 t.core.memory (KillBookkeeping.player 0+244)=0x15a28+BitVec.ofNat 32 (Weapon.down w.val)*28 ∧
      load32 t.core.memory (KillBookkeeping.player 0+248)=1 ∧
      load32 t.core.memory (KillBookkeeping.player 0+256)=(Weapon.lowerHeight y true).raw.toBitVec ∧
      PlayerHeight.Frame s.memory t.core.memory (E1M1FloorReturn.allWrites s) :=
  E1M1FloorReturn.joined_execution s f pc site v d sim map skill body info w y h dead stackSafe timing ins
