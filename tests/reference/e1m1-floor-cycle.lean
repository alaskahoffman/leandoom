theorem joined_checked (kind : FloorDamage.Kind) (s : X86Memory.State) (f : Option Flags)
    (z floor : Fixed) (time : Nat) (suit : Bool) (sim : Simulation)
    (map : sim.map.name="E1M1") (floorInputs : FloorCaller.Inputs kind s z floor time suit sim.rng)
    (nonzero : FloorDamage.requested (E1M1FloorCycle.boundary kind s sim.rng) ≠ 0) (v : PlayerDamage.State) (d : Int32)
    (skill : load32 (E1M1FloorCycle.boundary kind s sim.rng).core.memory (0x2b3e0#32)=2)
    (body : Death.Body) (info : body.info=E1M1Death.playerInfo) (w : Fin 3) (y : Fixed)
    (h : KillDeathBranches.Inputs (E1M1FloorCycle.boundary kind s sim.rng).core v d false 0 body (E1M1FloorCycle.afterFloor kind z floor time suit sim).deathWorld w y)
    (dead : (PlayerDamage.apply v d none false false (E1M1FloorCycle.afterFloor kind z floor time suit sim).rng).killed=true)
    (stackSafe : Apart (0x12c5c#32) ((E1M1FloorCycle.boundary kind s sim.rng).core.regs 4-(56#32)))
    (timing : E1M1DeathTiming.Inputs (E1M1FloorCycle.boundary kind s sim.rng).core (E1M1FloorCycle.afterFloor kind z floor time suit sim).rng) (ins : E1M1FloorReturn.Inputs (E1M1FloorCycle.boundary kind s sim.rng).core)
    (safe : ∀ a, a ∈ SectorCaller.slots s → ∀ b, b ∈ E1M1FloorReturn.allWrites (E1M1FloorCycle.boundary kind s sim.rng).core → Apart a b) :
    ∃ (extreme : Bool) (t : X86Control.State),
      E1M1DeathSetter.stateId extreme=Death.deathState
        (PlayerDamage.apply v d none false false (E1M1FloorCycle.afterFloor kind z floor time suit sim).rng).state.health E1M1Death.playerInfo ∧
      X86CodeMemory.run FloorCaller.cm E1M1FloorCycle.program [0x333e5] 342 ⟨s,f,0x333d0⟩=some t ∧
      t.pc=0x333e5 ∧ t.core.regs 4=s.regs 4 ∧
      t.core.regs 6=s.regs 6 ∧ t.core.regs 2=s.regs 2 ∧
      t.core.regs 1=s.regs 1 ∧ t.core.regs 3=s.regs 3 ∧
      t.core.regs 5=(E1M1FloorCycle.boundary kind s sim.rng).core.regs 5 ∧ t.core.regs 7=(E1M1FloorCycle.boundary kind s sim.rng).core.regs 7 ∧
      DeathSetter.observeFields t.core.memory ((E1M1FloorCycle.boundary kind s sim.rng).core.regs 0)=
        ((E1M1DeathSetter.entry extreme).pointer,DeathTiming.playerTicks extreme (E1M1FloorCycle.afterFloor kind z floor time suit sim).rng.play,
         (E1M1DeathSetter.entry extreme).sprite,(E1M1DeathSetter.entry extreme).frame) ∧
      load32 t.core.memory (0x12720#32)=FloorDamage.nextIndex (E1M1FloorCycle.afterFloor kind z floor time suit sim).rng.play ∧
      load32 t.core.memory (0x1271c#32)=BitVec.ofNat 32 (E1M1FloorCycle.afterFloor kind z floor time suit sim).rng.misc.toNat ∧
      load32 t.core.memory (0x12c5c#32)=0 ∧
      KillBookkeeping.joinedObservation (E1M1FloorCycle.boundary kind s sim.rng).core 0 t=KillBookkeeping.joinedLiveObservation
        (PlayerDamage.apply v d none false false (E1M1FloorCycle.afterFloor kind z floor time suit sim).rng) 0 body (E1M1FloorCycle.afterFloor kind z floor time suit sim).deathWorld ∧
      load32 t.core.memory (KillBookkeeping.player 0+244)=0x15a28+BitVec.ofNat 32 (Weapon.down w.val)*28 ∧
      load32 t.core.memory (KillBookkeeping.player 0+248)=1 ∧
      load32 t.core.memory (KillBookkeeping.player 0+256)=(Weapon.lowerHeight y true).raw.toBitVec ∧
      PlayerHeight.Frame s.memory t.core.memory
        (FloorJoined.effectWrites s ++ E1M1FloorReturn.allWrites (E1M1FloorCycle.boundary kind s sim.rng).core) := by
  exact E1M1FloorCycle.joined_execution kind s f z floor time suit sim map floorInputs nonzero v d skill body info w y h dead stackSafe timing ins safe
