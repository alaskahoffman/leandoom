theorem prepared_checked (kind : FloorDamage.Kind) (s : X86Memory.State) (f : Option Flags)
    (motion : Motion) (anim : PlayerAnim.State) (cmd : Ticcmd) (timer : Int32)
    (view : ViewState) (time : Int32) (cached : Bool) (floor : Fixed) (tick : Nat) (suit : Bool)
    (sim : Simulation) (map : sim.map.name="E1M1")
    (h : FloorJoined.Inputs kind s motion anim cmd timer view time cached true floor tick suit sim.rng)
    (v : PlayerDamage.State) (d : Int32) (body : Death.Body) (info : body.info=E1M1Death.playerInfo)
    (w : Fin 3) (y : Fixed)
    (contract : DamageTransport.Contract (E1M1FloorCycle.boundary kind s sim.rng).core v d
      (E1M1FloorCycle.afterFloor kind motion.z floor tick suit sim) body w y)
    (nonzero : FloorDamage.requested (E1M1FloorCycle.boundary kind s sim.rng)≠0)
    (readSafe : ∀ a, a ∈ DamageTransport.reads (E1M1FloorCycle.boundary kind s sim.rng).core w
      (E1M1FloorCycle.afterFloor kind motion.z floor tick suit sim).rng → a≠0x12720 →
      ∀ b, b ∈ E1M1PreparedFloor.prefixWrites s → Apart a b)
    (savedSafe : ∀ a, a ∈ SectorCaller.slots s →
      ∀ b, b ∈ E1M1FloorReturn.allWrites (E1M1FloorCycle.boundary kind s sim.rng).core → Apart a b) :
    ∃ (p : X86Control.State) (extreme : Bool) (t : X86Control.State),
      X86Routine.run PlayerPreparation.program [0x333d0] 225 ⟨s,f,0x333b1⟩=some p ∧
      p.pc=0x333d0 ∧
      X86CodeMemory.run FloorCaller.cm E1M1PreparedFloor.program [0x333e5] 567 ⟨s,f,0x333b1⟩=some t ∧
      E1M1DeathSetter.stateId extreme=Death.deathState
        (PlayerDamage.apply v d none false false (E1M1FloorCycle.afterFloor kind motion.z floor tick suit sim).rng).state.health E1M1Death.playerInfo ∧
      t.pc=0x333e5 ∧ t.core.regs 4=s.regs 4 ∧
      t.core.regs 6=p.core.regs 6 ∧ t.core.regs 2=p.core.regs 2 ∧
      t.core.regs 1=p.core.regs 1 ∧ t.core.regs 3=p.core.regs 3 ∧
      t.core.regs 5=(E1M1FloorCycle.boundary kind p.core sim.rng).core.regs 5 ∧ t.core.regs 7=(E1M1FloorCycle.boundary kind p.core sim.rng).core.regs 7 ∧
      DeathSetter.observeFields t.core.memory ((E1M1FloorCycle.boundary kind p.core sim.rng).core.regs 0)=
        ((E1M1DeathSetter.entry extreme).pointer,DeathTiming.playerTicks extreme (E1M1FloorCycle.afterFloor kind motion.z floor tick suit sim).rng.play,
         (E1M1DeathSetter.entry extreme).sprite,(E1M1DeathSetter.entry extreme).frame) ∧
      load32 t.core.memory (0x12720#32)=FloorDamage.nextIndex (E1M1FloorCycle.afterFloor kind motion.z floor tick suit sim).rng.play ∧
      load32 t.core.memory (0x1271c#32)=BitVec.ofNat 32 (E1M1FloorCycle.afterFloor kind motion.z floor tick suit sim).rng.misc.toNat ∧
      load32 t.core.memory (0x12c5c#32)=0 ∧
      KillBookkeeping.joinedObservation (E1M1FloorCycle.boundary kind p.core sim.rng).core 0 t=KillBookkeeping.joinedLiveObservation
        (PlayerDamage.apply v d none false false (E1M1FloorCycle.afterFloor kind motion.z floor tick suit sim).rng) 0 body (E1M1FloorCycle.afterFloor kind motion.z floor tick suit sim).deathWorld ∧
      load32 t.core.memory (KillBookkeeping.player 0+244)=0x15a28+BitVec.ofNat 32 (Weapon.down w.val)*28 ∧
      load32 t.core.memory (KillBookkeeping.player 0+248)=1 ∧
      load32 t.core.memory (KillBookkeeping.player 0+256)=(Weapon.lowerHeight y true).raw.toBitVec ∧
      PlayerHeight.Frame s.memory t.core.memory
        (SectorDispatch.writes s ++ (FloorJoined.effectWrites s ++ E1M1FloorReturn.allWrites (E1M1FloorCycle.boundary kind s sim.rng).core)) := by
  exact E1M1PreparedFloor.joined_execution kind s f motion anim cmd timer view time cached floor tick suit sim map h v d body info w y contract nonzero readSafe savedSafe

theorem joined_checked (kind : FloorDamage.Kind) (s : X86Memory.State) (f : Option Flags)
    (motion : Motion) (anim : PlayerAnim.State) (cmd : Ticcmd) (timer : Int32)
    (view : ViewState) (time : Int32) (cached : Bool) (floor : Fixed) (tick : Nat) (suit : Bool)
    (sim : Simulation) (map : sim.map.name="E1M1")
    (h : FloorJoined.Inputs kind s motion anim cmd timer view time cached true floor tick suit sim.rng)
    (v : PlayerDamage.State) (d : Int32) (body : Death.Body) (info : body.info=E1M1Death.playerInfo)
    (w : Fin 3) (y : Fixed)
    (contract : DamageTransport.Contract (E1M1FloorCycle.boundary kind s sim.rng).core v d
      (E1M1FloorCycle.afterFloor kind motion.z floor tick suit sim) body w y)
    (nonzero : FloorDamage.requested (E1M1FloorCycle.boundary kind s sim.rng)≠0)
    (readSafe : ∀ a, a ∈ DamageTransport.reads (E1M1FloorCycle.boundary kind s sim.rng).core w
      (E1M1FloorCycle.afterFloor kind motion.z floor tick suit sim).rng → a≠0x12720 →
      ∀ b, b ∈ E1M1PreparedFloor.prefixWrites s → Apart a b)
    (savedSafe : ∀ a, a ∈ SectorCaller.slots s →
      ∀ b, b ∈ E1M1FloorReturn.allWrites (E1M1FloorCycle.boundary kind s sim.rng).core → Apart a b)
    (buttons : BitVec 8) (choice : Fin 3) (selection : WeaponSelect.Inputs s buttons choice)
    (selectionSafe : ∀ a, a ∈ E1M1PlayerSelection.reads s choice → ∀ v, v ∈ E1M1PlayerSelection.priorWrites kind s sim.rng → Apart a v) :
    ∃ before : X86Control.State,
      X86CodeMemory.run FloorCaller.cm E1M1PreparedFloor.program [0x333e5] 567 ⟨s,f,0x333b1⟩=some before ∧
      X86CodeMemory.run FloorCaller.cm E1M1PlayerSelection.program [0x33476] 591 ⟨s,f,0x333b1⟩=some (WeaponSelect.result before.core buttons choice) ∧
      before.core.regs 2=s.regs 2 ∧ before.core.regs 3=s.regs 3 ∧
      PlayerHeight.Frame s.memory before.core.memory (E1M1PlayerSelection.priorWrites kind s sim.rng) ∧
      (∀ c : Weapon.Context,
        (WeaponSelect.owns s choice != 0)=c.player.weapons[choice.val] →
        WeaponSelect.current s=BitVec.ofNat 32 c.player.readyWeapon.val →
        load32 s.memory (s.regs 2+116)=BitVec.ofNat 32 c.player.pendingWeapon.val →
        load32 (WeaponSelect.result before.core buttons choice).core.memory (s.regs 2+116)=
          BitVec.ofNat 32 (c.select (if buttons &&& (4#8)=(0#8) then none else some choice.val)).player.pendingWeapon.val) := by
  exact E1M1PlayerSelection.joined_execution kind s f motion anim cmd timer view time cached floor tick suit sim map h v d body info w y contract nonzero readSafe savedSafe buttons choice selection selectionSafe
