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
      X86CodeMemory.run FloorCaller.cm E1M1PlayerSelection.program [0x33476] 591 ⟨s,f,0x333b1⟩=
        some (WeaponSelect.result before.core buttons choice) ∧
      X86CodeMemory.run FloorCaller.cm E1M1UseButton.program UseButtonCode.exits 597 ⟨s,f,0x333b1⟩=
        some (UseButtonCode.result (WeaponSelect.result before.core buttons choice).core) := by
  exact E1M1UseButton.joined_execution kind s f motion anim cmd timer view time cached floor tick suit sim map h v d body info w y contract nonzero readSafe savedSafe buttons choice selection selectionSafe
