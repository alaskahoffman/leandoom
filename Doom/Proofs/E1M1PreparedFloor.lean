import Doom.Proofs.OriginalDamageTransport
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1PreparedFloor
open Verification X86 X86Memory X86Control BlockSummary

def program (pc : Nat) : Option (X86Routine.Op × Nat) :=
  match E1M1FloorCycle.program pc with
  | some op => some op
  | none => PlayerPreparation.program pc

theorem contains_cycle (pc : Nat) (h : E1M1FloorCycle.program pc≠none) :
    program pc=E1M1FloorCycle.program pc := by
  unfold program
  cases eq : E1M1FloorCycle.program pc with
  | none => exact False.elim (h eq)
  | some op => rfl

theorem contains_preparation (pc : Nat) (h : PlayerPreparation.program pc≠none) :
    program pc=PlayerPreparation.program pc := by
  have range : (0x30ea0 ≤ pc ∧ pc < 0x30efb) ∨ (0x33030 ≤ pc ∧ pc < 0x3315e) ∨
      (0x33160 ≤ pc ∧ pc < 0x33268) ∨ (0x333b1 ≤ pc ∧ pc < 0x333d0) := by
    change (match PlayerHeight.Shared.program pc with | some op => some op | none => PlayerReactionProof.program pc)≠none at h
    cases hh : PlayerHeight.Shared.program pc with
    | none =>
      rw [hh] at h
      have r := PlayerPreparation.reaction_region pc h
      omega
    | some op =>
      unfold PlayerHeight.Shared.program PlayerHeight.Shared.bytesProgram at hh
      split at hh
      next hp => omega
      next hp =>
        split at hh
        next hc => change 0x33030 ≤ pc ∧ pc < 0x33030+302 at hc; omega
        next hc => simp_all
  rcases range with a|b|c|d
  · have checked : ∀ i : Fin 91, program (0x30ea0+i.val)=PlayerPreparation.program (0x30ea0+i.val) := by decide
    have eq : 0x30ea0+(pc-0x30ea0)=pc := by omega
    simpa only [eq] using checked ⟨pc-0x30ea0,by omega⟩
  · have checked : ∀ i : Fin 302, program (0x33030+i.val)=PlayerPreparation.program (0x33030+i.val) := by decide
    have eq : 0x33030+(pc-0x33030)=pc := by omega
    simpa only [eq] using checked ⟨pc-0x33030,by omega⟩
  · have checked : ∀ i : Fin 264, program (0x33160+i.val)=PlayerPreparation.program (0x33160+i.val) := by decide
    have eq : 0x33160+(pc-0x33160)=pc := by omega
    simpa only [eq] using checked ⟨pc-0x33160,by omega⟩
  · have checked : ∀ i : Fin 31, program (0x333b1+i.val)=PlayerPreparation.program (0x333b1+i.val) := by decide
    have eq : 0x333b1+(pc-0x333b1)=pc := by omega
    simpa only [eq] using checked ⟨pc-0x333b1,by omega⟩

/-- Initial addresses that preparation and the floor's stack stores may touch. -/
def prefixWrites (s : X86Memory.State) := SectorDispatch.writes s ++ FloorJoined.effectWrites s

/-- Lift the actual floor-call contracts across player preparation. The RNG
index is handled by the floor correspondence, not an incorrect disjointness
assumption that would exclude the suit-leak draw. -/
theorem boundary_agrees (kind : FloorDamage.Kind) (s t : X86Memory.State) (f : Option Flags)
    (z floor : Fixed) (tick : Nat) (suit : Bool) (rng after : DoomRandom) (w : Fin 3)
    (initial : FloorCaller.Inputs kind s z floor tick suit rng)
    (prepared : FloorCaller.Inputs kind t z floor tick suit rng)
    (edx : t.regs 2=s.regs 2) (sp : t.regs 4=s.regs 4)
    (frame : PlayerHeight.Frame s.memory t.memory (SectorDispatch.writes s))
    (objRead : ∀ b, b ∈ SectorDispatch.writes s → Apart (s.regs 2) b)
    (nonzero : FloorDamage.requested (FloorCaller.result kind s rng)≠0)
    (safe : ∀ a, a ∈ DamageTransport.reads (FloorCaller.result kind s rng).core w after → a≠0x12720 →
      ∀ b, b ∈ prefixWrites s → Apart a b) :
    DamageTransport.Agrees (FloorCaller.result kind s rng).core (FloorCaller.result kind t rng).core w after := by
  let a := FloorCaller.result kind s rng
  let b := FloorCaller.result kind t rng
  have oa := FloorCaller.correspondence kind s f z floor tick suit rng initial
  have ob := FloorCaller.correspondence kind t f z floor tick suit rng prepared
  rw [FloorCaller.execution kind s f z floor tick suit rng initial,Option.map_some] at oa
  rw [FloorCaller.execution kind t f z floor tick suit rng prepared,Option.map_some] at ob
  have same : FloorDamage.observe b=FloorDamage.observe a := Option.some.inj (ob.trans oa.symm)
  have amount := congrArg Prod.fst same
  have index := congrArg (fun x => x.2.1) same
  have nz : FloorDamage.requested b≠0 := fun eq => nonzero (amount.symm.trans eq)
  obtain ⟨aobj,az,az',_⟩ := FloorCaller.damage_arguments kind s z floor tick suit rng initial nonzero
  obtain ⟨bobj,bz,bz',_⟩ := FloorCaller.damage_arguments kind t z floor tick suit rng prepared nz
  have obj : SectorDispatch.object t=SectorDispatch.object s := by
    unfold SectorDispatch.object; rw [edx,frame _ objRead]
  have na : a.pc≠0x2fc39 := by intro eq; exact nonzero (by change FloorDamage.requested a=0; simp [FloorDamage.requested,eq])
  have nb : b.pc≠0x2fc39 := by intro eq; exact nz (by simp [FloorDamage.requested,eq])
  have ecx : b.core.regs 1=a.core.regs 1 := by
    apply BitVec.eq_of_toNat_eq
    simpa only [FloorDamage.observe,FloorDamage.requested,if_neg na,if_neg nb] using amount
  refine ⟨bobj.trans (obj.trans aobj.symm),ecx,bz.trans az.symm,bz'.trans az'.symm,?_,?_⟩
  · rw [FloorCaller.stack_position,FloorCaller.stack_position,sp]
  · intro addr ha
    by_cases atIndex : addr=0x12720
    · subst addr; exact index
    have af := FloorJoined.handler_frame kind s z floor tick suit rng initial
    have bf := FloorJoined.handler_frame kind t z floor tick suit rng prepared
    rw [FloorJoined.effect_locations s t sp] at bf
    rw [bf addr (fun x hx => safe addr ha atIndex x (List.mem_append_right _ hx)),
      frame addr (fun x hx => safe addr ha atIndex x (List.mem_append_left _ hx)),
      af addr (fun x hx => safe addr ha atIndex x (List.mem_append_right _ hx))]

/-- Preparation and the lethal floor cycle compose from initial-state contracts.
Damage contracts are transported by the preceding footprint theorem, not
assumed on the existential prepared state. The final memory frame spans both. -/
theorem joined_execution (kind : FloorDamage.Kind) (s : X86Memory.State) (f : Option Flags)
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
      ∀ b, b ∈ prefixWrites s → Apart a b)
    (savedSafe : ∀ a, a ∈ SectorCaller.slots s →
      ∀ b, b ∈ E1M1FloorReturn.allWrites (E1M1FloorCycle.boundary kind s sim.rng).core → Apart a b) :
    ∃ (p : X86Control.State) (extreme : Bool) (t : X86Control.State),
      X86Routine.run PlayerPreparation.program [0x333d0] 225 ⟨s,f,0x333b1⟩=some p ∧
      p.pc=0x333d0 ∧
      X86CodeMemory.run FloorCaller.cm program [0x333e5] 567 ⟨s,f,0x333b1⟩=some t ∧
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
  obtain ⟨p,run,pc,_,_,sp,_,edx⟩ := PlayerPreparation.execution_preserved s f motion anim cmd timer view time cached true h.preparation
  obtain ⟨p',run',_,_,_,frame⟩ := PreparedState.execution s f motion anim cmd timer view time cached true h.preparation
  have same : p'=p := Option.some.inj (run'.symm.trans run)
  subst p'
  have keep (a : Word) (ha : a ∈ FloorCaller.reads s) := frame a (h.floorReads a ha)
  have floorInputs := FloorJoined.transport kind s p.core motion.z floor tick suit sim.rng h.floorInputs edx sp keep
    (frame.byte _ h.tableRead)
  have eq := boundary_agrees kind s p.core f motion.z floor tick suit sim.rng
    (E1M1FloorCycle.afterFloor kind motion.z floor tick suit sim).rng w h.floorInputs floorInputs edx sp frame
    (h.floorReads _ (by simp [FloorCaller.reads])) nonzero readSafe
  have transported := contract.transport _ _ v d _ body w y eq
  have writeLocations := DamageTransport.allWrites_eq _ _ w _ eq
  have nz : FloorDamage.requested (E1M1FloorCycle.boundary kind p.core sim.rng)≠0 := by
    have oa := FloorCaller.correspondence kind s f motion.z floor tick suit sim.rng h.floorInputs
    have ob := FloorCaller.correspondence kind p.core f motion.z floor tick suit sim.rng floorInputs
    rw [FloorCaller.execution kind s f motion.z floor tick suit sim.rng h.floorInputs,Option.map_some] at oa
    rw [FloorCaller.execution kind p.core f motion.z floor tick suit sim.rng floorInputs,Option.map_some] at ob
    exact fun bad => nonzero ((congrArg Prod.fst (Option.some.inj (oa.trans ob.symm))).trans bad)
  have safe : ∀ a, a ∈ SectorCaller.slots p.core →
      ∀ b, b ∈ E1M1FloorReturn.allWrites (E1M1FloorCycle.boundary kind p.core sim.rng).core → Apart a b := by
    simpa only [SectorCaller.slots,sp,writeLocations] using savedSafe
  obtain ⟨extreme,t,choice,tail,post⟩ := E1M1FloorCycle.joined_execution kind p.core p.flags motion.z floor tick suit sim map floorInputs nz
    v d transported.skill body info w y transported.damage transported.dead transported.stackSafe transported.timing transported.returns safe
  have tail' : X86CodeMemory.run FloorCaller.cm E1M1FloorCycle.program [0x333e5] 342 p=some t := by
    have peq : p=⟨p.core,p.flags,0x333d0⟩ := by rw [←pc]
    rw [peq]; exact tail
  obtain ⟨j,hj,q,done⟩ := X86CodeMemory.run_path tail'
  have q := q.transfer program [0x333e5] contains_cycle (by
    intro addr hp; simp only [List.mem_singleton]; intro e; subst addr; exact hp (by decide))
  have tail : X86CodeMemory.run FloorCaller.cm program [0x333e5] 342 p=some t :=
    q.finish (fuel := 0) (by simp [X86CodeMemory.run,done]) 342 (by omega)
  obtain ⟨n,hn,path,_⟩ := X86Routine.run_path run
  have path := (X86CodeMemory.lift_success path FloorCaller.cm).transfer program [0x333e5] contains_preparation (by
    intro addr hp; simp only [List.mem_singleton]; intro e; subst addr; exact hp (by decide))
  rcases post with ⟨tpc,tsp,si,dx,cx,bx,bp,di,fields,index,misc,off,obs,weapon,tics,height,finalFrame⟩
  rw [FloorJoined.effect_locations s p.core sp,writeLocations] at finalFrame
  refine ⟨p,extreme,t,run,pc,path.finish tail 567 (by omega),choice,tpc,tsp.trans sp,
    si,dx,cx,bx,bp,di,fields,index,misc,off,obs,weapon,tics,height,?_⟩
  intro a ha
  rw [finalFrame a (fun b hb => ha b (List.mem_append_right _ hb))]
  exact frame a (fun b hb => ha b (List.mem_append_left _ hb))

end Doom.Proofs.E1M1PreparedFloor
