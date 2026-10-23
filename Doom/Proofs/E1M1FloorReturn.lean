import Doom.Proofs.OriginalLethalReturn
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1FloorReturn
open Verification X86 X86Memory X86Control BlockSummary

def program (pc : Nat) : Option (X86Routine.Op × Nat) :=
  match E1M1DeathTiming.program pc with
  | some op => some op
  | none => match DeathReturn.program pc with
    | some op => some op
    | none => LethalReturn.program pc

theorem contains_previous (pc : Nat) (h : E1M1DeathTiming.program pc≠none) :
    program pc=E1M1DeathTiming.program pc := by
  unfold program
  cases eq : E1M1DeathTiming.program pc with
  | none => exact False.elim (h eq)
  | some op => rfl

theorem previous_none (pc : Nat)
    (bound : (0x2a40d ≤ pc ∧ pc < 0x2a457) ∨ (0x2a6b1 ≤ pc ∧ pc < 0x2a6b6) ∨
      (0x2a747 ≤ pc ∧ pc < 0x2a74e)) : E1M1DeathTiming.program pc=none := by
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
  have b15 : ¬(0x2a3f1 ≤ pc ∧ pc < 0x2a40d) := by omega
  have b16 : ¬(0x24160 ≤ pc ∧ pc < 0x2417c) := by omega
  simp [E1M1DeathTiming.program,E1M1DeathSetter.program,DeathSetter.program,PainSetter.program,PainSetter.bytesProgram,
    KillDeathBranches.program,KillDeathBranches.bytesProgram,KillWeaponDrop.program,KillBookkeeping.joined,KillEntry.joined,
    ActorHealth.joined,PlayerHealth.joined,PlayerDamageEntry.program,PlayerDamageEntry.bytesProgram,
    WeaponDrop.program,WeaponDrop.bytesProgram,WeaponLower.bytesProgram,DeathTiming.program,DeathTiming.bytesProgram,
    DeathBranches.bytesProgram,DeathAutomap.bytesProgram,DeathChoice.bytesProgram,
    b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16,
    show pc ≠ 0x2fb76 by omega,show pc ≠ 0x2fba0 by omega,show pc ≠ 0x2fbd2 by omega]

theorem contains_return (pc : Nat) (h : DeathReturn.program pc≠none) :
    program pc=DeathReturn.program pc := by
  have bound : 0x2a40d ≤ pc ∧ pc < 0x2a457 := by
    by_cases yes : 0x2a40d ≤ pc ∧ pc < 0x2a457
    · exact yes
    · simp [DeathReturn.program,DeathReturn.bytesProgram,yes] at h
  simp only [program,previous_none pc (Or.inl bound)]
  cases eq : DeathReturn.program pc with
  | none => exact False.elim (h eq)
  | some op => rfl

theorem contains_damage (pc : Nat) (h : LethalReturn.program pc≠none) :
    program pc=LethalReturn.program pc := by
  have bound : (0x2a6b1 ≤ pc ∧ pc < 0x2a6b6) ∨ (0x2a747 ≤ pc ∧ pc < 0x2a74e) := by
    by_cases yes : (0x2a6b1 ≤ pc ∧ pc < 0x2a6b6) ∨ (0x2a747 ≤ pc ∧ pc < 0x2a74e)
    · exact yes
    · have b1 : ¬(0x2a6b1 ≤ pc ∧ pc < 0x2a6b6) := by omega
      have b2 : ¬(0x2a747 ≤ pc ∧ pc < 0x2a74e) := by omega
      simp [LethalReturn.program,LethalReturn.bytesProgram,b1,b2] at h
  have b : ¬(0x2a40d ≤ pc ∧ pc < 0x2a457) := by omega
  simp [program,previous_none pc (Or.inr bound),DeathReturn.program,DeathReturn.bytesProgram,b]

def allWrites (s : X86Memory.State) := E1M1DeathTiming.previousWrites s ++ E1M1DeathTiming.timingWrites s
/-- New hypotheses concern only initial address separation. Neither return
address nor any saved value is assumed at an intermediate state. -/
structure Inputs (s : X86Memory.State) : Prop where
  killReturnSafe : ∀ b, b ∈ E1M1DeathTiming.returnWrites s → Apart (s.regs 4-32) b
  outerSafe : ∀ a, a ∈ [s.regs 4-4,s.regs 4-8,s.regs 4-12,s.regs 4-16] →
    ∀ b, b ∈ E1M1DeathTiming.stackWrites s → Apart a b
  kindSafe : ∀ b, b ∈ allWrites s → Apart (s.regs 0+88) b

theorem joined_execution (s : X86Memory.State) (f : Option Flags) (pc : Nat)
    (site : pc ∈ PlayerDamageEntry.sites) (v : PlayerDamage.State) (d : Int32)
    (sim : Simulation) (map : sim.map.name="E1M1") (skill : load32 s.memory (0x2b3e0#32)=2)
    (body : Death.Body) (info : body.info=E1M1Death.playerInfo) (w : Fin 3) (y : Fixed)
    (h : KillDeathBranches.Inputs s v d false 0 body sim.deathWorld w y)
    (dead : (PlayerDamage.apply v d none false false sim.rng).killed=true)
    (stackSafe : Apart (0x12c5c#32) (s.regs 4-(56#32)))
    (timing : E1M1DeathTiming.Inputs s sim.rng) (ins : Inputs s) :
    ∃ (extreme : Bool) (k t : X86Control.State),
      E1M1DeathSetter.stateId extreme=Death.deathState
        (PlayerDamage.apply v d none false false sim.rng).state.health E1M1Death.playerInfo ∧
      X86Routine.run program [0x2a6b1] 289 ⟨s,f,pc⟩=some k ∧
      k.pc=0x2a6b1 ∧ k.core.regs 4=s.regs 4-28 ∧
      X86Routine.run program [pc+5] 295 ⟨s,f,pc⟩=some t ∧
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
      PlayerHeight.Frame s.memory t.core.memory (allWrites s) := by
  obtain ⟨extreme,g,saved,choice,grun,gpc,obj,sp,fields,index,misc,off,obs,weapon,tics,height,frame⟩ :=
    E1M1DeathTiming.joined_execution_tracked s f pc site v d sim map skill body info w y h dead stackSafe timing
  have kind : load32 g.core.memory (g.core.regs 3+88)=0 := by
    rw [obj,frame _ ins.kindSafe]
    exact h.prior.prior.kind
  have returnWord := saved.killReturn ins.killReturnSafe
  let k := DeathReturn.result g.core
  have kpc : k.pc=0x2a6b1 := by
    change (load32 g.core.memory (g.core.regs 4+20)).toNat=_
    rw [sp,show s.regs 4-52+20=s.regs 4-32 by simp [BitVec.sub_eq_add_neg,BitVec.add_assoc],returnWord]
    rfl
  have ksp : k.core.regs 4=s.regs 4-28 := by
    change g.core.regs 4+24=_
    rw [sp]; simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  have krun := DeathReturn.original_execution g.core g.flags kind (by change k.pc < _ ∨ _ ≤ k.pc; rw [kpc]; omega)
  change X86Routine.run DeathReturn.program [k.pc] 11 ⟨g.core,g.flags,0x2a40d⟩=some k at krun
  rw [kpc,←gpc] at krun
  obtain ⟨n,hn,p,_⟩ := X86Routine.run_path grun
  have p := p.transfer program [0x2a6b1] contains_previous (by
    intro pc hp; simp only [List.mem_singleton]; intro eq; subst pc; exact hp (by decide))
  obtain ⟨j,hj,q,_⟩ := X86Routine.run_path krun
  have q := q.transfer program [0x2a6b1] contains_return (by
    intro pc hp; simp only [List.mem_singleton]; intro eq; subst pc; exact hp (by decide))
  have tail : X86Routine.run program [0x2a6b1] 11 g=some k :=
    q.finish (fuel := 0) (by simp [X86Routine.run,kpc]) 11 (by omega)
  have runKill : X86Routine.run program [0x2a6b1] 289 ⟨s,f,pc⟩=some k := p.finish tail 289 (by omega)
  have outer (a : Word) (ha : a ∈ [s.regs 4-4,s.regs 4-8,s.regs 4-12,s.regs 4-16]) :
      load32 k.core.memory a=load32 (PlayerDamageEntry.saved s pc) a :=
    saved.outer a (ins.outerSafe a ha)
  have slots := DamageReturn.saved_slots s pc
  let t := LethalReturn.result k.core
  have tpc : t.pc=pc+5 := by
    change (load32 k.core.memory (k.core.regs 4+24)).toNat=_
    rw [ksp,show s.regs 4-28+24=s.regs 4-4 by simp [BitVec.sub_eq_add_neg,BitVec.add_assoc],
      outer _ (by simp)]
    change (load32 (PlayerDamageEntry.saved s pc) (s.regs 4-(4#32))).toNat=pc+5
    rw [slots.1]
    rcases (show pc=0x2fb76 ∨ pc=0x2fba0 ∨ pc=0x2fbd2 by simpa [PlayerDamageEntry.sites] using site) with rfl|rfl|rfl <;> decide
  have outside : 0x2a74e ≤ pc+5 := by
    simp only [PlayerDamageEntry.sites,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at site
    rcases site with rfl|rfl|rfl <;> decide
  have inactive : program (pc+5)=none := by
    simp only [PlayerDamageEntry.sites,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at site
    rcases site with rfl|rfl|rfl <;> decide
  have finish := LethalReturn.original_execution k.core k.flags (by change _ ≤ t.pc; rw [tpc]; exact outside)
  change X86Routine.run LethalReturn.program [t.pc] 6 ⟨k.core,k.flags,0x2a6b1⟩=some t at finish
  rw [tpc,←kpc] at finish
  obtain ⟨j,hj,q,_⟩ := X86Routine.run_path finish
  have q := q.transfer program [pc+5] contains_damage (by
    intro addr hp; simp only [List.mem_singleton]; intro eq; subst addr
    have yes := contains_damage (pc+5) hp; rw [inactive] at yes; exact hp yes.symm)
  have finish : X86Routine.run program [pc+5] 6 k=some t :=
    q.finish (fuel := 0) (by simp [X86Routine.run,tpc]) 6 (by omega)
  obtain ⟨n,hn,p,_⟩ := X86Routine.run_path runKill
  have p := p.transfer program [pc+5] (fun _ _ => rfl) (by
    intro addr hp; simp only [List.mem_singleton]; intro eq; subst addr; exact hp inactive)
  refine ⟨extreme,k,t,choice,runKill,kpc,ksp,p.finish finish 295 (by omega),tpc,?_,?_,?_,?_,
    rfl,fields,index,misc,off,obs,weapon,tics,height,frame⟩
  · change k.core.regs 4+28=s.regs 4
    rw [ksp]; simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  · change load32 k.core.memory (k.core.regs 4+12)=s.regs 5
    rw [ksp,show s.regs 4-28+12=s.regs 4-16 by simp [BitVec.sub_eq_add_neg,BitVec.add_assoc],outer _ (by simp)]
    exact slots.2.2.2.1
  · change load32 k.core.memory (k.core.regs 4+16)=s.regs 7
    rw [ksp,show s.regs 4-28+16=s.regs 4-12 by simp [BitVec.sub_eq_add_neg,BitVec.add_assoc],outer _ (by simp)]
    exact slots.2.2.1
  · change load32 k.core.memory (k.core.regs 4+20)=s.regs 6
    rw [ksp,show s.regs 4-28+20=s.regs 4-8 by simp [BitVec.sub_eq_add_neg,BitVec.add_assoc],outer _ (by simp)]
    exact slots.2.1

end Doom.Proofs.E1M1FloorReturn
