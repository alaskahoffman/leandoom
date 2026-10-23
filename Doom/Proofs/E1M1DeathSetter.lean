import Doom.Proofs.E1M1Death
import Doom.Proofs.OriginalDeathSetter
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1DeathSetter
open Verification X86 X86Memory X86Control BlockSummary

def stateId (extreme : Bool) : Nat := if extreme then 165 else 158
def entry (extreme : Bool) : DeathSetter.Entry :=
  if extreme then ⟨165,28,14,5,166,by decide,by decide⟩
  else ⟨158,28,7,10,159,by decide,by decide⟩

def stateBytes (extreme : Bool) : List UInt8 :=
  if extreme then [28,0,0,0,14,0,0,0,5,0,0,0,0,0,0,0,166,0,0,0,0,0,0,0,0,0,0,0]
  else [28,0,0,0,7,0,0,0,10,0,0,0,0,0,0,0,159,0,0,0,0,0,0,0,0,0,0,0]

theorem table_decoded (extreme : Bool) : DeathSetter.Table (entry extreme) (fun a =>
    let base := (entry extreme).pointer.toNat
    if base ≤ a.toNat ∧ a.toNat < base+28 then (stateBytes extreme).toArray[a.toNat-base]!.toBitVec else 0) := by
  cases extreme <;> constructor <;> decide

theorem live_metadata (extreme : Bool) :
    ((Death.frames.find? (·.id == stateId extreme)).map
      (fun frame => (frame.sprite,frame.frame,frame.tics,frame.next,frame.action))) =
    some ("PLAY",(entry extreme).frame.toNat,Int32.ofBitVec (entry extreme).tics,
      (entry extreme).next.toNat,"NULL") := by
  cases extreme <;> decide

/-- Exact live setState result; no action, sound, or RNG draw occurs on entry.
The randomized death duration is a subsequent P_KillMobj operation. -/
theorem live_entry (extreme : Bool) (body : Death.Body) (world : Death.World) :
    Death.setState Death.frames body world (stateId extreme) =
      .ok ({body with state := stateId extreme, tics := Int32.ofBitVec (entry extreme).tics},
        {world with events := world.events.push (.state (stateId extreme))}) := by
  cases extreme <;>
    simp only [stateId,entry,↓reduceIte,Death.setState,Std.Legacy.Range.forIn_eq_forIn_range'] <;>
    rw [show ([:1000002] : Std.Legacy.Range).size=1000001+1 from rfl,List.range'_succ,List.forIn_cons] <;> rfl

/-- The actual DOS state pointer/countdown agree with the actual Lean setState
result. Sprite/frame metadata is connected separately by live_metadata. -/
theorem live_correspondence (extreme : Bool) (s : X86Memory.State) (f : Option Flags)
    (h : DeathSetter.SetterInputs (entry extreme) s) (body : Death.Body) (world : Death.World) :
    (X86Routine.run DeathSetter.program [0x2a3f1] 24 ⟨s,f,0x30ea0⟩).map
      (fun t => let fields := DeathSetter.observeFields t.core.memory (s.regs 0)
        (fields.1,fields.2.1)) =
    (match Death.setState Death.frames body world (stateId extreme) with
      | .ok (body,_) => some (PlayerAnimation.statePointer body.state,body.tics.toBitVec)
      | .error _ => none) := by
  rw [DeathSetter.original_execution (entry extreme) s f h,live_entry]
  simp only [Option.map_some,DeathSetter.setterEnd,DeathSetter.entry_fields]
  cases extreme <;> rfl

def program (pc : Nat) : Option (X86Routine.Op × Nat) :=
  match KillDeathBranches.program pc with
  | some op => some op
  | none => DeathSetter.program pc

theorem contains_previous (pc : Nat) (h : KillDeathBranches.program pc≠none) :
    program pc=KillDeathBranches.program pc := by
  unfold program
  cases eq : KillDeathBranches.program pc with
  | none => exact False.elim (h eq)
  | some op => rfl

theorem contains_setter (pc : Nat) (h : DeathSetter.program pc≠none) :
    program pc=DeathSetter.program pc := by
  have bound : 0x30ea0 ≤ pc ∧ pc < 0x30efb := by
    by_cases yes : 0x30ea0 ≤ pc ∧ pc < 0x30efb
    · exact yes
    · simp [DeathSetter.program,PainSetter.program,PainSetter.bytesProgram,yes] at h
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
  simp [program,KillDeathBranches.program,KillDeathBranches.bytesProgram,
    KillWeaponDrop.program,KillBookkeeping.joined,KillEntry.joined,
    ActorHealth.joined,PlayerHealth.joined,PlayerDamageEntry.program,PlayerDamageEntry.bytesProgram,
    WeaponDrop.program,WeaponDrop.bytesProgram,WeaponLower.bytesProgram,
    DeathBranches.bytesProgram,DeathAutomap.bytesProgram,DeathChoice.bytesProgram,
    b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,
    show pc ≠ 0x2fb76 by omega,show pc ≠ 0x2fba0 by omega,show pc ≠ 0x2fbd2 by omega]

def previousWrites (s : X86Memory.State) := KillDeathBranches.priorWrites s 0 ++ [s.regs 4-56]
def suffixWrites (s : X86Memory.State) := DeathSetter.fields (s.regs 0) ++ [s.regs 4-60,s.regs 4-64]
def retained (s : X86Memory.State) := KillDeathBranches.retained s 0 ++ [0x12c5c,0x12720]
structure Inputs (s : X86Memory.State) : Prop where
  tables : ∀ extreme, DeathSetter.Table (entry extreme) s.memory
  tablePreviousSafe : ∀ extreme a, a ∈ DeathSetter.tableWords (entry extreme) →
    ∀ b, b ∈ previousWrites s → Apart a b
  tableSetterSafe : ∀ extreme a, a ∈ DeathSetter.tableWords (entry extreme) →
    ∀ b, b ∈ suffixWrites s → Apart a b
  stackSetterSafe : ∀ a, a ∈ [s.regs 4-56,s.regs 4-60,s.regs 4-64] →
    ∀ b, b ∈ DeathSetter.fields (s.regs 0) → Apart a b
  retainedSetterSafe : ∀ a, a ∈ retained s → ∀ b, b ∈ suffixWrites s → Apart a b

/-- Joined from the original floor-damage CALL, with all setter assumptions
transported from that initial memory. Returns to P_KillMobj before the RNG draw. -/
def stackWrites (s : X86Memory.State) := KillDeathBranches.stackWrites s 0 ++ suffixWrites s
def returnWrites (s : X86Memory.State) := KillDeathBranches.returnWrites s 0 ++ suffixWrites s

theorem joined_execution_tracked (s : X86Memory.State) (f : Option Flags) (pc : Nat)
    (site : pc ∈ PlayerDamageEntry.sites) (v : PlayerDamage.State) (d : Int32)
    (sim : Simulation) (map : sim.map.name="E1M1") (skill : load32 s.memory (0x2b3e0#32)=2)
    (body : Death.Body) (info : body.info=E1M1Death.playerInfo) (w : Fin 3) (y : Fixed)
    (h : KillDeathBranches.Inputs s v d false 0 body sim.deathWorld w y)
    (dead : (PlayerDamage.apply v d none false false sim.rng).killed=true)
    (stackSafe : Apart (0x12c5c#32) (s.regs 4-(56#32))) (ins : Inputs s) :
    ∃ (extreme : Bool) (t : X86Control.State),
      DeathStack.Saved s pc t.core.memory (stackWrites s) (returnWrites s) ∧
      stateId extreme=Death.deathState (PlayerDamage.apply v d none false false sim.rng).state.health E1M1Death.playerInfo ∧
      X86Routine.run program [0x2a3f1] 263 ⟨s,f,pc⟩=some t ∧
      t.pc=0x2a3f1 ∧ t.core.regs 0=1 ∧ t.core.regs 3=s.regs 0 ∧ t.core.regs 4=s.regs 4-52 ∧
      DeathSetter.observeFields t.core.memory (s.regs 0)=
        ((entry extreme).pointer,(entry extreme).tics,(entry extreme).sprite,(entry extreme).frame) ∧
      load32 t.core.memory (0x12c5c#32)=0 ∧
      KillBookkeeping.joinedObservation s 0 t=KillBookkeeping.joinedLiveObservation
        (PlayerDamage.apply v d none false false sim.rng) 0 body sim.deathWorld ∧
      load32 t.core.memory (KillBookkeeping.player 0+244)=0x15a28+BitVec.ofNat 32 (Weapon.down w.val)*28 ∧
      load32 t.core.memory (KillBookkeeping.player 0+248)=1 ∧
      load32 t.core.memory (KillBookkeeping.player 0+256)=(Weapon.lowerHeight y true).raw.toBitVec ∧
      PlayerHeight.Frame s.memory t.core.memory (previousWrites s ++ suffixWrites s) := by
  obtain ⟨g,gsaved,grun,gpc,obj,chosen,_,off,obs,weapon,tics,height,ebx,sp,ret,frame⟩ :=
    E1M1Death.floor_death_tracked s f pc site v d sim map skill body info w y h dead stackSafe
  have choice : ∃ extreme, stateId extreme=Death.deathState
      (PlayerDamage.apply v d none false false sim.rng).state.health E1M1Death.playerInfo := by
    rcases E1M1Death.player_states (PlayerDamage.apply v d none false false sim.rng).state.health with normal|extreme
    · exact ⟨false,normal.symm⟩
    · exact ⟨true,extreme.symm⟩
  obtain ⟨extreme,choice⟩ := choice
  have index : g.core.regs 2=(entry extreme).index := by
    rw [← choice] at chosen
    cases extreme <;> simpa [entry,stateId] using chosen
  have slots : DeathSetter.writes g.core=suffixWrites s := by
    simp [DeathSetter.writes,suffixWrites,obj,sp,BitVec.sub_sub]
  have table (a : Word) (ha : a ∈ DeathSetter.tableWords (entry extreme)) :
      load32 g.core.memory a=load32 s.memory a := frame a (ins.tablePreviousSafe extreme a ha)
  have input : DeathSetter.SetterInputs (entry extreme) g.core := by
    refine ⟨index,?_,?_,?_,?_⟩
    · constructor
      · rw [table _ (by simp [DeathSetter.tableWords])]; exact (ins.tables extreme).sprite
      · rw [table _ (by simp [DeathSetter.tableWords])]; exact (ins.tables extreme).frame
      · rw [table _ (by simp [DeathSetter.tableWords])]; exact (ins.tables extreme).tics
      · rw [table _ (by simp [DeathSetter.tableWords])]; exact (ins.tables extreme).action
      · rw [table _ (by simp [DeathSetter.tableWords])]; exact (ins.tables extreme).next
    · simpa [sp] using ret
    · intro a ha b hb
      apply ins.tableSetterSafe extreme a ha b
      simpa [suffixWrites,obj,sp,BitVec.sub_sub] using hb
    · intro a ha b hb
      apply ins.stackSetterSafe a
      · simpa [sp,BitVec.sub_sub] using ha
      · simpa [obj] using hb
  let t := DeathSetter.setterEnd (entry extreme) g.core
  have trun := DeathSetter.original_execution (entry extreme) g.core g.flags input
  rw [← gpc] at trun
  obtain ⟨n,hn,path,_⟩ := X86Routine.run_path grun
  have path := path.transfer program [0x2a3f1] contains_previous (by
    intro pc hp; simp only [List.mem_singleton]; intro eq; subst pc; exact hp (by decide))
  obtain ⟨k,hk,tail,_⟩ := X86Routine.run_path trun
  have tail := tail.transfer program [0x2a3f1] contains_setter (by
    intro pc hp; simp only [List.mem_singleton]; intro eq; subst pc; exact hp (by decide))
  have rest : X86Routine.run program [0x2a3f1] 24 g=some t :=
    tail.finish (fuel := 0) (by simp [X86Routine.run,DeathSetter.setterEnd,t]) 24 (by omega)
  have preserve (a : Word) (ha : a ∈ retained s) : load32 t.core.memory a=load32 g.core.memory a := by
    apply DeathSetter.memory_frame
    intro b hb; rw [slots] at hb; exact ins.retainedSetterSafe a ha b hb
  have obsKeep : KillBookkeeping.joinedObservation s 0 t=KillBookkeeping.joinedObservation s 0 g := by
    simp only [KillBookkeeping.joinedObservation,KillEntry.damageFields,KillBookkeeping.observation]
    repeat rw [preserve _ (by simp [retained,KillDeathBranches.retained,KillWeaponDrop.retained,
      KillBookkeeping.retained,KillEntry.retained,ActorHealth.fields])]
  have tracked : DeathStack.Saved s pc t.core.memory (stackWrites s) (returnWrites s) := by
    have fr := DeathSetter.memory_frame (entry extreme) g.core
    rw [slots] at fr
    exact gsaved.then_frame _ _ _ _ _ _ _ fr
  refine ⟨extreme,t,tracked,choice,path.finish rest 263 (by omega),rfl,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [t,DeathSetter.setterEnd,write]
  · simpa [t,DeathSetter.setterEnd,write] using ebx
  · simp [t,DeathSetter.setterEnd,write,sp,BitVec.sub_eq_add_neg,BitVec.add_assoc]
  · change DeathSetter.observeFields (DeathSetter.entryMemory (entry extreme) (DeathSetter.savedMemory g.core) (g.core.regs 0)) (s.regs 0)=_
    rw [obj,DeathSetter.entry_fields]
  · rw [preserve _ (by simp [retained]),off]
  · exact obsKeep.trans obs
  · rw [preserve _ (by simp [retained,KillDeathBranches.retained]),weapon]
  · rw [preserve _ (by simp [retained,KillDeathBranches.retained]),tics]
  · rw [preserve _ (by simp [retained,KillDeathBranches.retained]),height]
  · intro a safe
    rw [DeathSetter.memory_frame (entry extreme) g.core a]
    · exact frame a (fun b hb => safe b (List.mem_append_left _ hb))
    · intro b hb; rw [slots] at hb; exact safe b (List.mem_append_right _ hb)

theorem joined_execution (s : X86Memory.State) (f : Option Flags) (pc : Nat)
    (site : pc ∈ PlayerDamageEntry.sites) (v : PlayerDamage.State) (d : Int32)
    (sim : Simulation) (map : sim.map.name="E1M1") (skill : load32 s.memory (0x2b3e0#32)=2)
    (body : Death.Body) (info : body.info=E1M1Death.playerInfo) (w : Fin 3) (y : Fixed)
    (h : KillDeathBranches.Inputs s v d false 0 body sim.deathWorld w y)
    (dead : (PlayerDamage.apply v d none false false sim.rng).killed=true)
    (stackSafe : Apart (0x12c5c#32) (s.regs 4-(56#32))) (ins : Inputs s) :
    ∃ (extreme : Bool) (t : X86Control.State),
      stateId extreme=Death.deathState (PlayerDamage.apply v d none false false sim.rng).state.health E1M1Death.playerInfo ∧
      X86Routine.run program [0x2a3f1] 263 ⟨s,f,pc⟩=some t ∧
      t.pc=0x2a3f1 ∧ t.core.regs 0=1 ∧ t.core.regs 3=s.regs 0 ∧ t.core.regs 4=s.regs 4-52 ∧
      DeathSetter.observeFields t.core.memory (s.regs 0)=
        ((entry extreme).pointer,(entry extreme).tics,(entry extreme).sprite,(entry extreme).frame) ∧
      load32 t.core.memory (0x12c5c#32)=0 ∧
      KillBookkeeping.joinedObservation s 0 t=KillBookkeeping.joinedLiveObservation
        (PlayerDamage.apply v d none false false sim.rng) 0 body sim.deathWorld ∧
      load32 t.core.memory (KillBookkeeping.player 0+244)=0x15a28+BitVec.ofNat 32 (Weapon.down w.val)*28 ∧
      load32 t.core.memory (KillBookkeeping.player 0+248)=1 ∧
      load32 t.core.memory (KillBookkeeping.player 0+256)=(Weapon.lowerHeight y true).raw.toBitVec ∧
      PlayerHeight.Frame s.memory t.core.memory (previousWrites s ++ suffixWrites s) := by
  obtain ⟨extreme,t,_,rest⟩ :=
    joined_execution_tracked s f pc site v d sim map skill body info w y h dead stackSafe ins
  exact ⟨extreme,t,rest⟩

end Doom.Proofs.E1M1DeathSetter
