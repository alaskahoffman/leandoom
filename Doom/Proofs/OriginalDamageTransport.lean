import Doom.Proofs.E1M1FloorCycle
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
namespace Doom.Proofs.DamageTransport
open Verification X86 X86Memory X86Control BlockSummary

/-- Memory read by the lethal-floor contracts, including pointer-bearing words.
Stack scratch contents are not inputs to these contracts. -/
def reads (s : X86Memory.State) (w : Fin 3) (rng : DoomRandom) : List Word :=
  PlayerDamageEntry.reads s ++
  [PlayerDamageEntry.inputPlayer s+32,PlayerDamageEntry.inputPlayer s+220,
   0x2923c,s.regs 0+88,s.regs 0+68,0x2b400,0x2af44,KillBookkeeping.fragAddress 0] ++
  KillDeathBranches.reads s ++
  [WeaponDrop.location (KillWeaponDrop.dropView s 0) w 1,
   WeaponDrop.location (KillWeaponDrop.dropView s 0) w 2,
   WeaponDrop.location (KillWeaponDrop.dropView s 0) w 5,
   WeaponDrop.location (KillWeaponDrop.dropView s 0) w 6,
   WeaponDrop.location (KillWeaponDrop.dropView s 0) w 7,
   WeaponDrop.location (KillWeaponDrop.dropView s 0) w 8,
   WeaponDrop.location (KillWeaponDrop.dropView s 0) w 9] ++
  DeathSetter.tableWords (E1M1DeathSetter.entry false) ++
  DeathSetter.tableWords (E1M1DeathSetter.entry true) ++
  [0x12720,0x1271c,0x1261c+FloorDamage.nextIndex rng.play]

/-- Exactly the registers used by the contracts plus their memory footprint. -/
structure Agrees (s t : X86Memory.State) (w : Fin 3) (rng : DoomRandom) : Prop where
  r0 : t.regs 0=s.regs 0
  r1 : t.regs 1=s.regs 1
  r2 : t.regs 2=s.regs 2
  r3 : t.regs 3=s.regs 3
  r4 : t.regs 4=s.regs 4
  words : ∀ a, a ∈ reads s w rng → load32 t.memory a=load32 s.memory a

theorem Agrees.byte {s t w rng} (eq : Agrees s t w rng) (a : Word) (ha : a ∈ reads s w rng) :
    t.memory a=s.memory a := by
  have h := congrArg (fun v : Word => v.extractLsb' 0 8) (eq.words a ha)
  simpa only [PlayerHeight.load_byte] using h

theorem Agrees.half {s t w rng} (eq : Agrees s t w rng) (a : Word) (ha : a ∈ reads s w rng) :
    load16 t.memory a=load16 s.memory a := by
  rw [←SectorDispatch.load_half,←SectorDispatch.load_half,eq.words a ha]

/-- Shared proof pattern for transporting individual contract fields. All
address and memory rewrites still produce ordinary kernel-checked terms. -/
macro "damage_transport " evidence:term " across " rel:term " with "
    pl:term "," sub:term "," sec:term "," inf:term : tactic =>
  `(tactic| simpa (disch := simp [reads, PlayerDamageEntry.reads, KillDeathBranches.reads, WeaponDrop.location, KillWeaponDrop.dropView, write]) [
      PlayerDamageEntry.reads, PlayerDamageEntry.slots, PlayerDamageEntry.writes, PlayerHealth.writes, PlayerHealth.afterWrites,
      ActorHealth.fields, ActorHealth.callSlots, ActorHealth.joinedWrites, ActorHealth.afterWrites, KillEntry.initialReads,
      KillEntry.callSlots, KillEntry.suffixWrites, KillEntry.retained, KillEntry.returnWrites, KillEntry.stackWrites,
      KillBookkeeping.entryView, KillBookkeeping.playerPointer, KillBookkeeping.layout, KillBookkeeping.net, KillBookkeeping.reads,
      KillBookkeeping.priorWrites, KillBookkeeping.retained, KillBookkeeping.writes, KillBookkeeping.markWrites, KillBookkeeping.returnWrites,
      KillBookkeeping.stackWrites, KillWeaponDrop.dropView, KillWeaponDrop.priorWrites, KillWeaponDrop.retained, KillWeaponDrop.returnWrites,
      KillWeaponDrop.stackWrites, KillDeathBranches.reads, KillDeathBranches.priorWrites, KillDeathBranches.retained, KillDeathBranches.returnWrites,
      KillDeathBranches.stackWrites, WeaponDrop.location, WeaponDrop.writes, WeaponDrop.psp, E1M1DeathSetter.previousWrites,
      E1M1DeathSetter.suffixWrites, E1M1DeathSetter.retained, E1M1DeathSetter.returnWrites, E1M1DeathSetter.stackWrites, E1M1DeathTiming.previousWrites,
      E1M1DeathTiming.timingWrites, E1M1DeathTiming.retained, E1M1DeathTiming.returnWrites, E1M1DeathTiming.stackWrites, E1M1FloorReturn.allWrites,
      DeathSetter.fields, PainSetter.fields, write, List.mem_append, List.mem_cons,
      List.mem_singleton, List.not_mem_nil, or_false, ($rel).r0, ($rel).r1,
      ($rel).r2, ($rel).r3, ($rel).r4, ($pl), ($sub),
      ($sec), ($inf), ($rel).words, ($rel).byte, ($rel).half] using $evidence)

theorem entry (s t : X86Memory.State) (v : PlayerDamage.State) (d : Int32) (body : Death.Body) (world : Death.World) (w : Fin 3) (y : Fixed) (rng : DoomRandom) (eq : Agrees s t w rng)
    (h : PlayerDamageEntry.Inputs s v d false) : PlayerDamageEntry.Inputs t v d false := by
  have r0 := eq.r0; have r1 := eq.r1; have r2 := eq.r2; have r3 := eq.r3; have r4 := eq.r4
  have word := eq.words
  have byte := eq.byte
  have half := eq.half
  have player : PlayerDamageEntry.inputPlayer t=PlayerDamageEntry.inputPlayer s := by
    unfold PlayerDamageEntry.inputPlayer; rw [r0]; exact word _ (by simp [reads,PlayerDamageEntry.reads])
  have sub : PlayerDamageEntry.inputSubsector t=PlayerDamageEntry.inputSubsector s := by
    unfold PlayerDamageEntry.inputSubsector; rw [r0]; exact word _ (by simp [reads,PlayerDamageEntry.reads])
  have sector : PlayerDamageEntry.inputSector t=PlayerDamageEntry.inputSector s := by
    unfold PlayerDamageEntry.inputSector; rw [sub]; exact word _ (by simp [reads,PlayerDamageEntry.reads])
  have info : KillDeathBranches.infoPointer t=KillDeathBranches.infoPointer s := by
    unfold KillDeathBranches.infoPointer; rw [r0]; exact word _ (by simp [reads,KillDeathBranches.reads])
  constructor
  · damage_transport h.damage across eq with player, sub, sector, info
  · damage_transport h.inflictor across eq with player, sub, sector, info
  · damage_transport h.source across eq with player, sub, sector, info
  · damage_transport h.shootable across eq with player, sub, sector, info
  · damage_transport h.health across eq with player, sub, sector, info
  · damage_transport h.noSkull across eq with player, sub, sector, info
  · damage_transport h.liveSkull across eq with player, sub, sector, info
  · damage_transport h.isPlayer across eq with player, sub, sector, info
  · damage_transport h.skill across eq with player, sub, sector, info
  · damage_transport h.ordinary across eq with player, sub, sector, info
  · damage_transport h.liveOrdinary across eq with player, sub, sector, info
  · damage_transport h.god across eq with player, sub, sector, info
  · damage_transport h.invulnerable across eq with player, sub, sector, info
  · damage_transport h.armor across eq with player, sub, sector, info
  · damage_transport h.armorType across eq with player, sub, sector, info
  · damage_transport h.stackSafe across eq with player, sub, sector, info

theorem health (s t : X86Memory.State) (v : PlayerDamage.State) (d : Int32) (body : Death.Body) (world : Death.World) (w : Fin 3) (y : Fixed) (rng : DoomRandom) (eq : Agrees s t w rng)
    (h : PlayerHealth.Inputs s v d false) : PlayerHealth.Inputs t v d false := by
  have r0 := eq.r0; have r1 := eq.r1; have r2 := eq.r2; have r3 := eq.r3; have r4 := eq.r4
  have word := eq.words
  have byte := eq.byte
  have half := eq.half
  have player : PlayerDamageEntry.inputPlayer t=PlayerDamageEntry.inputPlayer s := by
    unfold PlayerDamageEntry.inputPlayer; rw [r0]; exact word _ (by simp [reads,PlayerDamageEntry.reads])
  have sub : PlayerDamageEntry.inputSubsector t=PlayerDamageEntry.inputSubsector s := by
    unfold PlayerDamageEntry.inputSubsector; rw [r0]; exact word _ (by simp [reads,PlayerDamageEntry.reads])
  have sector : PlayerDamageEntry.inputSector t=PlayerDamageEntry.inputSector s := by
    unfold PlayerDamageEntry.inputSector; rw [sub]; exact word _ (by simp [reads,PlayerDamageEntry.reads])
  have info : KillDeathBranches.infoPointer t=KillDeathBranches.infoPointer s := by
    unfold KillDeathBranches.infoPointer; rw [r0]; exact word _ (by simp [reads,KillDeathBranches.reads])
  constructor
  · exact entry s t v d body world w y rng eq h.toInputs
  · damage_transport h.playerHealth across eq with player, sub, sector, info
  · damage_transport h.damageCount across eq with player, sub, sector, info
  · damage_transport h.extraStack across eq with player, sub, sector, info

theorem actor (s t : X86Memory.State) (v : PlayerDamage.State) (d : Int32) (body : Death.Body) (world : Death.World) (w : Fin 3) (y : Fixed) (rng : DoomRandom) (eq : Agrees s t w rng)
    (h : ActorHealth.JoinedInputs s v d false) : ActorHealth.JoinedInputs t v d false := by
  have r0 := eq.r0; have r1 := eq.r1; have r2 := eq.r2; have r3 := eq.r3; have r4 := eq.r4
  have word := eq.words
  have byte := eq.byte
  have half := eq.half
  have player : PlayerDamageEntry.inputPlayer t=PlayerDamageEntry.inputPlayer s := by
    unfold PlayerDamageEntry.inputPlayer; rw [r0]; exact word _ (by simp [reads,PlayerDamageEntry.reads])
  have sub : PlayerDamageEntry.inputSubsector t=PlayerDamageEntry.inputSubsector s := by
    unfold PlayerDamageEntry.inputSubsector; rw [r0]; exact word _ (by simp [reads,PlayerDamageEntry.reads])
  have sector : PlayerDamageEntry.inputSector t=PlayerDamageEntry.inputSector s := by
    unfold PlayerDamageEntry.inputSector; rw [sub]; exact word _ (by simp [reads,PlayerDamageEntry.reads])
  have info : KillDeathBranches.infoPointer t=KillDeathBranches.infoPointer s := by
    unfold KillDeathBranches.infoPointer; rw [r0]; exact word _ (by simp [reads,KillDeathBranches.reads])
  constructor
  · exact health s t v d body world w y rng eq h.toHealth
  · damage_transport h.tactileDisabled across eq with player, sub, sector, info
  · damage_transport h.earlierSafe across eq with player, sub, sector, info
  · damage_transport h.tactileSafe across eq with player, sub, sector, info
  · damage_transport h.actorSafe across eq with player, sub, sector, info

theorem kill (s t : X86Memory.State) (v : PlayerDamage.State) (d : Int32) (body : Death.Body) (world : Death.World) (w : Fin 3) (y : Fixed) (rng : DoomRandom) (eq : Agrees s t w rng)
    (h : KillEntry.JoinedInputs s v d false body) : KillEntry.JoinedInputs t v d false body := by
  have r0 := eq.r0; have r1 := eq.r1; have r2 := eq.r2; have r3 := eq.r3; have r4 := eq.r4
  have word := eq.words
  have byte := eq.byte
  have half := eq.half
  have player : PlayerDamageEntry.inputPlayer t=PlayerDamageEntry.inputPlayer s := by
    unfold PlayerDamageEntry.inputPlayer; rw [r0]; exact word _ (by simp [reads,PlayerDamageEntry.reads])
  have sub : PlayerDamageEntry.inputSubsector t=PlayerDamageEntry.inputSubsector s := by
    unfold PlayerDamageEntry.inputSubsector; rw [r0]; exact word _ (by simp [reads,PlayerDamageEntry.reads])
  have sector : PlayerDamageEntry.inputSector t=PlayerDamageEntry.inputSector s := by
    unfold PlayerDamageEntry.inputSector; rw [sub]; exact word _ (by simp [reads,PlayerDamageEntry.reads])
  have info : KillDeathBranches.infoPointer t=KillDeathBranches.infoPointer s := by
    unfold KillDeathBranches.infoPointer; rw [r0]; exact word _ (by simp [reads,KillDeathBranches.reads])
  constructor
  · exact actor s t v d body world w y rng eq h.toActor
  · damage_transport h.player across eq with player, sub, sector, info
  · damage_transport h.kind across eq with player, sub, sector, info
  · damage_transport h.flags across eq with player, sub, sector, info
  · damage_transport h.tall across eq with player, sub, sector, info
  · damage_transport h.readsSafe across eq with player, sub, sector, info
  · damage_transport h.killStackSafe across eq with player, sub, sector, info
  · damage_transport h.heightSafe across eq with player, sub, sector, info
  · damage_transport h.byteSafe across eq with player, sub, sector, info
  · damage_transport h.sourceSafe across eq with player, sub, sector, info
  · damage_transport h.retainedSafe across eq with player, sub, sector, info

theorem bookLayout (s t : X86Memory.State) (v : PlayerDamage.State) (d : Int32) (body : Death.Body) (world : Death.World) (w : Fin 3) (y : Fixed) (rng : DoomRandom) (eq : Agrees s t w rng)
    (h : KillBookkeeping.Layout (KillBookkeeping.entryView s) 0) : KillBookkeeping.Layout (KillBookkeeping.entryView t) 0 := by
  have r0 := eq.r0; have r1 := eq.r1; have r2 := eq.r2; have r3 := eq.r3; have r4 := eq.r4
  have word := eq.words
  have byte := eq.byte
  have half := eq.half
  have player : PlayerDamageEntry.inputPlayer t=PlayerDamageEntry.inputPlayer s := by
    unfold PlayerDamageEntry.inputPlayer; rw [r0]; exact word _ (by simp [reads,PlayerDamageEntry.reads])
  have sub : PlayerDamageEntry.inputSubsector t=PlayerDamageEntry.inputSubsector s := by
    unfold PlayerDamageEntry.inputSubsector; rw [r0]; exact word _ (by simp [reads,PlayerDamageEntry.reads])
  have sector : PlayerDamageEntry.inputSector t=PlayerDamageEntry.inputSector s := by
    unfold PlayerDamageEntry.inputSector; rw [sub]; exact word _ (by simp [reads,PlayerDamageEntry.reads])
  have info : KillDeathBranches.infoPointer t=KillDeathBranches.infoPointer s := by
    unfold KillDeathBranches.infoPointer; rw [r0]; exact word _ (by simp [reads,KillDeathBranches.reads])
  constructor
  · damage_transport h.ptr across eq with player, sub, sector, info
  · damage_transport h.separated across eq with player, sub, sector, info
  · damage_transport h.stackSafe across eq with player, sub, sector, info

theorem book (s t : X86Memory.State) (v : PlayerDamage.State) (d : Int32) (body : Death.Body) (world : Death.World) (w : Fin 3) (y : Fixed) (rng : DoomRandom) (eq : Agrees s t w rng)
    (h : KillBookkeeping.Inputs (KillBookkeeping.entryView s) 0 body world) : KillBookkeeping.Inputs (KillBookkeeping.entryView t) 0 body world := by
  have r0 := eq.r0; have r1 := eq.r1; have r2 := eq.r2; have r3 := eq.r3; have r4 := eq.r4
  have word := eq.words
  have byte := eq.byte
  have half := eq.half
  have player : PlayerDamageEntry.inputPlayer t=PlayerDamageEntry.inputPlayer s := by
    unfold PlayerDamageEntry.inputPlayer; rw [r0]; exact word _ (by simp [reads,PlayerDamageEntry.reads])
  have sub : PlayerDamageEntry.inputSubsector t=PlayerDamageEntry.inputSubsector s := by
    unfold PlayerDamageEntry.inputSubsector; rw [r0]; exact word _ (by simp [reads,PlayerDamageEntry.reads])
  have sector : PlayerDamageEntry.inputSector t=PlayerDamageEntry.inputSector s := by
    unfold PlayerDamageEntry.inputSector; rw [sub]; exact word _ (by simp [reads,PlayerDamageEntry.reads])
  have info : KillDeathBranches.infoPointer t=KillDeathBranches.infoPointer s := by
    unfold KillDeathBranches.infoPointer; rw [r0]; exact word _ (by simp [reads,KillDeathBranches.reads])
  constructor
  · exact bookLayout s t v d body world w y rng eq h.toLayout
  · damage_transport h.source across eq with player, sub, sector, info
  · damage_transport h.environmental across eq with player, sub, sector, info
  · damage_transport h.victim across eq with player, sub, sector, info
  · damage_transport h.flags across eq with player, sub, sector, info
  · damage_transport h.netgame across eq with player, sub, sector, info
  · damage_transport h.kills across eq with player, sub, sector, info
  · damage_transport h.frags across eq with player, sub, sector, info

theorem bookJoined (s t : X86Memory.State) (v : PlayerDamage.State) (d : Int32) (body : Death.Body) (world : Death.World) (w : Fin 3) (y : Fixed) (rng : DoomRandom) (eq : Agrees s t w rng)
    (h : KillBookkeeping.JoinedInputs s v d false 0 body world) : KillBookkeeping.JoinedInputs t v d false 0 body world := by
  have r0 := eq.r0; have r1 := eq.r1; have r2 := eq.r2; have r3 := eq.r3; have r4 := eq.r4
  have word := eq.words
  have byte := eq.byte
  have half := eq.half
  have player : PlayerDamageEntry.inputPlayer t=PlayerDamageEntry.inputPlayer s := by
    unfold PlayerDamageEntry.inputPlayer; rw [r0]; exact word _ (by simp [reads,PlayerDamageEntry.reads])
  have sub : PlayerDamageEntry.inputSubsector t=PlayerDamageEntry.inputSubsector s := by
    unfold PlayerDamageEntry.inputSubsector; rw [r0]; exact word _ (by simp [reads,PlayerDamageEntry.reads])
  have sector : PlayerDamageEntry.inputSector t=PlayerDamageEntry.inputSector s := by
    unfold PlayerDamageEntry.inputSector; rw [sub]; exact word _ (by simp [reads,PlayerDamageEntry.reads])
  have info : KillDeathBranches.infoPointer t=KillDeathBranches.infoPointer s := by
    unfold KillDeathBranches.infoPointer; rw [r0]; exact word _ (by simp [reads,KillDeathBranches.reads])
  constructor
  · exact kill s t v d body world w y rng eq h.toKill
  · exact book s t v d body world w y rng eq h.book
  · damage_transport h.bookReadsSafe across eq with player, sub, sector, info
  · damage_transport h.bookRetained across eq with player, sub, sector, info

theorem drop (s t : X86Memory.State) (v : PlayerDamage.State) (d : Int32) (body : Death.Body) (world : Death.World) (w : Fin 3) (y : Fixed) (rng : DoomRandom) (eq : Agrees s t w rng)
    (h : KillWeaponDrop.Inputs s v d false 0 body world w y) : KillWeaponDrop.Inputs t v d false 0 body world w y := by
  have r0 := eq.r0; have r1 := eq.r1; have r2 := eq.r2; have r3 := eq.r3; have r4 := eq.r4
  have word := eq.words
  have byte := eq.byte
  have half := eq.half
  have player : PlayerDamageEntry.inputPlayer t=PlayerDamageEntry.inputPlayer s := by
    unfold PlayerDamageEntry.inputPlayer; rw [r0]; exact word _ (by simp [reads,PlayerDamageEntry.reads])
  have sub : PlayerDamageEntry.inputSubsector t=PlayerDamageEntry.inputSubsector s := by
    unfold PlayerDamageEntry.inputSubsector; rw [r0]; exact word _ (by simp [reads,PlayerDamageEntry.reads])
  have sector : PlayerDamageEntry.inputSector t=PlayerDamageEntry.inputSector s := by
    unfold PlayerDamageEntry.inputSector; rw [sub]; exact word _ (by simp [reads,PlayerDamageEntry.reads])
  have info : KillDeathBranches.infoPointer t=KillDeathBranches.infoPointer s := by
    unfold KillDeathBranches.infoPointer; rw [r0]; exact word _ (by simp [reads,KillDeathBranches.reads])
  have loc (n : Fin 18) : WeaponDrop.location (KillWeaponDrop.dropView t 0) w n=WeaponDrop.location (KillWeaponDrop.dropView s 0) w n := by
    simp [WeaponDrop.location,WeaponDrop.psp,KillWeaponDrop.dropView,write,r4]
  constructor
  · exact bookJoined s t v d body world w y rng eq h.prior
  · rw [loc]
    exact (word _ (by simp [reads])).trans h.ready
  · rw [loc]
    exact (word _ (by simp [reads])).trans h.height
  · rw [loc]
    exact (word _ (by simp [reads])).trans h.down
  · rw [loc]
    exact (word _ (by simp [reads])).trans h.tics
  · rw [loc]
    exact (word _ (by simp [reads])).trans h.misc
  · rw [loc]
    exact (word _ (by simp [reads])).trans h.callback
  · rw [loc]
    exact (word _ (by simp [reads])).trans h.next
  · damage_transport h.separate across eq with player, sub, sector, info
  · damage_transport h.readsSafe across eq with player, sub, sector, info
  · damage_transport h.retainedSafe across eq with player, sub, sector, info

theorem branches (s t : X86Memory.State) (v : PlayerDamage.State) (d : Int32) (body : Death.Body) (world : Death.World) (w : Fin 3) (y : Fixed) (rng : DoomRandom) (eq : Agrees s t w rng)
    (h : KillDeathBranches.Inputs s v d false 0 body world w y) : KillDeathBranches.Inputs t v d false 0 body world w y := by
  have r0 := eq.r0; have r1 := eq.r1; have r2 := eq.r2; have r3 := eq.r3; have r4 := eq.r4
  have word := eq.words
  have byte := eq.byte
  have half := eq.half
  have player : PlayerDamageEntry.inputPlayer t=PlayerDamageEntry.inputPlayer s := by
    unfold PlayerDamageEntry.inputPlayer; rw [r0]; exact word _ (by simp [reads,PlayerDamageEntry.reads])
  have sub : PlayerDamageEntry.inputSubsector t=PlayerDamageEntry.inputSubsector s := by
    unfold PlayerDamageEntry.inputSubsector; rw [r0]; exact word _ (by simp [reads,PlayerDamageEntry.reads])
  have sector : PlayerDamageEntry.inputSector t=PlayerDamageEntry.inputSector s := by
    unfold PlayerDamageEntry.inputSector; rw [sub]; exact word _ (by simp [reads,PlayerDamageEntry.reads])
  have info : KillDeathBranches.infoPointer t=KillDeathBranches.infoPointer s := by
    unfold KillDeathBranches.infoPointer; rw [r0]; exact word _ (by simp [reads,KillDeathBranches.reads])
  constructor
  · exact drop s t v d body world w y rng eq h.prior
  · damage_transport h.console across eq with player, sub, sector, info
  · damage_transport h.automap across eq with player, sub, sector, info
  · damage_transport h.spawn across eq with player, sub, sector, info
  · damage_transport h.normal across eq with player, sub, sector, info
  · damage_transport h.extreme across eq with player, sub, sector, info
  · damage_transport h.extremeBound across eq with player, sub, sector, info
  · damage_transport h.readsSafe across eq with player, sub, sector, info
  · damage_transport h.retainedSafe across eq with player, sub, sector, info

theorem setter (s t : X86Memory.State) (v : PlayerDamage.State) (d : Int32) (body : Death.Body) (world : Death.World) (w : Fin 3) (y : Fixed) (rng : DoomRandom) (eq : Agrees s t w rng)
    (h : E1M1DeathSetter.Inputs s) : E1M1DeathSetter.Inputs t := by
  have r0 := eq.r0; have r1 := eq.r1; have r2 := eq.r2; have r3 := eq.r3; have r4 := eq.r4
  have word := eq.words
  have byte := eq.byte
  have half := eq.half
  have player : PlayerDamageEntry.inputPlayer t=PlayerDamageEntry.inputPlayer s := by
    unfold PlayerDamageEntry.inputPlayer; rw [r0]; exact word _ (by simp [reads,PlayerDamageEntry.reads])
  have sub : PlayerDamageEntry.inputSubsector t=PlayerDamageEntry.inputSubsector s := by
    unfold PlayerDamageEntry.inputSubsector; rw [r0]; exact word _ (by simp [reads,PlayerDamageEntry.reads])
  have sector : PlayerDamageEntry.inputSector t=PlayerDamageEntry.inputSector s := by
    unfold PlayerDamageEntry.inputSector; rw [sub]; exact word _ (by simp [reads,PlayerDamageEntry.reads])
  have info : KillDeathBranches.infoPointer t=KillDeathBranches.infoPointer s := by
    unfold KillDeathBranches.infoPointer; rw [r0]; exact word _ (by simp [reads,KillDeathBranches.reads])
  constructor
  · intro extreme
    have keep (a : Word) (ha : a ∈ DeathSetter.tableWords (E1M1DeathSetter.entry extreme)) := word a (by cases extreme <;> simp [reads,ha])
    exact ⟨(keep _ (by simp [DeathSetter.tableWords])).trans (h.tables extreme).sprite, (keep _ (by simp [DeathSetter.tableWords])).trans (h.tables extreme).frame, (keep _ (by simp [DeathSetter.tableWords])).trans (h.tables extreme).tics, (keep _ (by simp [DeathSetter.tableWords])).trans (h.tables extreme).action, (keep _ (by simp [DeathSetter.tableWords])).trans (h.tables extreme).next⟩
  · damage_transport h.tablePreviousSafe across eq with player, sub, sector, info
  · damage_transport h.tableSetterSafe across eq with player, sub, sector, info
  · damage_transport h.stackSetterSafe across eq with player, sub, sector, info
  · damage_transport h.retainedSetterSafe across eq with player, sub, sector, info

theorem timing (s t : X86Memory.State) (v : PlayerDamage.State) (d : Int32) (body : Death.Body) (world : Death.World) (w : Fin 3) (y : Fixed) (rng : DoomRandom) (eq : Agrees s t w rng)
    (h : E1M1DeathTiming.Inputs s rng) : E1M1DeathTiming.Inputs t rng := by
  have r0 := eq.r0; have r1 := eq.r1; have r2 := eq.r2; have r3 := eq.r3; have r4 := eq.r4
  have word := eq.words
  have byte := eq.byte
  have half := eq.half
  have player : PlayerDamageEntry.inputPlayer t=PlayerDamageEntry.inputPlayer s := by
    unfold PlayerDamageEntry.inputPlayer; rw [r0]; exact word _ (by simp [reads,PlayerDamageEntry.reads])
  have sub : PlayerDamageEntry.inputSubsector t=PlayerDamageEntry.inputSubsector s := by
    unfold PlayerDamageEntry.inputSubsector; rw [r0]; exact word _ (by simp [reads,PlayerDamageEntry.reads])
  have sector : PlayerDamageEntry.inputSector t=PlayerDamageEntry.inputSector s := by
    unfold PlayerDamageEntry.inputSector; rw [sub]; exact word _ (by simp [reads,PlayerDamageEntry.reads])
  have info : KillDeathBranches.infoPointer t=KillDeathBranches.infoPointer s := by
    unfold KillDeathBranches.infoPointer; rw [r0]; exact word _ (by simp [reads,KillDeathBranches.reads])
  constructor
  · exact setter s t v d body world w y rng eq h.previous
  · damage_transport h.index across eq with player, sub, sector, info
  · damage_transport h.misc across eq with player, sub, sector, info
  · damage_transport h.table across eq with player, sub, sector, info
  · damage_transport h.readsPreviousSafe across eq with player, sub, sector, info
  · damage_transport h.indexStackSafe across eq with player, sub, sector, info
  · damage_transport h.tableTimingSafe across eq with player, sub, sector, info
  · damage_transport h.ticsTimingSafe across eq with player, sub, sector, info
  · damage_transport h.retainedTimingSafe across eq with player, sub, sector, info

theorem returns (s t : X86Memory.State) (v : PlayerDamage.State) (d : Int32) (body : Death.Body) (world : Death.World) (w : Fin 3) (y : Fixed) (rng : DoomRandom) (eq : Agrees s t w rng)
    (h : E1M1FloorReturn.Inputs s) : E1M1FloorReturn.Inputs t := by
  have r0 := eq.r0; have r1 := eq.r1; have r2 := eq.r2; have r3 := eq.r3; have r4 := eq.r4
  have word := eq.words
  have byte := eq.byte
  have half := eq.half
  have player : PlayerDamageEntry.inputPlayer t=PlayerDamageEntry.inputPlayer s := by
    unfold PlayerDamageEntry.inputPlayer; rw [r0]; exact word _ (by simp [reads,PlayerDamageEntry.reads])
  have sub : PlayerDamageEntry.inputSubsector t=PlayerDamageEntry.inputSubsector s := by
    unfold PlayerDamageEntry.inputSubsector; rw [r0]; exact word _ (by simp [reads,PlayerDamageEntry.reads])
  have sector : PlayerDamageEntry.inputSector t=PlayerDamageEntry.inputSector s := by
    unfold PlayerDamageEntry.inputSector; rw [sub]; exact word _ (by simp [reads,PlayerDamageEntry.reads])
  have info : KillDeathBranches.infoPointer t=KillDeathBranches.infoPointer s := by
    unfold KillDeathBranches.infoPointer; rw [r0]; exact word _ (by simp [reads,KillDeathBranches.reads])
  constructor
  · damage_transport h.killReturnSafe across eq with player, sub, sector, info
  · damage_transport h.outerSafe across eq with player, sub, sector, info
  · damage_transport h.kindSafe across eq with player, sub, sector, info



/-- The damage-call obligations already used by the floor-cycle theorem. -/
structure Contract (s : X86Memory.State) (v : PlayerDamage.State) (d : Int32)
    (sim : Simulation) (body : Death.Body) (w : Fin 3) (y : Fixed) : Prop where
  skill : load32 s.memory (0x2b3e0#32)=2
  damage : KillDeathBranches.Inputs s v d false 0 body sim.deathWorld w y
  dead : (PlayerDamage.apply v d none false false sim.rng).killed=true
  stackSafe : Apart (0x12c5c#32) (s.regs 4-(56#32))
  timing : E1M1DeathTiming.Inputs s sim.rng
  returns : E1M1FloorReturn.Inputs s

theorem Contract.transport (s t : X86Memory.State) (v : PlayerDamage.State) (d : Int32)
    (sim : Simulation) (body : Death.Body) (w : Fin 3) (y : Fixed)
    (h : Contract s v d sim body w y) (eq : Agrees s t w sim.rng) : Contract t v d sim body w y := by
  refine ⟨?_,branches s t v d body sim.deathWorld w y sim.rng eq h.damage,h.dead,?_,
    DamageTransport.timing s t v d body sim.deathWorld w y sim.rng eq h.timing,
    DamageTransport.returns s t v d body sim.deathWorld w y sim.rng eq h.returns⟩
  · exact (eq.words _ (by simp [reads,PlayerDamageEntry.reads])).trans h.skill
  · simpa only [eq.r4] using h.stackSafe

theorem allWrites_eq (s t : X86Memory.State) (w : Fin 3) (rng : DoomRandom)
    (eq : Agrees s t w rng) : E1M1FloorReturn.allWrites t=E1M1FloorReturn.allWrites s := by
  have r0 := eq.r0; have r1 := eq.r1; have r2 := eq.r2; have r3 := eq.r3; have r4 := eq.r4
  have word := eq.words
  have byte := eq.byte
  have half := eq.half
  have player : PlayerDamageEntry.inputPlayer t=PlayerDamageEntry.inputPlayer s := by
    unfold PlayerDamageEntry.inputPlayer; rw [r0]; exact word _ (by simp [reads,PlayerDamageEntry.reads])
  have sub : PlayerDamageEntry.inputSubsector t=PlayerDamageEntry.inputSubsector s := by
    unfold PlayerDamageEntry.inputSubsector; rw [r0]; exact word _ (by simp [reads,PlayerDamageEntry.reads])
  have sector : PlayerDamageEntry.inputSector t=PlayerDamageEntry.inputSector s := by
    unfold PlayerDamageEntry.inputSector; rw [sub]; exact word _ (by simp [reads,PlayerDamageEntry.reads])
  have info : KillDeathBranches.infoPointer t=KillDeathBranches.infoPointer s := by
    unfold KillDeathBranches.infoPointer; rw [r0]; exact word _ (by simp [reads,KillDeathBranches.reads])
  simp (disch := simp [reads, PlayerDamageEntry.reads, KillDeathBranches.reads, WeaponDrop.location, KillWeaponDrop.dropView, write]) [PlayerDamageEntry.reads, PlayerDamageEntry.slots, PlayerDamageEntry.writes, PlayerHealth.writes, PlayerHealth.afterWrites, ActorHealth.fields, ActorHealth.callSlots, ActorHealth.joinedWrites, ActorHealth.afterWrites, KillEntry.initialReads, KillEntry.callSlots, KillEntry.suffixWrites, KillEntry.retained, KillEntry.returnWrites, KillEntry.stackWrites, KillBookkeeping.entryView, KillBookkeeping.playerPointer, KillBookkeeping.layout, KillBookkeeping.net, KillBookkeeping.reads, KillBookkeeping.priorWrites, KillBookkeeping.retained, KillBookkeeping.writes, KillBookkeeping.markWrites, KillBookkeeping.returnWrites, KillBookkeeping.stackWrites, KillWeaponDrop.dropView, KillWeaponDrop.priorWrites, KillWeaponDrop.retained, KillWeaponDrop.returnWrites, KillWeaponDrop.stackWrites, KillDeathBranches.reads, KillDeathBranches.priorWrites, KillDeathBranches.retained, KillDeathBranches.returnWrites, KillDeathBranches.stackWrites, WeaponDrop.location, WeaponDrop.writes, WeaponDrop.psp, E1M1DeathSetter.previousWrites, E1M1DeathSetter.suffixWrites, E1M1DeathSetter.retained, E1M1DeathSetter.returnWrites, E1M1DeathSetter.stackWrites, E1M1DeathTiming.previousWrites, E1M1DeathTiming.timingWrites, E1M1DeathTiming.retained, E1M1DeathTiming.returnWrites, E1M1DeathTiming.stackWrites, E1M1FloorReturn.allWrites, DeathSetter.fields, PainSetter.fields, write, List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, r0, r1, r2, r3, r4, player, sub, sector, info, word, byte, half]

end Doom.Proofs.DamageTransport
