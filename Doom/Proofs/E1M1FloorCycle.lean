import Doom.Proofs.E1M1SectorReturn
import Doom.Proofs.OriginalFloorJoined
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1FloorCycle
open Verification X86 X86Memory X86Control BlockSummary

def program (pc : Nat) : Option (X86Routine.Op × Nat) :=
  match E1M1SectorReturn.program pc with
  | some op => some op
  | none => FloorCaller.program pc

theorem contains_return (pc : Nat) (h : E1M1SectorReturn.program pc≠none) :
    program pc=E1M1SectorReturn.program pc := by
  unfold program
  cases eq : E1M1SectorReturn.program pc with
  | none => exact False.elim (h eq)
  | some op => rfl

theorem contains_caller (pc : Nat) (h : FloorCaller.program pc≠none) :
    program pc=FloorCaller.program pc := by
  have range : (0x24160 ≤ pc ∧ pc < 0x2417c) ∨ (0x2fb20 ≤ pc ∧ pc < 0x2fbdc) ∨
      (0x333d0 ≤ pc ∧ pc < 0x333e5) := by
    by_cases yes : (0x24160 ≤ pc ∧ pc < 0x2417c) ∨ (0x2fb20 ≤ pc ∧ pc < 0x2fbdc) ∨
      (0x333d0 ≤ pc ∧ pc < 0x333e5)
    · exact yes
    have a : ¬(0x333d0 ≤ pc ∧ pc < 0x333e5) := by omega
    have b : ¬(0x2fb20 ≤ pc ∧ pc < 0x2fb20+SectorEntry.entryBytes.length) := by
      have : SectorEntry.entryBytes.length=55 := by decide
      omega
    have c : ¬(0x2fb57 ≤ pc ∧ pc < 0x2fb57+FloorDamage.code.length) := by
      have : FloorDamage.code.length=133 := by decide
      omega
    have d : ¬(0x24160 ≤ pc ∧ pc < 0x24160+Doom19.playRandomBytes.length) := by
      have : Doom19.playRandomBytes.length=28 := by decide
      omega
    simp [FloorCaller.program,FloorCaller.bytesProgram,FloorEntry.bytesProgram,
      FloorDamage.bytesProgram,a,b,c,d] at h
  rcases range with a|b|c
  · have checked : ∀ i : Fin 28, program (0x24160+i.val)=FloorCaller.program (0x24160+i.val) := by decide
    have eq : 0x24160+(pc-0x24160)=pc := by omega
    simpa only [eq] using checked ⟨pc-0x24160,by omega⟩
  · have checked : ∀ i : Fin 188, program (0x2fb20+i.val)=FloorCaller.program (0x2fb20+i.val) := by decide
    have eq : 0x2fb20+(pc-0x2fb20)=pc := by omega
    simpa only [eq] using checked ⟨pc-0x2fb20,by omega⟩
  · have checked : ∀ i : Fin 21, program (0x333d0+i.val)=FloorCaller.program (0x333d0+i.val) := by decide
    have eq : 0x333d0+(pc-0x333d0)=pc := by omega
    simpa only [eq] using checked ⟨pc-0x333d0,by omega⟩

/-- Exact proved boundary summary; it is a function of the initial caller state,
not an arbitrary intermediate-state witness. -/
abbrev boundary := FloorCaller.result

/-- RNG supplied to damage after the optional floor/suit-leak draw. -/
def afterFloor (kind : FloorDamage.Kind) (z floor : Fixed) (time : Nat)
    (suit : Bool) (sim : Simulation) : Simulation :=
  {sim with rng := (LevelSpecials.floorDamage kind.special z floor suit time sim.rng).2}

/-- Caller lookup, real CALL/prologue, floor decision, lethal damage and all
three returns in one execution. Damage preconditions are pulled back through
`boundary`, an already-proved exact summary of the initial state. They remain
explicit obligations; this theorem does not prove the global game invariant. -/
theorem joined_execution (kind : FloorDamage.Kind) (s : X86Memory.State) (f : Option Flags)
    (z floor : Fixed) (time : Nat) (suit : Bool) (sim : Simulation)
    (map : sim.map.name="E1M1") (floorInputs : FloorCaller.Inputs kind s z floor time suit sim.rng)
    (nonzero : FloorDamage.requested (boundary kind s sim.rng) ≠ 0) (v : PlayerDamage.State) (d : Int32)
    (skill : load32 (boundary kind s sim.rng).core.memory (0x2b3e0#32)=2)
    (body : Death.Body) (info : body.info=E1M1Death.playerInfo) (w : Fin 3) (y : Fixed)
    (h : KillDeathBranches.Inputs (boundary kind s sim.rng).core v d false 0 body (afterFloor kind z floor time suit sim).deathWorld w y)
    (dead : (PlayerDamage.apply v d none false false (afterFloor kind z floor time suit sim).rng).killed=true)
    (stackSafe : Apart (0x12c5c#32) ((boundary kind s sim.rng).core.regs 4-(56#32)))
    (timing : E1M1DeathTiming.Inputs (boundary kind s sim.rng).core (afterFloor kind z floor time suit sim).rng) (ins : E1M1FloorReturn.Inputs (boundary kind s sim.rng).core)
    (safe : ∀ a, a ∈ SectorCaller.slots s → ∀ b, b ∈ E1M1FloorReturn.allWrites (boundary kind s sim.rng).core → Apart a b) :
    ∃ (extreme : Bool) (t : X86Control.State),
      E1M1DeathSetter.stateId extreme=Death.deathState
        (PlayerDamage.apply v d none false false (afterFloor kind z floor time suit sim).rng).state.health E1M1Death.playerInfo ∧
      X86CodeMemory.run FloorCaller.cm program [0x333e5] 342 ⟨s,f,0x333d0⟩=some t ∧
      t.pc=0x333e5 ∧ t.core.regs 4=s.regs 4 ∧
      t.core.regs 6=s.regs 6 ∧ t.core.regs 2=s.regs 2 ∧
      t.core.regs 1=s.regs 1 ∧ t.core.regs 3=s.regs 3 ∧
      t.core.regs 5=(boundary kind s sim.rng).core.regs 5 ∧ t.core.regs 7=(boundary kind s sim.rng).core.regs 7 ∧
      DeathSetter.observeFields t.core.memory ((boundary kind s sim.rng).core.regs 0)=
        ((E1M1DeathSetter.entry extreme).pointer,DeathTiming.playerTicks extreme (afterFloor kind z floor time suit sim).rng.play,
         (E1M1DeathSetter.entry extreme).sprite,(E1M1DeathSetter.entry extreme).frame) ∧
      load32 t.core.memory (0x12720#32)=FloorDamage.nextIndex (afterFloor kind z floor time suit sim).rng.play ∧
      load32 t.core.memory (0x1271c#32)=BitVec.ofNat 32 (afterFloor kind z floor time suit sim).rng.misc.toNat ∧
      load32 t.core.memory (0x12c5c#32)=0 ∧
      KillBookkeeping.joinedObservation (boundary kind s sim.rng).core 0 t=KillBookkeeping.joinedLiveObservation
        (PlayerDamage.apply v d none false false (afterFloor kind z floor time suit sim).rng) 0 body (afterFloor kind z floor time suit sim).deathWorld ∧
      load32 t.core.memory (KillBookkeeping.player 0+244)=0x15a28+BitVec.ofNat 32 (Weapon.down w.val)*28 ∧
      load32 t.core.memory (KillBookkeeping.player 0+248)=1 ∧
      load32 t.core.memory (KillBookkeeping.player 0+256)=(Weapon.lowerHeight y true).raw.toBitVec ∧
      PlayerHeight.Frame s.memory t.core.memory
        (FloorJoined.effectWrites s ++ E1M1FloorReturn.allWrites (boundary kind s sim.rng).core) := by
  let q := boundary kind s sim.rng
  let next := afterFloor kind z floor time suit sim
  have first := FloorCaller.execution kind s f z floor time suit sim.rng floorInputs
  obtain ⟨n,hn,path,done⟩ := X86CodeMemory.run_path first
  have site : q.pc ∈ PlayerDamageEntry.sites := by
    have no : q.pc≠0x2fc39 := by
      intro eq
      apply nonzero
      change FloorDamage.requested q=0
      simp [FloorDamage.requested,eq]
    change q.pc ∈ FloorDamage.exits at done
    simp only [FloorDamage.exits,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at done
    simp only [PlayerDamageEntry.sites,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false]
    exact done.resolve_left no
  have indexSafe (a : Word) (ha : a ∈ SectorCaller.slots s) : Apart a (0x12720#32) :=
    FloorCaller.apart_symm (floorInputs.stackSafe _ (by simp [FloorCaller.reads]) a
      (List.mem_append_left _ ha))
  have saved := FloorReturn.caller_saved kind s z floor time suit sim.rng floorInputs indexSafe
  obtain ⟨extreme,t,choice,run,post⟩ := E1M1SectorReturn.joined_execution s q.core q.flags q.pc site v d
    next map skill body info w y h dead stackSafe timing ins saved safe
  have run := X86CodeMemory.run_lift_success run FloorCaller.cm
  obtain ⟨j,hj,tail,finish⟩ := X86CodeMemory.run_path run
  have tail := tail.transfer program [0x333e5] contains_return (by
    intro addr hp; simp only [List.mem_singleton]; intro eq; subst addr; exact hp (by decide))
  have run : X86CodeMemory.run FloorCaller.cm program [0x333e5] 300 q=some t :=
    tail.finish (fuel := 0) (by simp [X86CodeMemory.run,finish]) 300 (by omega)
  have path := path.transfer program [0x333e5] contains_caller (by
    intro addr hp; simp only [List.mem_singleton]; intro eq; subst addr; exact hp (by decide))
  rcases post with ⟨pc,sp,si,dx,cx,bx,bp,di,fields,index,misc,off,obs,weapon,tics,height,frame⟩
  have before := FloorJoined.handler_frame kind s z floor time suit sim.rng floorInputs
  refine ⟨extreme,t,choice,path.finish (fuel := 300) run 342 (by omega),pc,sp,si,dx,cx,bx,bp,di,
    fields,index,misc,off,obs,weapon,tics,height,?_⟩
  intro a ha
  rw [frame a (fun b hb => ha b (List.mem_append_right _ hb))]
  exact before a (fun b hb => ha b (List.mem_append_left _ hb))

end Doom.Proofs.E1M1FloorCycle
